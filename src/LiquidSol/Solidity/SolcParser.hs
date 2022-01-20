{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
module LiquidSol.Solidity.SolcParser
  ( decodeSolcOutput
  , SolcDecoded(..)) where

import Data.Maybe (catMaybes)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Aeson (FromJSON(..), (.:), (.:?))
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Types as Aeson
import Control.Monad ((<=<), forM)
import Control.Monad.State.Strict
import Control.Monad.Except
import Prelude hiding (head)

import LiquidSol.Solidity.Internal.Syntax
import LiquidSol.Util.Unsafe (head)
import qualified LiquidSol.SourceMap as SourceMap
import Data.ByteString.Lazy (ByteString)
import Text.Read (readMaybe)
import qualified LiquidSol.Solidity.TypeLexer as TypeP
import qualified LiquidSol.Solidity.TypeParser as TypeP
import qualified Data.List.NonEmpty as NE
import Data.Scientific (Scientific)
import qualified Data.Scientific as Scientific
import Data.List (isPrefixOf)
import Control.Monad.Extra (fromMaybeM)
import Numeric (readHex)

newtype Decode a = Decode { unDecode :: StateT SourceCtx (Except String) a }
  deriving (Functor, Applicative, Monad, MonadError String, MonadState SourceCtx)

data SolcDecoded = SolcDecoded
  { sold_sourceUnits :: HashMap Text SolSourceUnit }
  deriving (Show)

data SolcOutput = SolcOutput
  { solc_sources :: HashMap Text SolNode
  }
  deriving (Show)

instance FromJSON SolcOutput where
  parseJSON root = do
    -- { "sources": { "filename": {"AST": { ... }}, ... }, ... }
    srcs <- Aeson.withObject @Aeson.Object "JSON" (.: "sources") root
    -- for each source entry, go down "AST" and then parse the source units
    rawAsts <- forM srcs (Aeson.withObject "AST" (parseJSON @SolNode <=< (.: "AST")))
    pure (SolcOutput rawAsts)

decodeSolcOutput :: ByteString -> SourceMap.SourceMap -> Either String (SolcDecoded, SourceCtx)
decodeSolcOutput jsonString sourceMap = do
  nodeTree <- Aeson.eitherDecode' jsonString
  runExcept $ runStateT (unDecode (decodeOutput nodeTree)) emptySourceCtx{srcCtx_srcmap = sourceMap}

decodeOutput :: SolcOutput -> Decode SolcDecoded
decodeOutput out = SolcDecoded <$> traverse decodeSourceUnit (solc_sources out)

liftAeson :: Aeson.Parser a -> Decode a
liftAeson a = liftEither $ Aeson.parseEither (\_ -> a) ()

expectNodeType :: Text -> SolNode -> Decode ()
expectNodeType ty node
  | node_name node == ty = pure ()
  | otherwise = throwError ("expected " <> show ty <> " node, got " <> show (node_name node))

addLocs :: SolNode -> Decode ()
addLocs SolNode{node_id = i, node_src = src} =
  modify (\c -> c{srcCtx_locs = HashMap.insert i src (srcCtx_locs c)})

addNode :: HasRef a => SolNode -> Decode a -> Decode (TypedRef a)
addNode node m = do
  a <- m
  let ref = TypedRef (node_id node)
  modify (\c -> updateRef ref a c{srcCtx_nodes = HashMap.insert (node_id node) node (srcCtx_nodes c)})
  pure ref

decodeSourceUnit :: SolNode -> Decode SolSourceUnit
decodeSourceUnit node = addLocs node *> do
    expectNodeType "SourceUnit" node
    let isContract n = do
          pure $ node_name n == "ContractDefinition"
    SolSourceUnit <$> (traverse decodeContract =<< filterM isContract (node_children node))

decodeContract :: SolNode -> Decode ContractRef
decodeContract node = addLocs node *> do
  expectNodeType "ContractDefinition" node
  cname <- getAttr @Text "name" node
  bases <- getAttr @[Int] "linearizedBaseContracts" node
  isFull <- getAttr @Bool "fullyImplemented" node
  kind <- decodeContractKind =<< getAttr @Text "contractKind" node
  body <- catMaybes <$> traverse decodeCbody (node_children node)
  addNode node . pure $ SolContract
    { contract_name = cname
    , contract_kind = kind
    , contract_bases = TypedRef <$> bases
    , contract_body = body
    , contract_full = isFull }

decodeContractKind :: Text -> Decode SolContractKind
decodeContractKind = \case
  "library" -> pure SolLibraryKind
  "contract" -> pure SolContractKind
  "interface" -> pure SolInterfaceKind
  k -> fail $ "Unknown contractKind: " <> Text.unpack k

decodeCbody :: SolNode -> Decode (Maybe CbodyRef)
decodeCbody node = addLocs node *> case node_name node of
  "VariableDeclaration" -> fin (CStateVar <$> decodeVarDecl node)
  "FunctionDefinition" -> fin (decodeFunDecl node)
  "StructDefinition" -> do
    name <- getAttr "name" node
    fields <- traverse decodeVarDecl (node_children node)
    fin (pure $ CStruct name fields)
  "UsingForDirective" -> do
    let getDecl = getAttr @Int "referencedDeclaration"
    (lib, mty) <- case node_children node of
      [libN] -> (, Nothing) <$> getDecl libN
      [libN, tyN] -> (,) <$> getDecl libN <*> (Just <$> decodeType tyN)
      cs -> error $ "invalid UsingForDirective, expected 1 or 2 children, got " <> show cs
    fin (pure $ CUsingFor (TypedRef lib) mty)
  "EnumDefinition" -> do
    name <- getAttr @Text "name" node
    let values = forM (node_children node) $ \vnode -> do
          expectNodeType "EnumValue" vnode
          getAttr @Text "name" vnode
    fin (CEnum name <$> values)
  "ModifierDefinition" -> do
    name <- getAttr @Text "name" node
    let (argNodes, body) = case dropIrrelevantNodes $ node_children node of
          [a, b] -> (a, b)
          _ -> error $ "malformed ModifierDefinition: " <> show node
    _args <- decodeParamList argNodes
    body' <- decodeStmt body
    fin (pure $ CMod name body')
  -- Ignore the following for now in our prototype tool
  "EventDefinition" -> fin (pure CEvent)
  n | n `elem` ["InheritanceSpecifier", "StructuredDocumentation"] -> pure Nothing
  n -> fail $ "unexpected node in contract body: " <> show n
  where
    fin m = Just <$> addNode node m

decodeVarDecl :: SolNode -> Decode VarDeclRef
decodeVarDecl node = addLocs node *> do
  name <- liftAeson (node_attributes node .: "name")
  (ty, value) <- case node_children node of
    -- First child gives the type
    -- Second child, if it exists, provides the assigned expression
    (tnode:vnode:_) -> do
      ty <- decodeType tnode
      -- In Solidity >= 0.6, a doc node may be the second child if the variable is
      -- not assigned
      (ty,) <$> case node_name vnode of
        "StructuredDocumentation" -> pure Nothing
        _ -> Just <$> decodeExpression vnode
    (tnode:_) -> (, Nothing) <$> decodeType tnode
    [] -> do
      -- This is a var in solidity 0.4.x, corresponding to a
      -- VariableDeclarationStatement.
      tyStr <- getAttr @Text "type" node
      ty <- case parseTypeString tyStr of
        Left _ -> error $ "could not get type of var VariableDeclaration: " <> show tyStr
        Right t -> pure t
      pure (ty, Nothing)
  storageLoc <- getAttr @Text "storageLocation" node >>= \case
    "default" -> pure SolLocDefault
    "memory" -> pure SolLocMemory
    "storage" -> pure SolLocStorage
    "calldata" -> pure SolLocCalldata
    l -> fail $ "unknown storageLocation: " <> show l
  vis <- getAttr @Text "visibility" node >>= decodeVis
  addNode node $
    pure (SolVarDecl { varDecl_name = name, varDecl_type = ty, varDecl_value = value
                     , varDecl_loc = storageLoc, varDecl_vis = vis })

getAttr :: FromJSON a => Text -> SolNode -> Decode a
getAttr name node = liftAeson (node_attributes node .: name)

getAttrMaybe :: FromJSON a => Text -> SolNode -> Decode (Maybe a)
getAttrMaybe name node = liftAeson (node_attributes node .:? name)

decodeVis :: Text -> Decode SolVis
decodeVis = \case
  "private" -> pure VisPrivate
  "internal" -> pure VisInternal
  "external" -> pure VisExternal
  "public" -> pure VisPublic
  s -> fail $ "invalid visibility: " <> Text.unpack s

decodeMut :: Text -> Decode SolMut
decodeMut = \case
  "nonpayable" -> pure MutNone
  "view" -> pure MutView
  "pure" -> pure MutPure
  "payable" -> pure MutPayable
  s -> fail $ "invalid stateMutability: " <> Text.unpack s

decodeFunDecl :: SolNode -> Decode SolCbody
decodeFunDecl node = case node of
  -- Drop override specifier for Solidity >= 0.6 since it's irrelevant
  _ | (argNodes:retNodes:rest) <- dropOverride (node_children node) -> do
    expectNodeType "FunctionDefinition" node
    name <- getAttr @Text "name" node
    isCtor <- getAttr @Bool "isConstructor" node
    args <- decodeParamList argNodes
    rets <- decodeParamList retNodes
    let (modList, bodyNode) = case rest of
          [] -> ([], Nothing)
          _ -> (init rest, Just (last rest))
    mods <- forM modList $ \modNode -> do
      expectNodeType "ModifierInvocation" modNode
      case node_children modNode of
        (modName:modArgs) -> do
          expectNodeType "Identifier" modName
          refDecl <- getAttr @NodeRef "referencedDeclaration" modName
          args' <- traverse decodeExpression modArgs
          pure (refDecl, args')
        _ -> fail "malformed ModifierInvocation"
    body <- mapM decodeStmt bodyNode
    vis <- getAttr @Text "visibility" node >>= decodeVis
    mut <- getAttr @Text "stateMutability" node >>= decodeMut
    pure $ CFun { cfun_name=name, cfun_args=args, cfun_rets=rets
                , cfun_body=body, cfun_isCtor=isCtor, cfun_mods=mods
                , cfun_vis=vis, cfun_mut=mut }
  _ -> fail "malformed FunctionDefinition"
  where
    dropOverride = dropWhile (\n -> node_name n `elem` ["OverrideSpecifier", "StructuredDocumentation"])

dropIrrelevantNodes :: [SolNode] -> [SolNode]
dropIrrelevantNodes = dropWhile (\n -> node_name n `elem` ["StructuredDocumentation"])

decodeStmt :: SolNode -> Decode StmtRef
decodeStmt node = fin $ case node_name node of
  "Block" -> SolStmtBlock <$> traverse decodeStmt (node_children node)
  "VariableDeclarationStatement" -> do
    case node_children node of
      [dnode] -> mkSingleDecl dnode Nothing
      [dnode, asgn] -> mkSingleDecl dnode (Just asgn)
      [] -> fail $ "invalid VariableDeclarationStatement: no children assigned "
      ns -> do
        -- This is a tuple assignment
        -- Multiple variable declarations followed by value
        let asgns = init ns
        let val = last ns
        vref <- decodeExpression val
        asgns' <- traverse decodeVarDecl asgns
        gets (lookupRef vref) >>= \case
          SolExprFunCall{} ->
            pure $ SolStmtVarDecl (NE.fromList asgns') (Just vref)
          _ -> fail $ "arbitrary tuple assignment not supported"
    where
      mkSingleDecl dNode asgnNode = do
        decl <- decodeVarDecl dNode
        asgn <- mapM decodeExpression asgnNode
        -- vd <- gets (lookupRef decl)
        -- modify (updateRef decl vd{varDecl_value=asgn})
        pure $ SolStmtVarDecl (pure decl) asgn
  "ExpressionStatement" -> SolStmtExpr <$> decodeExpression (head (node_children node))
  "Return" -> do
    vals <- case node_children node of
      [] -> pure []
      [childN] -> do
        childRef <- decodeExpression childN
        gets (lookupRef childRef) >>= \case
          SolExprTuple es -> pure es
          _ -> pure [childRef]
      _ -> fail $ "invalid Return, expected 0 or 1 children, got " <> show (length (node_children node))
    pure $ SolStmtReturn vals
  "Break" -> pure SolStmtBreak
  "Continue" -> pure SolStmtContinue
  "IfStatement" -> do
    (guardNode, brThen, brElse) <- case node_children node of
      [g, brThen] -> pure (g, brThen, Nothing)
      [g, brThen, brElse] -> pure (g, brThen, Just brElse)
      _ -> fail "invalid IfStatement"
    guardExpr <- decodeExpression guardNode
    brThen' <- decodeStmt brThen
    brElse' <- mapM decodeStmt brElse
    pure $ SolStmtIf guardExpr brThen' brElse'
  "ForStatement" -> do
    (initNode, guardNode, loopNode, bodyNode) <- case node_children node of
      [i, g, l, b] -> pure (i, g, l, b)
      _ -> fail "invalid ForStatement"
    loopStmtRef <- decodeStmt loopNode
    loopExprRef <- gets (lookupRef loopStmtRef) >>= \case
      SolStmtExpr r -> pure r
      _ -> fail "invalid ForStatement: expected ExpressionStatement"
    SolStmtFor
      <$> decodeStmt initNode
      <*> decodeExpression guardNode
      <*> pure (loopStmtRef, loopExprRef)
      <*> decodeStmt bodyNode
  "WhileStatement" -> do
    (guardNode, bodyNode) <- case node_children node of
      [g, b] -> pure (g, b)
      _ -> fail "invalid WhileStatement"
    SolStmtWhile <$> decodeExpression guardNode <*> decodeStmt bodyNode
  "EmitStatement" -> pure SolStmtEmit
  "InlineAssembly" -> SolStmtAsm <$> getAttr @Text "operations" node
  "PlaceholderStatement" -> pure SolStmtPlaceholder
  "Throw" -> pure SolStmtThrow
  _ -> fail $ "expected statement, got " <> show (node_name node)
  where
    fin s = addLocs node *> addNode node s

decodeParamList :: SolNode -> Decode [VarDeclRef]
decodeParamList node = do
  expectNodeType "ParameterList" node
  traverse decodeVarDecl (node_children node)

decodeExpression :: SolNode -> Decode ExprRef
decodeExpression node = addLocs node *> case node_name node of
  "Identifier" -> fin $
    SolExprIdent
      <$> getAttr @Text "value" node
      <*> getAttr @NodeRef "referencedDeclaration" node
  "Literal" -> do
    kind <- liftAeson @Text $ fromMaybeM (node_attributes node .: "kind") (node_attributes node .:? "token")
    litStr <- getAttr @String "value" node
    denom <- getAttrMaybe @String "subdenomination" node
    let readDenom = \case
          "seconds" -> pure 1
          "minutes" -> pure 60
          "hours" -> pure 3600
          "days" -> pure 86400
          "weeks" -> pure 604800
          "years" -> pure 257252000
          "wei" -> pure 1
          "szabo" -> pure (10 ^ (12 :: Integer))
          "finney" -> pure (10 ^ (15 :: Integer))
          "ether" -> pure (10 ^ (18 :: Integer))
          d -> fail $ "Unknown subdenomination: " <> d
    denomMult <- maybe (pure 1) readDenom denom
    tyStr <- getAttr @String "type" node
    lit <- case kind of
      -- Check for address literals in solidity 0.4.x
      "number"
        | "0x" `isPrefixOf` litStr
        , ((x, ""):_) <- readHex (drop 2 litStr) ->
          pure $ if tyStr == "address" then SolLitAddr x else SolLitInt x
        | Just x <- (readMaybe litStr :: Maybe Scientific), Scientific.isInteger x ->
            pure (SolLitInt (denomMult * Scientific.coefficient x * (10 ^ Scientific.base10Exponent x)))
      "bool" | litStr == "true" -> pure (SolLitBool True)
      "bool" | litStr == "false" -> pure (SolLitBool False)
      "string" -> pure (SolLitString litStr)
      _ -> fail ("Unknown token: " <> show kind <> ": " <> litStr)
    fin (pure (SolExprLit lit))
  "UnaryOperation" -> fin $
    SolExprUnaryOp <$> getAttr "operator" node <*> decodeExpression (head (node_children node))
  "BinaryOperation" -> do
    commonType <- getAttr @Aeson.Object "commonType" node
    tyStr <- liftAeson @Text (commonType .: "typeString")
    let ty = case parseTypeString tyStr of
          Left _ -> error $ "could not get type of binary operation: " <> show tyStr
          Right t -> t
    case node_children node of
      [e1, e2] -> fin $
        SolExprBinaryOp
          <$> getAttr @Text "operator" node
          <*> decodeExpression e1
          <*> decodeExpression e2
          <*> pure ty
      es -> fail $ "expected two children, got " <> show (length es)
  "FunctionCall" -> do
    -- expectNodeType "Identifier" (head (node_children node))
    isStructCons <- getAttr @Bool "isStructConstructorCall" node
    isTypeConvert <- getAttr @Bool "type_conversion" node
    args <- traverse decodeExpression (node_children node)
    let mkCall = pure $ SolExprFunCall (head args) (tail args)
    let mkStructCons = do
          ref <- getAttr @NodeRef "referencedDeclaration" (head (node_children node))
          pure $ SolExprStructCons (unsafeCastTypedRef ref) (tail args)
    let mkTypeConvert = do
          ty <- gets (lookupRef (head args)) >>= \case
            SolExprElemType name -> pure $ SolTyElem name
            SolExprIdent name declRef -> pure $ SolTyUser declRef name
            SolExprMember{} -> error "decodeExpression: todo: namespaced types"
            e -> error $ "decodeExpression: type convert has unexpected first argument " <> show e
          pure $ SolExprTypeConvert ty (head (tail args))
    fin $ if | isStructCons -> mkStructCons
             | isTypeConvert -> mkTypeConvert
             | otherwise -> mkCall
  "Assignment" -> do
    op <- getAttr @Text "operator" node
    tyStr <- getAttr @Text "type" node
    let ty = case parseTypeString tyStr of
          Left _ -> error $ "could not get type of assignment: " <> show tyStr
          Right t -> t
    case node_children node of
      [e1, e2] -> fin (SolExprAssign op <$> decodeExpression e1 <*> decodeExpression e2 <*> pure ty)
      es -> fail $ "expected two children, got " <> show (length es)
  "MemberAccess" -> fin $
    SolExprMember
      <$> decodeExpression (head (node_children node))
      <*> getAttr "member_name" node
      <*> getAttr "referencedDeclaration" node
  "IndexAccess" -> case node_children node of
    [e1, e2] -> fin (SolExprIndex <$> decodeExpression e1 <*> decodeExpression e2)
    es -> fail $ "expected two children, got " <> show (length es)
  "ElementaryTypeNameExpression" -> do
    tyStr <- getAttrMaybe @Text "value" node >>= \case
      -- Solidity <= 0.5
      Just t -> pure t
      -- Solidity 0.6 or 0.7
      _ | [n] <- node_children node -> do
            expectNodeType "ElementaryTypeName" n
            getAttr "name" n
      _ -> fail "failed to parse ElementaryTypeNameExpression"
    fin (pure (SolExprElemType tyStr))
  "TupleExpression" -> fin (SolExprTuple <$> traverse decodeExpression (node_children node))
  "NewExpression" -> do
    ty <- case node_children node of
      [n] -> decodeType n
      _ -> fail $ "expected one child in NewExpression, got " <> show (length (node_children node))
    fin (pure $ SolExprNew ty)
  "Conditional" -> do
    (g, e1, e2) <- case node_children node of
      [g, e1, e2] -> pure (g, e1, e2)
      _ -> fail $ "expected three children in Conditional, got " <> show (length (node_children node))
    fin (SolExprConditional <$> decodeExpression g <*> decodeExpression e1 <*> decodeExpression e2)
  _ -> fail $ "expected expression, got " <> show (node_name node)
  where
    fin m = do
      ref <- addNode node m
      tyStr <- getAttr @Text "type" node
      let maybeTy = case parseTypeString tyStr of
            Left _
              | "int_const " `Text.isPrefixOf` tyStr && "..." `Text.isInfixOf` tyStr ->
                  -- The text probably got truncated (solc WTF) so assume it is an integer
                  Just SolTyLitInt
              | otherwise -> Nothing
            -- Left err -> error $ "Failed to get expression type: " <> err <> ": " <> show tyStr
            Right ty -> Just ty
      forM_ maybeTy $ \ty ->
        modify (\st -> st{srcCtx_exprTypes = HashMap.insert ref ty (srcCtx_exprTypes st)})
      pure ref

parseTypeString :: Text -> Either String SolType
parseTypeString s = TypeP.scanTokens (Text.unpack s) >>= TypeP.parseType

decodeType :: SolNode -> Decode SolType
decodeType node = addLocs node *> case node_name node of
  "ElementaryTypeName" -> SolTyElem <$> getAttr "type" node
  "UserDefinedTypeName" ->
    SolTyUser
      <$> getAttr @Int "referencedDeclaration" node
      <*> getAttr @Text "name" node
  "ArrayTypeName" -> do
    len <- case node_children node of
      _:l:_ -> do
        expectNodeType "Literal" l
        Just . read <$> getAttr @String "value" l
      _ -> pure Nothing
    SolTyArr
       <$> (decodeType $ head (node_children node))
       <*> pure len
  "Mapping" ->
    let cs = node_children node in
      SolTyMapping <$> (decodeType $ head cs) <*> (decodeType $ head (tail cs))
  _ -> fail $ "expected type, got " <> show (node_name node)
