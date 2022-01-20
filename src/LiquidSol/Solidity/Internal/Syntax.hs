{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
module LiquidSol.Solidity.Internal.Syntax where

import Data.Text (Text)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Aeson (FromJSON(..), (.:), (.:?), (.!=))
import qualified Data.Aeson as Aeson
import Data.Hashable (Hashable)
import GHC.Stack (HasCallStack)

import LiquidSol.SrcLoc
import qualified LiquidSol.SourceMap as SourceMap
import LiquidSol.Syntax (Annot)
import LiquidSol.Util.Unsafe (hmUnsafeLookup)
import Data.List.NonEmpty (NonEmpty)

data SolNode = SolNode
  { node_attributes :: Aeson.Object
  , node_children :: [SolNode]
  , node_id :: !Int
  , node_name :: Text
  , node_src :: !SrcLoc
  }
  deriving (Show)

instance FromJSON SolNode where
  parseJSON = Aeson.withObject "Node" $ \v -> SolNode
      <$> v .:? "attributes" .!= mempty
      <*> v .:? "children" .!= mempty
      <*> v .: "id"
      <*> v .: "name"
      <*> v .: "src"

-- * Decoded AST (graph representation)

type NodeRef = Int

data SourceCtx = SourceCtx
  { srcCtx_nodes :: HashMap NodeRef SolNode
  , srcCtx_stmts :: HashMap NodeRef SolStmt
  , srcCtx_exprs :: HashMap NodeRef SolExpr
  , srcCtx_exprTypes :: HashMap ExprRef SolType
  , srcCtx_varDecls :: HashMap NodeRef SolVarDecl
  , srcCtx_cbody :: HashMap NodeRef SolCbody
  , srcCtx_contracts :: HashMap NodeRef SolContract
  , srcCtx_locs :: HashMap NodeRef SrcLoc
  , srcCtx_srcmap :: SourceMap.SourceMap
  , srcCtx_annots :: [(Int, Annot)]
  , srcCtx_maxNode :: Int }
--  deriving (Show)

instance Show SourceCtx where
  show _ = "SourceCtx{..}"

emptySourceCtx :: SourceCtx
emptySourceCtx = SourceCtx
  { srcCtx_nodes = mempty
  , srcCtx_stmts = mempty
  , srcCtx_exprs = mempty
  , srcCtx_exprTypes = mempty
  , srcCtx_varDecls = mempty
  , srcCtx_cbody = mempty
  , srcCtx_contracts = mempty
  , srcCtx_locs = mempty
  , srcCtx_srcmap = undefined
  , srcCtx_annots = []
  , srcCtx_maxNode = 0 }

sourceCtxGetLoc :: (HasRef a, HasCallStack, Show a) => TypedRef a -> SourceCtx -> SrcLoc
sourceCtxGetLoc r ctx = case HashMap.lookup (asNodeRef r) (srcCtx_locs ctx) of
  Just l -> l
  _ -> error $ "Failed to find source location of node " <> show (lookupRef r ctx)

sourceCtxGetType :: ExprRef -> SourceCtx -> SolType
sourceCtxGetType r ctx = srcCtx_exprTypes ctx `hmUnsafeLookup` r

sourceCtxFreshRef :: SourceCtx -> (NodeRef, SourceCtx)
sourceCtxFreshRef ctx =
  let n = srcCtx_maxNode ctx in
    (n + 1, ctx{srcCtx_maxNode = n})

newtype TypedRef a = TypedRef { asNodeRef :: NodeRef }
  deriving (Show, Eq, Ord, Hashable)
type VarDeclRef = TypedRef SolVarDecl
type StmtRef = TypedRef SolStmt
type ExprRef = TypedRef SolExpr
type CbodyRef = TypedRef SolCbody
type ContractRef = TypedRef SolContract

unsafeCastTypedRef :: NodeRef -> TypedRef a
unsafeCastTypedRef r = TypedRef r

class HasRef a where
  lookupRef :: HasCallStack => TypedRef a -> SourceCtx -> a
  updateRef :: TypedRef a -> a -> SourceCtx -> SourceCtx
  tryLookupRef :: NodeRef -> SourceCtx -> Maybe a
  _project :: SourceCtx -> HashMap NodeRef a
  _update :: SourceCtx -> HashMap NodeRef a -> SourceCtx

  lookupRef (TypedRef r) ctx = _project ctx `hmUnsafeLookup` r
  updateRef (TypedRef r) a ctx =
    let ctx' = _update ctx (HashMap.insert r a (_project ctx)) in
      ctx'{srcCtx_maxNode = max r (srcCtx_maxNode ctx')}
  tryLookupRef r ctx = HashMap.lookup r (_project ctx)

instance HasRef SolVarDecl where
  _project = srcCtx_varDecls
  _update ctx hm = ctx{srcCtx_varDecls = hm}

instance HasRef SolStmt where
  _project = srcCtx_stmts
  _update ctx hm = ctx{srcCtx_stmts = hm}

instance HasRef SolExpr where
  _project = srcCtx_exprs
  _update ctx hm = ctx{srcCtx_exprs = hm}

instance HasRef SolCbody where
  _project = srcCtx_cbody
  _update ctx hm = ctx{srcCtx_cbody = hm}

instance HasRef SolContract where
  _project = srcCtx_contracts
  _update ctx hm = ctx{srcCtx_contracts = hm}

data SolSourceUnit = SolSourceUnit [ContractRef]
  deriving (Show)

data SolContractKind
  = SolContractKind
  | SolInterfaceKind
  | SolLibraryKind
  deriving (Show, Eq)

-- based on libsolidity/ast/AST.h and ASTJsonImporter.h
-- also see ASTForward.h for a summary

data SolContract = SolContract
  { contract_name :: Text
  , contract_kind :: SolContractKind
  , contract_bases :: [ContractRef]
  , contract_body :: [CbodyRef]
  , contract_full :: Bool
  }
  deriving (Show)

data SolVis
  = VisPrivate
  | VisInternal
  | VisPublic
  | VisExternal
  deriving (Show, Eq, Ord)

data SolMut
  = MutPayable
  | MutNone
  | MutView
  | MutPure
  deriving (Show, Eq, Ord)

data SolCbody
  = CStateVar VarDeclRef
  | CFun
    { cfun_name :: Text
    , cfun_args :: [VarDeclRef]
    , cfun_rets :: [VarDeclRef]
    , cfun_body :: Maybe StmtRef
    , cfun_isCtor :: Bool
    , cfun_mods :: [(NodeRef, [ExprRef])]
    , cfun_vis :: SolVis
    , cfun_mut :: SolMut
    }
  | CStruct Text [VarDeclRef]
  | CInherit Text
  | CMod Text StmtRef
  | CEvent
  | CUsingFor ContractRef (Maybe SolType)
  | CEnum Text [Text]
  deriving (Show)

data SolVarDecl = SolVarDecl
  { varDecl_name :: Text
  , varDecl_type :: SolType
  , varDecl_value :: Maybe ExprRef
  , varDecl_loc :: SolStorageLoc
  , varDecl_vis :: SolVis
  }
  deriving (Show)

data SolStmt
  = SolStmtAsm Text
  | SolStmtBlock [StmtRef]
  | SolStmtIf ExprRef StmtRef (Maybe StmtRef)
  | SolStmtWhile ExprRef StmtRef
  | -- ^ init, guard, after iter (stmt expression), body
    SolStmtFor StmtRef ExprRef (StmtRef, ExprRef) StmtRef
  | SolStmtContinue
  | SolStmtBreak
  | SolStmtReturn [ExprRef]
  | SolStmtEmit
  | SolStmtVarDecl (NonEmpty VarDeclRef) (Maybe ExprRef)
  | SolStmtExpr ExprRef
  | SolStmtPlaceholder
  | SolStmtThrow -- ^ solidity 0.4.x only
  deriving (Show)

data SolType
  = SolTyElem Text -- ^ Elementary type
  | SolTyUser NodeRef Text -- ^ User defined type (ref to original decl, name)
  | SolTyArr SolType (Maybe Integer) -- ^ Array type
  | SolTyMapping SolType SolType -- ^ Mapping type
  | SolTyFun [SolType] [SolType] -- ^ Function type
  | SolTyTuple [SolType] -- ^ Tuple type
  | SolTyType SolType -- ^ Type information
  | SolTyLitInt -- ^ Int literal (why does solidity do this???)
  deriving (Show, Eq)

data SolLit
  = SolLitInt Integer
  | SolLitAddr Integer
  | SolLitBool Bool
  | SolLitString String
  deriving (Show)

data SolExpr
  = SolExprAssign Text ExprRef ExprRef SolType -- ^ operator, lhs, rhs, expected type
  | SolExprUnaryOp Text ExprRef
  | SolExprBinaryOp Text ExprRef ExprRef SolType
  | SolExprFunCall ExprRef [ExprRef] -- ^ function call
  | SolExprTypeConvert SolType ExprRef -- ^ type cast
  | SolExprStructCons CbodyRef [ExprRef] -- ^ struct construction
  | SolExprNew SolType
  | SolExprMember ExprRef Text (Maybe NodeRef)
  | SolExprIndex ExprRef ExprRef
  | SolExprIdent Text NodeRef
  | SolExprLit SolLit
  | SolExprElemType Text
  | SolExprTuple [ExprRef]
  | SolExprConditional ExprRef ExprRef ExprRef
  deriving (Show)

data SolStorageLoc
  = SolLocDefault
  | SolLocMemory
  | SolLocStorage
  | SolLocCalldata
  deriving (Show, Eq, Ord)
