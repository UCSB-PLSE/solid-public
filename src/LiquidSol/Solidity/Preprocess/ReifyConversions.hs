{-# LANGUAGE OverloadedStrings #-}
module LiquidSol.Solidity.Preprocess.ReifyConversions (reifyConversions) where
import LiquidSol.Solidity.Types (bytesTypes, uintTypes)

import Control.Monad.State.Strict
import LiquidSol.Solidity.ContextMonad
import LiquidSol.Solidity.Syntax
import qualified Data.HashMap.Strict as HashMap
-- import LiquidSol.Util.Unsafe
-- import Control.Monad.Extra (maybeM)
import qualified Data.List.NonEmpty as NE

isUintType :: SolType -> Maybe (Maybe Int)
isUintType = \case
  SolTyLitInt -> Just Nothing
  SolTyElem (flip HashMap.lookup uintTypes -> Just sz) -> Just (Just sz)
  _ -> Nothing

isBytesType :: SolType -> Maybe (Maybe Integer)
isBytesType = \case
  SolTyElem "bytes" -> Just Nothing
  SolTyElem (flip HashMap.lookup bytesTypes -> Just sz) -> Just (Just sz)
  _ -> Nothing

reifyCast :: SolType -> SolType -> ExprRef -> Context ExprRef
reifyCast tyFrom tyTo eref
  | tyFrom == tyTo = pure eref
  -- Cast from unsigned integer to address
  | Just _ <- isUintType tyFrom
  , let addressTy = SolTyElem "address", SolTyElem "address" <- tyTo = mkConvert addressTy
  -- Cast between integer types
  | Just _ <- isUintType tyFrom, Just _ <- isUintType tyTo = mkConvert tyTo
  -- Cast from unsigned integer to bytes
  | Just _ <- isUintType tyFrom, Just _ <- isBytesType tyTo = mkConvert tyTo
  -- Cast between bytesN types
  | Just (Just _) <- isBytesType tyFrom, Just (Just _) <- isBytesType tyTo = mkConvert tyTo
  | otherwise = pure eref
  where
    mkConvert toType = do
      eref' <- copyNode eref
      modifyContext
        $ (\ctx -> ctx{srcCtx_exprTypes = HashMap.insert eref' toType (srcCtx_exprTypes ctx)})
        . updateRef eref' (SolExprTypeConvert toType eref)
      pure eref'

goReifyExpr :: ExprRef -> SolExpr -> Context SolExpr
goReifyExpr eref = \case
  e@(SolExprLit SolLitAddr{}) -> do
    -- insert cast for address literals
    eref' <- copyNode eref
    modifyContext (updateRef eref' e)
    pure $ SolExprTypeConvert (SolTyElem "address") eref'
  SolExprBinaryOp op e1ref e2ref ty -> do
    e1tyMaybe <- getsContext (HashMap.lookup e1ref . srcCtx_exprTypes)
    e2tyMaybe <- getsContext (HashMap.lookup e2ref . srcCtx_exprTypes)
    (e1ref', e2ref') <-
      if | Just e1ty <- e1tyMaybe, Just e2ty <- e2tyMaybe ->
           (,) <$> reifyCast e1ty ty e1ref <*> reifyCast e2ty ty e2ref
         | otherwise -> pure (e1ref, e2ref)
    pure (SolExprBinaryOp op e1ref' e2ref' ty)
  SolExprIndex e1ref e2ref -> do
    -- Only need to convert the index parameter
    e1tyMaybe <- getsContext (HashMap.lookup e1ref . srcCtx_exprTypes)
    e2tyMaybe <- getsContext (HashMap.lookup e2ref . srcCtx_exprTypes)
    let indexable = \case
          SolTyMapping ty _ -> Just ty
          SolTyArr{} -> Just (SolTyElem "uint256")
          _ -> Nothing
    e2ref' <-
      if | Just ty <- e1tyMaybe >>= indexable , Just e2ty <- e2tyMaybe ->
           reifyCast e2ty ty e2ref
         | otherwise -> pure e2ref
    pure $ SolExprIndex e1ref e2ref'
  SolExprAssign op e1ref e2ref ty -> do
    e2tyMaybe <- getsContext (HashMap.lookup e2ref . srcCtx_exprTypes)
    e2ref' <- maybe (pure e2ref) (\e2Ty -> reifyCast e2Ty ty e2ref) e2tyMaybe
    pure (SolExprAssign op e1ref e2ref' ty)
  e@(SolExprFunCall fref erefs) -> do
    getsContext (getFunctionSig fref) >>= \case
      Nothing -> pure e
      Just (argTys, _, _) -> do
        erefs' <- forM (erefs `zip` argTys) $ \(er, ty) -> do
          mty <- getsContext (HashMap.lookup er . srcCtx_exprTypes)
          maybe (pure er) (\ety -> reifyCast ety ty er) mty
        pure $ SolExprFunCall fref erefs'
  e -> pure e

goReifyStmt :: StmtRef -> SolStmt -> Context SolStmt
goReifyStmt _sref stmt = getContext >>= \ctx0 -> case stmt of
  SolStmtVarDecl varDecls mValue
    | (NE.uncons -> (vdRef, Nothing)) <- varDecls
    , Just eref <- mValue
    , Just ty <- (HashMap.lookup eref . srcCtx_exprTypes) ctx0 -> do
      -- Assignment of single variable
      eref' <- reifyCast ty (varDecl_type (lookupRef vdRef ctx0)) eref
      pure $ SolStmtVarDecl (vdRef NE.:| []) (Just eref')
    | Just (flip lookupRef ctx0 -> SolExprTuple valueRefs) <- mValue
    , length varDecls == length valueRefs -> do
      error "todo reify tuple assignment"
  s -> pure s

reifyExpr :: ExprRef -> Context ExprRef
reifyExpr = replaceExprM goReifyExpr

reifyVarDecl :: SolVarDecl -> Context SolVarDecl
reifyVarDecl vd =
  case varDecl_value vd of
    Just eref -> do
      eref' <- reifyExpr eref
      mty <- getsContext (HashMap.lookup eref' . srcCtx_exprTypes)
      eref'' <- maybe (pure eref') (\ty -> reifyCast ty (varDecl_type vd) eref') mty
      pure $ vd{varDecl_value = Just eref''}
    Nothing -> pure vd

-- | Reify implicit type conversions
reifyConversions :: SourceCtx -> SourceCtx
reifyConversions = snd . runContext go
  where
    go = do
      contracts <- getsContext srcCtx_contracts
      forM_ contracts $ \c -> do
        forM_ (contract_body c) $ \cbref -> do
          cb <- getsContext (lookupRef cbref)
          case cb of
            CStateVar vdref -> do
              vd <- getsContext (lookupRef vdref)
              vd' <- reifyVarDecl vd
              modifyContext (updateRef vdref vd')
            f@CFun{cfun_body=body} -> do
              body' <- traverse (replaceStmtM goReifyExpr goReifyStmt) body
              modifyContext (updateRef cbref f{cfun_body=body'})
            _ -> pure ()
      pure ()
