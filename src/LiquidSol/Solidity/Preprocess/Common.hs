{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}
module LiquidSol.Solidity.Preprocess.Common where

import Control.Monad.State.Strict
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Text (Text)
import qualified Data.Text as Text

import LiquidSol.Solidity.ContextMonad
import LiquidSol.Solidity.Syntax
import LiquidSol.Util.Unsafe

-- | Lift the given expression into a variable, if needed.
-- This also directly passes in variables of reference types (assuming NO ALIASING).
anfLiftExpression :: Monad m => SolType -> TypedRef SolExpr
                  -> ContextT m (Maybe (TypedRef SolStmt), TypedRef SolExpr)
anfLiftExpression etype eref = getContext >>= \ctx0 ->
  case lookupRef eref ctx0 of
    SolExprIdent _ r
      | Just SolVarDecl{varDecl_loc=loc} <- tryLookupRef r ctx0
      , loc `elem` [SolLocMemory, SolLocStorage] -> pure (Nothing, eref)
    _ -> do
        -- Generate variable declaration
        let name = "__expr#" <> Text.pack (show (asNodeRef eref))
        let vd = SolVarDecl{ varDecl_name=name, varDecl_type=etype, varDecl_value=Nothing
                           , varDecl_loc=SolLocDefault, varDecl_vis=VisPrivate }
        vdRef <- createNode vd
        -- Generate declaration statement
        let decl = SolStmtVarDecl (pure vdRef) (Just eref)
        declRef <- createNode decl
        let cpLoc locs =
              let eloc = hmUnsafeLookup locs (asNodeRef eref) in
                HashMap.insert (asNodeRef declRef) eloc
                . HashMap.insert (asNodeRef vdRef) eloc
                $ locs
        modifyContext (\c -> updateRef declRef decl c{srcCtx_locs = cpLoc (srcCtx_locs c)})
        -- Generate new identifier
        eref' <- copyNode eref
        modifyContext $ updateRef eref' (SolExprIdent name (asNodeRef vdRef))
        pure (Just declRef, eref')

-- | Produce an inlined version of the given function with the given arguments
inlineFunction :: CbodyRef -> [ExprRef] -> [ExprRef] -> Context StmtRef
inlineFunction cbref argRefs retRefs =
  -- Deep copy the function body, arguments, and rets.
  deepCopyCbody cbref >>= \cbref' -> getsContext (lookupRef cbref') >>= \case
    CFun{cfun_args=args, cfun_rets=rets, cfun_body=Just body, cfun_mods=mods} ->
      goInline args rets mods body
    _ -> error "inlineFunction: attempting to inline non-function cbody (or function with no body)"
  where
    goInline args rets _mods body = do
      -- map each arg/ret declaration to the replacement arg/ret
      let identMap = HashMap.fromList ((asNodeRef <$> (args <> rets)) `zip` (argRefs <> retRefs))
          substStmt :: Monad m => StmtRef -> SolStmt
                    -> ContextT (StateT (HashMap NodeRef Text) m) SolStmt
          substStmt _ = \case
            SolStmtReturn{} -> error "inlineFunction: return when inlining not supported"
            SolStmtVarDecl vdRefs me -> do
              forM_ vdRefs $ \r -> do
                vd@SolVarDecl{varDecl_name=name} <- getsContext (lookupRef r)
                let newName = name <> "#in_" <> Text.pack (show (asNodeRef r))
                lift $ modify (HashMap.insert (asNodeRef r) newName)
                modifyContext  (updateRef r vd{varDecl_name=newName})
              pure (SolStmtVarDecl vdRefs me)
            s -> pure s

          substExpr :: Monad m => ExprRef -> SolExpr
                    -> ContextT (StateT (HashMap NodeRef Text) m) SolExpr
          substExpr _ = \case
            e@(SolExprIdent _ declRef)
              | Just eref' <- HashMap.lookup declRef identMap ->
                  -- Replace this identifier if it is a formal argument (or return value)
                  getsContext (lookupRef eref')
              | otherwise ->
                -- Replace this identifier name if it was defined in this function.
                lift (gets (HashMap.lookup declRef)) >>= \case
                  Just x' -> pure $ SolExprIdent x' declRef
                  Nothing -> pure e
            e -> pure e
      -- TODO: modifiers
      -- Return reference to the copied function body. (note: this has problems with return statements.)
      ctx0 <- getContext
      let inlineAction = runContextT (replaceStmtM substExpr substStmt body) ctx0
      let (stmt', ctx1) = evalState inlineAction HashMap.empty
      putContext ctx1
      pure stmt'
