{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}
module LiquidSol.Solidity.Preprocess.Inheritance
  (resolveSuper) where

import LiquidSol.Solidity.ContextMonad
import LiquidSol.Solidity.Syntax
import Control.Monad (forM)
import Data.Foldable (forM_)
import qualified Data.HashMap.Strict as HashMap
import Data.Maybe (catMaybes)
import Control.Monad.Extra (concatMapM)
import Data.HashMap.Strict (HashMap)
import LiquidSol.Util.Unsafe

resolveSuper :: SourceCtx -> SourceCtx
resolveSuper = snd . runContext go
  where
    go = do
      copied <- copyInherited
      updateRefs (HashMap.fromList [(c, refMap) | (c, _, refMap) <- copied])
    updateRefs copied = do
      contracts <- getsContext (HashMap.toList . srcCtx_contracts)
      forM contracts $ \(ctref, ct) -> do
        let refMap = HashMap.fromList [(asNodeRef r, asNodeRef r')
                                      | (r, r') <- copied `hmUnsafeLookup` ctref]
        forM (contract_body ct) $ \cbref ->
          getsContext (lookupRef cbref) >>= \case
            f@CFun{cfun_body=Just body} -> do
              body' <- replaceStmtM (visitExpr refMap) (\_ s -> pure s) body
              modifyContext (updateRef cbref f{cfun_body=Just body'})
            _ -> pure ()

    visitExpr :: Monad m => HashMap NodeRef NodeRef -> ExprRef -> SolExpr -> ContextT m SolExpr
    visitExpr refMap _ e = case e of
      SolExprFunCall e1ref _ -> do
        getsContext (lookupRef e1ref) >>= \case
          -- Replace super.f() -> Parent.f()
          SolExprMember e2ref x (Just r)
            | Just r' <- HashMap.lookup r refMap -> do
                e2 <- getsContext (lookupRef e2ref)
                getsContext (tryLookupRef r') >>= \case
                  Just CFun{cfun_name=name}
                    | SolExprIdent "super" _ <- e2 ->
                      modifyContext (updateRef e1ref (SolExprIdent name r'))
                  _ -> pure ()
          -- Replace f() -> Parent.f()
          SolExprIdent _ r
            | Just r' <- HashMap.lookup r refMap ->
                getsContext (tryLookupRef r') >>= \case
                  Just CFun{cfun_name=name} ->
                    modifyContext (updateRef e1ref (SolExprIdent name r'))
                  _ -> pure ()
          _ -> pure ()
        pure e
      _ -> pure e

    copyInherited = do
      -- Copy inherited methods
      contracts <- getsContext (HashMap.toList . srcCtx_contracts)
      copied <- traverse (uncurry runContract) contracts
      forM_ copied $ \(r, ct, cp) -> do
        let ctbody = (snd <$> cp) <> contract_body ct
        modifyContext (updateRef (unsafeCastTypedRef r) (ct{contract_body = ctbody}))
      pure copied
    runContract cref contract = do
      -- Copy inherited methods
      bases <- traverse (getsContext . lookupRef) (contract_bases contract)
      copied <- flip concatMapM (tail bases) $ \ans -> do
        forM (contract_body ans) $ \cbref ->
          getsContext (lookupRef cbref) >>= \case
            CFun{cfun_isCtor=False, cfun_body=Just _} -> do
              cbref' <- deepCopyCbody cbref
              getsContext (lookupRef cbref') >>= \case
                f@CFun{cfun_name=name} ->
                  modifyContext (updateRef cbref' f{cfun_name = contract_name ans <> "." <> name})
                _ -> pure ()
              pure $ Just (cbref, cbref')
            _ -> pure Nothing
      pure (cref, contract, catMaybes copied)
