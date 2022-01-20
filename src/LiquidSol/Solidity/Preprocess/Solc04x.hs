module LiquidSol.Solidity.Preprocess.Solc04x (removeSol04xEmit) where

import Control.Monad.State.Strict
import LiquidSol.Solidity.ContextMonad
import LiquidSol.Solidity.Syntax
import qualified Data.HashMap.Strict as HashMap

-- | Convert event "function calls" into emit statements
removeSol04xEmit :: SourceCtx -> SourceCtx
removeSol04xEmit = snd <$> runContext go
  where
    go = do
      ctx <- getContext
      forM_ (HashMap.toList (srcCtx_stmts ctx)) $ \(sref, s) -> do
        case s of
          SolStmtExpr eref
            | SolExprFunCall ef _ <- lookupRef eref ctx
            , SolExprIdent _ declRef <- lookupRef ef ctx
            , Just CEvent <- tryLookupRef declRef ctx ->
              putNode (unsafeCastTypedRef sref) SolStmtEmit
          _ -> pure ()
