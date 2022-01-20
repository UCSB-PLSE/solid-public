{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}
module LiquidSol.Solidity.Preprocess.Libraries
  (replaceSafeMath, copyLibraries) where

import Control.Monad
import Data.Bifunctor
import Data.Either (partitionEithers)
import qualified Data.HashMap.Strict as HashMap
import Data.Maybe (catMaybes)
import Data.Text (Text)
import qualified Data.Text as Text
import Prelude hiding (head)

import LiquidSol.Solidity.ContextMonad
import LiquidSol.Solidity.Syntax
import LiquidSol.Util.Unsafe

-- | Hacky function that drops ALL libraries and then replaces all SafeMath
-- method calls with unsafe math
replaceSafeMath :: SourceCtx -> SourceCtx
replaceSafeMath ctx0 = snd $ runContext go ctx0
  where
    go = do
      -- Find safe math library
      let safeMathLibs = [(r, c) | r@(flip lookupRef ctx0 -> c) <- libs, contract_name c == "SafeMath"]
      case safeMathLibs of
        (sm:_) -> goReplace sm
        [] -> pure ()
    goReplace (smRef, _sm) = do
      -- Replace safe math in all expressions
      allExprs <- getsContext srcCtx_exprs
      forM_ (HashMap.keys allExprs) $ \eref -> replaceInExpr (unsafeCastTypedRef eref)
      -- Drop SafeMath from contracts
      modifyContext (\ctx -> ctx{ srcCtx_contracts =
                                  HashMap.delete (asNodeRef smRef) (srcCtx_contracts ctx)})

    allContracts = srcCtx_contracts ctx0
    (libs, _) = partitionEithers [splitLib (unsafeCastTypedRef r) | (r, _) <- HashMap.toList allContracts]
    splitLib cref = case contract_kind (lookupRef cref ctx0) of
      SolLibraryKind -> Left cref
      _ -> Right cref
    ops = HashMap.fromList [("add", "+"), ("sub", "-"), ("mul", "*"), ("div", "/")]
    replaceInExpr eref = do
      ctx <- getContext
      case lookupRef eref ctx of
        SolExprFunCall fref args
          | SolExprMember e1 mname _ <- lookupRef fref ctx
          , Just (SolTyElem _) <- HashMap.lookup e1 (srcCtx_exprTypes ctx)
          , HashMap.member mname ops ->
            let newExpr = SolExprBinaryOp (ops `hmUnsafeLookup` mname) e1 (head args) (SolTyElem "uint256") in
              modifyContext (updateRef eref newExpr)
        _ -> pure ()

-- | Copy library bodies into contracts
copyLibraries :: SourceCtx -> SourceCtx
copyLibraries = snd . runContext go
  where
    go = do
      -- Find libraries and contracts
      allContracts <- getsContext (HashMap.toList . srcCtx_contracts)
      let splitLibs (unsafeCastTypedRef -> r, c) = case contract_kind c of
            SolLibraryKind -> Left r
            _ -> Right r
      let (libs, contracts) = partitionEithers (splitLibs <$> allContracts)
      -- TODO: Resolve using fors in contracts
      -- Rename library functions to fully qualified names
      fqnTable <- renameFqns libs
      -- Copy library cbodies into each contract and update identifier references
      copyLibs libs contracts fqnTable
      -- Drop all libraries and using fors
      dropLibs
      pure ()

    -- This returns a table of (library ref, member name, cbody ref, fqn)
    renameFqns :: Monad m => [ContractRef] -> ContextT m [(ContractRef, Text, NodeRef, Text)]
    renameFqns libs = fmap mconcat $
      forM libs $ \lref -> do
        l <- getsContext (lookupRef lref)
        let mangle n = contract_name l <> "$$" <> n
        idents <- forM (contract_body l) $ \cbref -> do
          npairs <- getsContext (lookupRef cbref) >>= \case
            f@CFun{cfun_name=fname} -> do
              let fname' = mangle fname <> "$" <> Text.pack (show (asNodeRef cbref))
              modifyContext (updateRef cbref f{cfun_name = fname'})
              pure (Just (fname, fname'))
            CStruct sname vds -> do
              let sname' = mangle sname
              modifyContext (updateRef cbref (CStruct sname' vds))
              pure (Just (sname, sname'))
            _ -> pure Nothing
          pure ((\(n, f) -> (lref, n, asNodeRef cbref, f)) <$> npairs)
        pure (catMaybes idents)

    copyLibs :: Monad m => [ContractRef] -> [ContractRef] -> [(ContractRef, Text, NodeRef, Text)] -> ContextT m ()
    copyLibs libs contracts fqnTable = do
      -- Copy library cbodies. Record mapping between (original, copy) refs.
     copied <- forM contracts $ \cref -> do
       copied <- forM libs $ \lref -> do
         c <- getsContext (lookupRef cref)
         l <- getsContext (lookupRef lref)
         libCbs <- traverse (\r -> (r,) <$> deepCopyCbody r) (contract_body l)
         -- Insert the copied cbodies
         modifyContext (updateRef cref c{contract_body = contract_body c <> (snd <$> libCbs)})
         pure (first asNodeRef <$> libCbs)
       pure (cref, HashMap.fromList (mconcat copied))
     -- Update library identifiers to point to new copies
     forM_ copied $ \(cref, refMap) -> do
       -- We need two maps. First is the FQN map, for mapping library members to copied defs.
       -- Second is ident map, for mapping existing idents to copied defs.
       let fqnMap = HashMap.fromList
             [((asNodeRef lr, n), (asNodeRef (refMap `hmUnsafeLookup` r), n')) | (lr, n, r, n') <- fqnTable]
           identMap = HashMap.fromList [(origRef, (asNodeRef (refMap `hmUnsafeLookup` origRef), n'))
                                       | (_, _, origRef, n') <- fqnTable]
           updStmt = replaceStmtM (goUpdExpr fqnMap identMap) (goUpdStmt fqnMap identMap)
           updExpr = replaceExprM (goUpdExpr fqnMap identMap)
           -- updType = goUpdType updMap
           updVarDecl = goUpdVarDecl fqnMap identMap
       c <- getsContext (lookupRef cref)
       forM (contract_body c) $ \cbref -> do
         cb' <- getsContext (lookupRef cbref) >>= \case
           f@CFun{cfun_args=args, cfun_rets=rets, cfun_body=body, cfun_mods=mods} -> do
             args' <- traverse updVarDecl args
             rets' <- traverse updVarDecl rets
             body' <- traverse updStmt body
             mods' <- traverse (\(r, es) -> (maybe r fst (HashMap.lookup r identMap),) <$> traverse updExpr es) mods
             pure (f{cfun_args=args', cfun_rets=rets', cfun_body=body', cfun_mods=mods'})
           CStruct name fields -> do
             fields' <- traverse updVarDecl fields
             pure (CStruct name fields')
           CStateVar vd -> CStateVar <$> updVarDecl vd
           cb -> pure cb
         modifyContext (updateRef cbref cb')

    goUpdType fqnMap identMap = \case
      SolTyUser r _
        | Just (r', x') <- HashMap.lookup r identMap ->
          pure (SolTyUser r' x')
      SolTyArr t msz -> SolTyArr <$> recur t <*> pure msz
      SolTyMapping t1 t2 ->
        SolTyMapping <$> recur t1 <*> recur t2
      SolTyFun ta tr ->
        SolTyFun <$> traverse recur ta <*> traverse recur tr
      SolTyTuple ts -> SolTyTuple <$> traverse recur ts
      t -> pure t
      where
        recur = goUpdType fqnMap identMap

    goUpdStmt fqnMap identMap _sref = \case
      SolStmtVarDecl vds me ->
        SolStmtVarDecl
          <$> traverse (recurWith goUpdVarDecl) vds
          <*> traverse (replaceExprM (recurWith goUpdExpr)) me
      s -> pure s
      where
        recurWith f = f fqnMap identMap

    goUpdExpr fqnMap identMap _eref e = getContext >>= \ctx -> case e of
      SolExprFunCall em args
        | SolExprMember e1 _ (Just r) <- lookupRef em ctx
        , Just (r', x) <- HashMap.lookup r identMap -> do
            modifyContext (updateRef em (SolExprIdent x r'))
            pure $ SolExprFunCall em (e1:args)
      SolExprMember e1 n _
        | SolExprIdent _ lr <- lookupRef e1 ctx
        , Just (r', n') <- HashMap.lookup (lr, n) fqnMap ->
          pure $ SolExprIdent n' r'
      SolExprIdent _ r
        | Just (r', x) <- HashMap.lookup r identMap -> pure $ SolExprIdent x r'
      _ -> pure e

    goUpdVarDecl fqnMap identMap vdref = getsContext (lookupRef vdref) >>= \vd -> do
      ty' <- goUpdType fqnMap identMap (varDecl_type vd)
      let updExpr eref e = goUpdExpr fqnMap identMap eref e *> pure eref
      expr' <- traverse (\eref -> getsContext (lookupRef eref) >>= updExpr eref) (varDecl_value vd)
      modifyContext (updateRef vdref vd{varDecl_type=ty', varDecl_value=expr'})
      pure vdref

    dropLibs = modifyContext (\ctx -> ctx{srcCtx_contracts = dropUsingFors ctx (doDrop ctx)})
      where
        doDrop ctx = HashMap.filterWithKey dropFn (srcCtx_contracts ctx)
        dropFn _ = \case
            SolContract{contract_kind=SolLibraryKind} -> False
            _ -> True
        dropUsingFors ctx =
          HashMap.map (\c -> c{contract_body = filter (filterUsingFor ctx) (contract_body c)})
        filterUsingFor ctx r = case lookupRef r ctx of
          CUsingFor{} -> False
          _ -> True
