{-# LANGUAGE OverloadedStrings, FlexibleContexts, ScopedTypeVariables #-}
module LiquidSol.SymEncode
  ( sortEncode
  , arith2Encode, constEncode, predEncode
  , relEncode
  , envEncode
  , SmtEncodeT(..), resetSmtSolver, initSmtSolver, logMessage, withSolverScope
  , encNewVar, encNewVar_, encWithNewVar
  , getVar, getVar_, getVarSort, applySortProps
  , getMapRepr, getMapRepr_, getMapSums, getMapSums_
  , liftSolver, getSolver, checkSat, evalSmtEncodeT
  , pushHead, pushBody, applyAssertStack, clearAssertStack, applyAndClearAssertStack
  , getAuxExpr, getUnintFunSorts) where

import Control.Monad.Extra (maybeM, fromMaybeM, concatMapM)
import Control.Monad.State.Strict
import Control.Monad.Except (MonadError)
import Data.DList (DList)
import qualified Data.DList as DList

import Data.Maybe (fromMaybe)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
-- import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Traversable (forM)
import qualified SimpleSMT as S hiding (ppSExpr)

import qualified LiquidSol.Syntax as LS
import qualified LiquidSol.Logic as LS
import LiquidSol.LiquidTypes (LocalEnv)
import qualified LiquidSol.LiquidTypes as LS
import qualified LiquidSol.AggProps as Agg
import LiquidSol.PrettyPrint

import LiquidSol.Util.Unsafe (unsafeLookup)
import qualified LiquidSol.SmtProcs as S
-- import Data.Foldable (traverse_)

import qualified LiquidSol.Solidity.Types as SolTypes
import System.IO (hFlush, IOMode(WriteMode), openFile, hClose)
import Data.Time.Clock.System (systemNanoseconds, systemSeconds, getSystemTime)
import LiquidSol.LiOpts (LiOpts)
import qualified LiquidSol.LiOpts as LiOpts
import Control.Applicative (Alternative((<|>)))
import System.Directory.Extra (createDirectoryIfMissing)
import LiquidSol.SortCheck (getPredSort, tcEnvToSortEnv)
import LiquidSol.Util.Unsafe (fromJust)
import Control.Monad.Reader.Class (MonadReader)

type HornEnv = Map String S.SExpr

data EncState = EncState
  { esRename :: Map Text S.SExpr
  , esMaxId :: Int
  , esSolver :: S.Solver
  , esArrProps :: Map LS.Sort ((String, S.SExpr), (String, S.SExpr)) -- repr(name, sort), len(name, sort)
  , esMapReprs :: Map LS.Sort (String, S.SExpr) -- name, sort
  , esMapSums :: Map Agg.PathOp (String, S.SExpr) -- name, sort
  , esMapNnzs :: Map Agg.PathOp (String, S.SExpr) -- name, sort
  , esStructs :: Map Text (S.SExpr, S.SExpr, [(Text, (S.SExpr, LS.Sort))]) -- sort, constructor, fields(fun, sort)
  , esClauseHead :: [S.SExpr]
  , esClauseBody :: [S.SExpr]
  , esSymVars :: HornEnv
  , esDelta :: LS.Delta ()
  , esLogger :: Maybe S.Logger
  }

newtype SmtEncodeT m a = SmtEncodeT { unSmtEncodeT :: StateT EncState m a }
  deriving ( Functor, Applicative, Monad
           , MonadState EncState
           , MonadError e
           , MonadIO
           , MonadTrans
           , MonadReader s)

logMessage :: MonadIO m => String -> SmtEncodeT m ()
logMessage m = gets esLogger >>= \case
  Just l -> liftIO $ S.logMessage l m
  Nothing -> pure ()

-- * Sorts
arraySortName :: String
arraySortName = "SolArray"

mapSortName :: String
mapSortName = "Map"

stringSortName :: String
stringSortName = "SolByte"

-- unsigned integers
uintBounds :: Maybe Int -> S.SExpr -> S.SExpr
uintSort_ :: String
uintSort :: S.SExpr
uintDiv, uintMod :: String
uConst :: Integer -> S.SExpr
uintMax_ :: Int -> String
uintMax :: Int -> S.SExpr
u256Add, u256Sub, u256Mul, {- u256Div,-} u256Lt, u256Leq, u256Gt, u256Geq :: S.SExpr -> S.SExpr -> S.SExpr
-- u256FromInt, u256ToInt :: S.SExpr -> S.SExpr

{- integer configuration -}

uintDiv = "uint_div"
uintMod = "uint_mod"
uintBounds Nothing i = u256Geq i (uConst 0)
uintBounds (Just n) i = S.and (u256Geq i (uConst 0)) (u256Leq i (uintMax n))
uintSort_ = "uint_t"
uintSort = S.const uintSort_
uConst = S.int
uintMax_ n = "uint" <> show n <> "Max"
uintMax = S.const . uintMax_
u256Add = S.add
u256Sub = S.sub
u256Mul = S.mul
-- u256Div = S.div
u256Leq = S.leq
u256Lt = S.lt
u256Geq = S.geq
u256Gt = S.gt
-- u256FromInt = id
-- u256ToInt = id

{- bitvec configuration -}
{-
uintBounds i = S.and (u256Geq i (uConst 0)) (u256Leq i u256Max)
uintSort = S.const "uint256_t"
uConst = S.nat2bv 256 . S.int
u256Max = S.const "uint256Max"
u256Add = S.bvAdd
u256Sub = S.bvSub
u256Mul = S.bvMul
u256Div = S.bvUDiv
u256Leq = S.bvULeq
u256Lt = S.bvULt
u256Geq e1 e2 = S.not (S.bvULt e1 e2)
u256Gt e1 e2 = S.not (S.bvULeq e1 e2)
u256FromInt = S.nat2bv 256
u256ToInt = S.bv2nat
-}

-- * Encoding

evalSmtEncodeT :: MonadIO m => LiOpts -> LS.Delta () -> SmtEncodeT m a -> m a
evalSmtEncodeT opts delta m = do
  -- TODO: logging
  timestamp <- (\t -> show (systemSeconds t) <> "_" <> show (systemNanoseconds t)) <$> liftIO getSystemTime
  (fileLogHandleM, fileLogger) <- case LiOpts.logDir opts of
    Just logDir -> do
      liftIO $ createDirectoryIfMissing True logDir
      handle <- liftIO $ openFile (logDir <> "/" <> "liquidsol-query-" <> timestamp <> ".log") WriteMode
      fileLogger <- do
        l <- liftIO $ S.newLoggerWithHandler 0 handle
        let l' = l{S.logSexp = logSexp, S.logFormat = S.logFormat l}
            logSexp t e = S.logMessage l' $
              case t of
                    S.LogRecv -> "; recv: " <> S.showsSExpr e ""
                    _ -> show (S.ppSExpr e)
        pure l'
      pure (Just handle, Just fileLogger)
    Nothing -> pure (Nothing, Nothing)
  stdoutLogger <- if LiOpts.logSmt opts then Just <$> liftIO (S.newLogger 0) else pure Nothing
  let logger =
        if | Just fl <- fileLogger , Just sl <- stdoutLogger ->
             Just (S.multicastLogger fl sl)
           | otherwise -> fileLogger <|> stdoutLogger
  solver <- liftIO $ S.newSolver (LiOpts.z3Path opts) ["-in", "-smt2"] logger
  let es = EncState { esRename = Map.empty, esMaxId = 0, esSolver = solver
                    , esArrProps = Map.empty
                    , esMapReprs = Map.empty, esMapSums = Map.empty, esMapNnzs = Map.empty
                    , esStructs = Map.empty
                    , esClauseHead = [], esClauseBody = [], esSymVars = Map.empty
                    , esDelta = delta
                    , esLogger = logger
                    }
  result <- evalStateT (unSmtEncodeT (initSmtSolver opts *> m)) es
  _ <- liftIO $ S.stop solver
  liftIO $ forM_ fileLogHandleM $ \h ->
    hFlush h *> hClose h
  pure result

resetSmtSolver :: MonadIO m => LiOpts -> SmtEncodeT m ()
resetSmtSolver opts = do
  EncState{esSolver=solver} <- get
  liftIO $ S.simpleCommand solver ["reset"]
  initSmtSolver opts

initSmtSolver :: MonadIO m => LiOpts -> SmtEncodeT m ()
initSmtSolver opts = do
  EncState{esSolver=solver, esDelta=delta} <- get
  liftIO $ S.setOption solver ":timeout" (show (LiOpts.smtTimeout opts))  -- 10 second timeout
  liftIO $ S.setOption solver ":fp.engine" "spacer"
  liftIO $ S.setLogic solver "HORN"
  logMessage "; Declare sorts"
  -- Declare string sort
  _ <- liftIO $ S.declareSort solver stringSortName 0
  -- Declare uint256 sort
  _ <- liftIO $ S.defineSort solver uintSort_ S.tInt
  -- Declare uintMax
  liftIO $ forM_ [1..32] $ \i ->
    let n = i * 8 in
      S.define solver (uintMax_ n) uintSort (uConst (SolTypes.uintMax n))
  -- Declare uintDiv and uintMod
  _ <- liftIO $
    let args = [("x", uintSort), ("y", uintSort), ("z", uintSort)]
        x = S.const "x"
        y = S.const "y"
        z = S.const "z"
        -- z = x / y ==> z * y <= x && x < (z + 1) * y
        divApprox = S.and (S.fun "<=" [S.mul z y, x]) (S.fun "<" [x, S.mul (S.add z (S.int 1)) y])
        divBody = divApprox -- S.ite (S.eq y (S.int 0)) (S.bool False) divApprox
        -- z = x % y ==> (z <= y and x < y ==> z = x)
        modBody = S.and (S.lt z y) (S.implies (S.lt x y) (S.eq z x)) in
      S.defineFun solver uintDiv args S.tBool divBody *>
      S.defineFun solver uintMod args S.tBool modBody

  -- Declare mapping sort
  _ <- liftIO $ S.declareSort solver mapSortName 1

  -- Declare nnzupd
  _ <- liftIO $
    let out = S.const "out"
        old = S.const "old"
        xold = S.const "xold"
        xnew = S.const "xnew" in
      S.defineFun solver "nnzupd" [("out", uintSort), ("old", uintSort), ("xold", uintSort), ("xnew", uintSort)] S.tBool $
        S.ite (S.leq xold (S.int 0))
          (S.ite (S.leq xnew (S.int 0)) (S.eq out old) (S.eq out (S.add old (S.int 1))))
          (S.ite (S.leq xnew (S.int 0)) (S.eq out (S.sub old (S.int 1))) (S.eq out old))

  -- Declare array sort
  _ <- liftIO $ S.declareSort solver arraySortName 1

  -- Declare structs
  let structs = Map.toList (LS.delta_structs delta)
  scts <- forM structs $ \(name, flds) -> do
    let sname = mangleStruct name
    let sort = S.Atom sname
    sflds <- forM flds $ \(f, t) -> do
      let s = LS.rtypeToSort t
      ssort <- sortEncode s
      pure (f, mangleStructField name f, s, ssort)
    let ctor = sname <> "$$cons"
    pure (name, (sort, S.const ctor, sflds))
  let sctMap = Map.fromList
        [ (name, (sort, ctor, flds'))
        | (name, (sort, ctor, flds)) <- scts
        , let flds' = [(f, (S.Atom sf, fsort)) | (f, sf, fsort, _) <- flds] ]
  -- Do it all at once so we don't have to care about struct ordering.
  -- Solidity structs *usually* aren't mutually recursive.
  let (structSorts, structCtors) = unzip
        [ (S.List [sort, S.int 0], S.List [S.List (ctor:fldDefns)])
        | (_, (sort, ctor, flds)) <- scts
        , let fldDefns = [S.fun f [sfsort] | (_, f, _, sfsort) <- flds] ]
  let structCmd = S.fun "declare-datatypes" [S.List structSorts, S.List structCtors]
  _ <- liftIO $ S.command solver structCmd
  modify (\st -> st{esStructs = sctMap})


withSolverScope :: MonadIO m => SmtEncodeT m a -> SmtEncodeT m a
withSolverScope m = do
  st@EncState{esSolver = solver} <- get
  liftIO $ S.push solver
  result <- m
  liftIO $ S.pop solver
  put st
  pure result

liftSolver :: MonadIO m => (S.Solver -> a -> IO b) -> a -> SmtEncodeT m b
liftSolver f x = gets esSolver >>= \solver -> liftIO (f solver x)

getSolver :: Monad m => SmtEncodeT m S.Solver
getSolver = gets esSolver

-- | Push the formula into the head of the Horn clause
pushHead :: MonadIO m => S.SExpr -> SmtEncodeT m ()
pushHead se =
  modify (\st -> st{esClauseHead = se : esClauseHead st})

-- | Push the formula into the body of the Horn clause
pushBody :: MonadIO m => S.SExpr -> SmtEncodeT m ()
pushBody se =
  modify (\st -> st{esClauseBody = se : esClauseBody st})

-- | Assert everything in the assert stack.
applyAssertStack :: MonadIO m => SmtEncodeT m ()
applyAssertStack = do
  EncState{esSolver = solver, esClauseHead = hs, esClauseBody = bs, esSymVars = vars} <- get
  unless (Map.null vars) $ liftIO $
    S.assert solver (S.sForall (Map.toList vars) (S.implies (S.andMany hs) (S.andMany bs)))

-- | Clear the assert stack.
clearAssertStack :: MonadIO m => SmtEncodeT m ()
clearAssertStack = modify (\st -> st{esClauseHead = [], esClauseBody = [], esSymVars = Map.empty
                                    , esRename = Map.empty
                                    , esArrProps = Map.empty
                                    , esMapReprs = Map.empty
                                    , esMapNnzs = Map.empty
                                    , esMapSums = Map.empty})

applyAndClearAssertStack :: MonadIO m => SmtEncodeT m ()
applyAndClearAssertStack = applyAssertStack *> clearAssertStack

checkSat :: MonadIO m => SmtEncodeT m S.Result
checkSat = do
  applyAndClearAssertStack
  gets esSolver >>= (liftIO . S.check)

mkFreshVar_ :: MonadIO m => LS.Sort -> SmtEncodeT m String
mkFreshVar_ sort = do
  EncState{esMaxId = xid} <- get
  let name = "s" <> show xid
  smtSort <- sortEncode sort
  modify (\st' -> st'{esMaxId = xid + 1, esSymVars = Map.insert name smtSort (esSymVars st')})
    {-
  case sort of
    LS.SortArray{} -> do
      -- encode outputs of len and repr relations
      pushHead (uintBounds (Just 256) (S.fun arrayLenName [S.const name]))
    LS.SortStruct structName -> do
      (_, flds) <- gets ((Map.! structName) . esStructs)
      let flds' = [(fldName, name <> "_" <> Text.unpack fldName, fldSort) | (fldName, fldSort) <- Map.toList flds]
      modify (\st' -> st'
               { esStructVars = Map.insert name (Map.fromList [(f, s) | (f, _, s) <- flds']) (esStructVars st')
               , esSymVars = esSymVars st' <> Map.fromList [(sv, srt) | (_, sv, srt) <- flds'] })
    _ -> pure ()
    -}
  pure name

mkFreshVar :: MonadIO m => LS.Sort -> SmtEncodeT m S.SExpr
mkFreshVar sort = S.const <$> mkFreshVar_ sort


encNewVar_ :: MonadIO m => Text -> LS.Sort -> SmtEncodeT m String
encNewVar_ x sort = do
  v <- mkFreshVar_ sort
  applySortProps sort v
  let sv = S.const v
  modify (\st -> st{esRename = Map.insert x sv (esRename st)})
  pure v

encNewVar :: MonadIO m => Text -> LS.Sort -> SmtEncodeT m S.SExpr
encNewVar x sort = S.const <$> encNewVar_ x sort

encWithNewVar :: MonadIO m => Text -> LS.Sort -> (S.SExpr -> SmtEncodeT m a) -> SmtEncodeT m a
encWithNewVar x sort f = do
  st <- get
  res <- encNewVar x sort >>= f
  modify (\st' -> st'{esRename = (esRename st)})
  pure res


getArrayProps :: MonadIO m => LS.Sort -> SmtEncodeT m (S.SExpr -> S.SExpr, S.SExpr -> S.SExpr)
getArrayProps = fmap f . getArrayProps_
  where
    f ((l, _), (r, _)) = (S.select (S.const l), S.select (S.const r))

-- | Get array length and repr variables, given element sort
getArrayProps_ :: MonadIO m => LS.Sort -> SmtEncodeT m ((String, S.SExpr), (String, S.SExpr))
getArrayProps_ elemSort = fromMaybeM mk fetch
  where
    fetch = gets (Map.lookup elemSort . esArrProps)
    mk = do
      let reprName = "|Arepr" <> sortAbbrev elemSort <> "|"
          lenName = "|Alen" <> sortAbbrev elemSort <> "|"
      elemSort' <- sortEncode elemSort
      let reprSort = S.tArray (S.fun arraySortName [elemSort']) (S.tArray S.tInt elemSort')
      let lenSort = S.tArray (S.fun arraySortName [elemSort']) S.tInt
      let props = ((lenName, lenSort), (reprName, reprSort))
      modify (\st -> st{ esSymVars = Map.insert reprName reprSort
                                   . Map.insert lenName lenSort
                                   $ esSymVars st
                       , esArrProps = Map.insert elemSort props (esArrProps st) })
      pure props
  --gets (\st -> (esArrayVars st) `unsafeLookup` a)

sortAbbrev :: LS.Sort -> String
sortAbbrev = \case
  LS.SortInt _ -> "I"
  LS.SortBool -> "B"
  LS.SortByte -> "By"
  LS.SortStruct n -> "S:" <> Text.unpack n <> ":"
  LS.SortMapping _ s -> "M" <> sortAbbrev s
  LS.SortArray s _ -> "A" <> sortAbbrev s

-- | Get repr of map
getMapRepr :: MonadIO m => LS.Sort -> SmtEncodeT m (S.SExpr -> S.SExpr)
getMapRepr sort = getter <$> getMapRepr_ sort
  where
    getter (n, _) = S.select (S.const n)

getMapRepr_ :: MonadIO m => LS.Sort -> SmtEncodeT m (String, S.SExpr)
getMapRepr_ sort = fromMaybeM mk fetch
  where
    fetch = gets (Map.lookup sort . esMapReprs)
    mk = do
      let name = "|repr" <> sortAbbrev sort <> "|"
      valSort <- sortEncode sort
      let reprSort = S.tArray (S.fun mapSortName [valSort]) (S.tArray S.tInt valSort)
      modify (\st -> st{ esSymVars = Map.insert name reprSort (esSymVars st)
                       , esMapReprs = Map.insert sort (name, reprSort) (esMapReprs st) })
      pure (name, reprSort)

-- | Get sum of map given the sort of the VALUE
getMapSums :: MonadIO m => LS.Sort -> SmtEncodeT m (Map Agg.PathOp (S.SExpr -> S.SExpr))
getMapSums valSort = Map.map getter <$> getMapSums_ valSort
  where
    getter (name, _) = S.select (S.const name)

getMapSums_ :: MonadIO m => LS.Sort -> SmtEncodeT m (Map Agg.PathOp (String, S.SExpr))
getMapSums_ valSort = do
  delta <- gets esDelta
  let paths = Set.toList (Agg.splitSortPath delta valSort)
      fetch p = gets (Map.lookup p . esMapSums)
      pathToSort = \case
        Agg.I -> S.tInt
        Agg.M p -> S.fun mapSortName [pathToSort p]
        Agg.S n _ _ -> S.const (mangleStruct n)
      mk p = do
        let name = "|" <> Agg.pathToGhostVar "sum" p <> "|"
        let ssort = S.tArray (S.fun mapSortName [pathToSort p]) S.tInt
        modify (\st -> st{ esSymVars = Map.insert name ssort (esSymVars st)
                         , esMapSums = Map.insert p (name, ssort) (esMapSums st) })
        pure (name, ssort)
  sums <- forM paths (\p -> (p,) <$> fromMaybeM (mk p) (fetch p))
  pure (Map.fromList sums)

getMapNnz :: MonadIO m => LS.Sort -> SmtEncodeT m [S.SExpr -> S.SExpr]
getMapNnz valSort = fmap (\(f, _) -> \e -> S.select (S.const f) e) <$> getMapNnz_ valSort

getMapNnz_ :: MonadIO m => LS.Sort -> SmtEncodeT m [(String, S.SExpr)]
getMapNnz_ valSort = do
  let mk = do
        let name = "|nnz|"
        let ssort = S.tArray (S.fun mapSortName [uintSort]) S.tInt
        modify (\st -> st{ esSymVars = Map.insert name ssort (esSymVars st)
                         , esMapNnzs = Map.insert Agg.I (name, ssort) (esMapNnzs st) })
        pure (name, ssort)
      fetch = gets (Map.lookup Agg.I . esMapNnzs)
  case valSort of
    LS.SortInt{} -> pure <$> fromMaybeM mk fetch
    _ -> pure []

mangleStruct :: Text -> String
mangleStruct n = "Struct_" <> Text.unpack n

mangleStructField :: Text -> Text -> String
mangleStructField n f = Text.unpack ("Struct_" <> n <> "$$" <> f)

sortEncode :: MonadIO m => LS.Sort -> SmtEncodeT m S.SExpr
sortEncode = \case
  LS.SortInt{} -> pure uintSort
  LS.SortBool -> pure S.tBool
  LS.SortMapping _ t2 -> (\s -> S.fun mapSortName [s]) <$> sortEncode t2
  LS.SortArray t _ -> do
    sort' <- sortEncode t
    pure $ S.fun arraySortName [sort']
  LS.SortStruct n -> pure $ S.Atom (mangleStruct n)
  LS.SortByte -> pure (S.const stringSortName)

arith2Encode :: MonadIO m => LS.Arith2 -> (S.SExpr -> S.SExpr -> SmtEncodeT m S.SExpr)
arith2Encode op = case op of
  LS.AAdd -> liftPure u256Add
  LS.ASub -> liftPure u256Sub
  LS.AMul -> liftPure u256Mul
  LS.ADiv -> approx uintDiv
  LS.AMod -> approx uintMod -- liftPure S.mod
  LS.AAddMod -> wrappedAdd
  where
    liftPure f e1 e2 = pure (f e1 e2)
    wrappedAdd e1 e2 = do
      let e' = S.add e1 e2
      -- FIXME: this is an unsound hack
      let maxInt = SolTypes.uint256Max
      pure $ S.ite (S.gt e' (S.int maxInt)) (S.sub e' (S.int (maxInt + 1))) e'
    approx fname e1 e2 = do
      eres <- mkFreshVar_ (LS.SortInt Nothing)
      applySortProps (LS.SortInt Nothing) eres
      pushHead (S.fun fname [e1, e2, S.const eres])
      pure (S.const eres)

getVarSort :: LocalEnv p -> Text -> LS.Sort
getVarSort env x = case LS.localEnvLookup x env of
  Just (LS.RType _ ty _) -> LS.skelToSort ty
  Nothing -> error $ "getVarSort: failed to find " <> show x <> " in env"

applySortProps :: MonadIO m => LS.Sort -> String -> SmtEncodeT m ()
applySortProps sort v = case sort of
  LS.SortArray elemSort msz -> do
    (slen, _) <- getArrayProps elemSort
    case msz of
      Just len -> pushHead (S.eq (slen (S.const v)) (S.int (toInteger len)))
      Nothing -> pushHead (uintBounds (Just 256) (slen (S.const v)))
  LS.SortMapping _ valSort -> do
    sums <- getMapSums valSort
    forM_ (Map.elems sums) $ \ssum -> pushHead (S.geq (ssum (S.const v)) (S.int 0))
    nnzs <- getMapNnz valSort
    forM_ nnzs $ \snnz ->
      -- hack
      let sz = case valSort of
            LS.SortInt (Just s) -> s
            _ -> 256
      in
      pushHead (S.geq (snnz (S.const v)) (S.int 0)) *>
      pushHead (S.leq (snnz (S.const v)) (uintMax sz))
  LS.SortInt m -> pushHead (uintBounds m (S.const v))
  _ -> pure ()

getVar_ :: MonadIO m => LocalEnv p -> Text -> SmtEncodeT m String
getVar_ env x = maybeM mkVar (pure . unwrapVar) (gets (Map.lookup x . esRename))
  where
    unwrapVar = \case
      S.Atom n -> n
      _ -> undefined
    -- ty = LS.rtypeSkel $ fromJust (LS.localEnvLookup x env)
    mkVar = do
      let sort = getVarSort env x
      encNewVar_ x sort

getVar :: MonadIO m => LocalEnv p -> Text -> SmtEncodeT m S.SExpr
getVar env x = S.const <$> getVar_ env x

constEncode :: MonadIO m => LocalEnv p -> LS.Constant -> SmtEncodeT m S.SExpr
constEncode env = \case
  LS.CInt x -> pure $ S.int x
  LS.CByte _ -> mkFreshVar LS.SortByte -- pure $ S.int (toInteger x)
  LS.CAddress x -> pure $ S.int x
  LS.CBool b -> pure $ S.bool b
  LS.CMapZero t1 t2 -> do
    let sort = LS.skelToSort (LS.TyMapping t1 t2)
    let valSort = LS.skelToSort t2
    a <- mkFreshVar_ sort
    let sa = S.const a

    -- repr
    zeroVal <- constEncode env (LS.zeroValue t2)
    valSort' <- sortEncode valSort
    let zeroConst = S.List [S.List [S.Atom "as", S.Atom "const", S.tArray S.tInt valSort'], zeroVal]
    repr <- getMapRepr valSort
    pushHead (S.eq (repr sa) zeroConst)

    -- sum
    sums <- getMapSums valSort
    forM_ sums (\ssum -> pushHead (S.eq (ssum sa) (S.int 0)))

    -- nnz
    nnz <- getMapNnz valSort
    forM_ nnz (\snnz -> pushHead (S.eq (snnz sa) (S.int 0)))

    pure sa
  LS.CArrZero t msz -> do
    let elemSort = LS.skelToSort t
    let reprSort = LS.SortArray elemSort msz
    a <- mkFreshVar_ reprSort
    let sa = S.const a
    (slen, srepr) <- getArrayProps elemSort
    zeroVal <- constEncode env (LS.zeroValue t)
    valSort <- sortEncode (LS.skelToSort t)
    pushHead (S.eq (slen sa) (S.int (fromMaybe 0 msz)))
    pushHead (S.eq (srepr sa) (S.arrayConst (S.tArray S.tInt valSort) zeroVal))
    {-
    case t of
      LS.TyInt{} -> pushHead (S.fun "sum" [sa, S.int 0])
      _ -> pure ()
    -}
    pure sa
  LS.CStruct n _flds -> do
    v <- mkFreshVar (LS.SortStruct n)
    flds <- gets (Map.fromList . (`unsafeLookup` n) . LS.delta_structs . esDelta)
    (_, cons, cflds) <- gets ((`unsafeLookup` n) . esStructs)
    flds' <- forM cflds $ \(f, _) -> constEncode env (LS.zeroValue (LS.rtypeSkel (flds `unsafeLookup` f)))
    let v' = S.List (cons:flds')
    pushHead (S.eq v v')
    pure v
  LS.CString _ -> mkFreshVar (LS.SortArray LS.SortByte Nothing)

predEncode :: MonadIO m => LocalEnv p -> LS.Pred -> SmtEncodeT m S.SExpr
predEncode env = \case
  LS.PConst c -> constEncode env c
  LS.PVar x -> getVar env x
  LS.PArith2 op p1 p2 -> do
    s1 <- predEncode env p1
    s2 <- predEncode env p2
    arith2Encode op s1 s2
  LS.PAnd p1 p2 -> S.and <$> predEncode env p1 <*> predEncode env p2
  LS.POr p1 p2 -> S.or <$> predEncode env p1 <*> predEncode env p2
  LS.PNot p1 -> S.not <$> predEncode env p1
  LS.PRel rel p1 p2 -> relEncode env rel p1 p2
  LS.PImplies p q -> S.implies <$> predEncode env p <*> predEncode env q
  LS.PIff p q -> do
    p' <- predEncode env p
    q' <- predEncode env q
    pure (S.or (S.and p' q') (S.and (S.not p') (S.not q')))
  LS.PMapInd em ei -> do
    sem <- predEncode env em
    si <- predEncode env ei
    let s = case sem of
          S.Atom s_ -> s_
          _ -> error "predEncode: invariant violated: mapping should be a symbolic variable"
    getSort em >>= \case
      LS.SortArray sort _ -> do
        (_, srepr) <- getArrayProps sort
        sv <- mkFreshVar_ sort
        let sval = S.const sv
        pushHead (S.eq sval (S.select (srepr sem) si))
        applySortProps sort sv
        pure sval
      LS.SortMapping _ vsort -> do
        v <- mkFreshVar_ vsort
        let sv = S.const v
        repr <- getMapRepr vsort
        pushHead (S.eq sv (S.select (repr (S.const s)) si))
        applySortProps vsort v
        pure sv
      _ -> undefined
  LS.PMapPut em ei eval -> do
    sem <- predEncode env em
    si <- predEncode env ei
    sval <- predEncode env eval
    let v = case sem of
          S.Atom s_ -> s_
          _ -> error "predEncode: invariant violated: mapping should be a symbolic variable"
        sv = S.const v
    asort <- getSort em
    v' <- mkFreshVar_ asort
    let sv' = S.const v'
    case asort of
      LS.SortArray t _ -> do
        (slen, srepr) <- getArrayProps t
        pushHead (S.eq (slen sv') (slen sv))
        pushHead (S.eq (srepr sv') (S.store (srepr sv) si sval))
      LS.SortMapping _ vsort -> do
        repr <- getMapRepr vsort
        pushHead (S.eq (repr sv') (S.store (repr sv) si sval))
      _ -> undefined
    pure sv'
  LS.PField e f -> do
    e' <- predEncode env e
    getSort e >>= \case
      LS.SortStruct name -> do
        (fld, fsort) <- gets ((\(_, _, flds) -> Map.fromList flds `unsafeLookup` f) . (`unsafeLookup` name) . esStructs)
        sf <- mkFreshVar_ fsort
        pushHead (S.eq (S.const sf) (S.List [fld, e']))
        applySortProps fsort sf
        pure (S.const sf)
      LS.SortArray t _ | f == "length" -> do
        (slen, _) <- getArrayProps t
        pure (slen e')
      sort ->
        error $ "predEncode: unexpected field access: " <> show e <> ", " <> show f <> ", " <> show sort <> ", " <> show e'
  LS.PFieldUpd e f ef -> do
    se <- predEncode env e
    sef <- predEncode env ef
    getSort e >>= \case
      LS.SortStruct name -> do
        (_, cons, fldInfo) <- gets ((`unsafeLookup` name) . esStructs)
        se' <- mkFreshVar (LS.SortStruct name)
        -- Equate all of the fields, except for the updated one.
        let flds' = [ if fld == f then sef else S.List [fGet, se]
                    | (fld, (fGet, _)) <- fldInfo]
        pushHead $ S.eq se' (S.List (cons:flds'))
        pure se'
      -- TODO: dynamic array resizing not supported yet
      arrSort@(LS.SortArray elemSort _)
        | f == "length" -> do
            let s = case se of
                      S.Atom s_ -> s_
                      _ -> error "predEncode: invariant violated: array should be a symbolic variable"
            (slen, srepr) <- getArrayProps elemSort
            s' <- mkFreshVar_ arrSort
            pushHead $ S.eq (srepr (S.const s')) (srepr (S.const s))
            pushHead $ S.eq (slen (S.const s')) sef
            pure (S.const s')
      t -> error $ "predEncode: field update of type " <> show (pretty t) <> " not supported"
  LS.PUnintFn "sum" [p] -> do
    let (p1, path) = Agg.sumPredToPath p
    s <- predEncode env p1
    getSort p1 >>= \case
      LS.SortMapping _ valSort ->
        (\sums -> (sums `unsafeLookup` path) s) <$> getMapSums valSort
      _ -> error $ "predEncode: sum on non-mapping: " <> show p
  LS.PUnintFn "nnz" [p] -> do
    s <- predEncode env p
    getSort p >>= \case
      LS.SortMapping _ valSort@LS.SortInt{} -> do
        nnz <- getMapNnz valSort
        case nnz of
          [snnz] -> pure (snnz s)
          _ -> error $ "predEncode: nnz on sort that isn't map(int)"
      _ -> error $ "predEncode: nnz on sort that isn't map(int)"
  LS.PUnintFn n es -> do
    delta <- gets esDelta
    zippedArgs' <- forM es $ \e -> do
      e' <- predEncode env e
      let sort = case getPredSort e (tcEnvToSortEnv env delta) of
            Just s -> s
            Nothing -> error $ "Cannot get sort of " <> show e
      aux <- getAuxExpr sort
      -- Invariant: sorts with aux variables are always encoded as symbolic variables
      se <- case e' of
        S.Atom s -> pure s
        _ -> do
          s <- mkFreshVar_ sort
          pushHead (S.eq (S.const s) e')
          pure s
      saux <- traverse (\(_, f) -> f se) aux
      sfn <- getUnintFunSorts sort
      pure (S.const se, saux, fst <$> sfn)
    let (args', auxArgs, ufArgs) = unzip3 zippedArgs'
    -- add unint function symbols
    pure $ S.fun (Text.unpack n) (args' <> mconcat auxArgs <> (S.const <$> mconcat ufArgs))
  LS.PHavoc ty -> do
    let sort = LS.skelToSort ty
    s <- mkFreshVar_ sort
    applySortProps sort s
    pure (S.const s)
  LS.PCast e ty -> do
    e' <- predEncode env e
    let havocValue toTy = do
          let toSort = LS.skelToSort toTy
          s <- mkFreshVar_ toSort
          applySortProps toSort s
          pure (S.const s)
    getSort e >>= \case
      t | LS.SortInt{} <- t, LS.TyAddress{} <- ty -> pure e'
      t | LS.SortInt{} <- t, LS.TyInt{} <- ty -> pure e'
      t | LS.SortInt{} <- t, LS.TyArray LS.TyByte _ <- ty -> havocValue ty
      t | LS.SortArray LS.SortByte _ <- t, LS.TyInt _ <- ty -> havocValue ty
      t | t == LS.skelToSort ty -> pure e'
      t -> error $ "predEncode: don't know how to cast " <> show t <> " to " <> show ty <> " in " <> show e
  where
    getSort p = flip fmap (gets esDelta) $ \delta ->
      case getPredSort p (tcEnvToSortEnv env delta) of
        Just s -> s
        Nothing -> error ("could not determine sort of " <> show p)
    {-
    collectAnd = \case
      LS.PAnd p q -> collectAnd p ++ collectAnd q
      p -> [p]
    -}

relEncode :: MonadIO m => LocalEnv p -> LS.Rel -> LS.Pred -> LS.Pred -> SmtEncodeT m S.SExpr
relEncode env rel e1 e2 = do
    e1' <- predEncode env e1
    e2' <- predEncode env e2
    sort <- getSort e1
    (_, mkAuxs) <- unzip <$> getAuxExpr sort

    let mkAuxPreds = do
          let (x1, x2) = case (e1', e2') of
                (S.Atom v1, S.Atom v2) -> (v1, v2)
                _ -> error $ show e1 <> " " <> show e2
          forM mkAuxs $ \f -> S.eq <$> f x1 <*> f x2

    auxPreds <- if null mkAuxs then pure [] else mkAuxPreds
    pure $ S.andMany (relOp rel e1' e2' : auxPreds)
  where
    relOp = \case
      LS.RelGt -> u256Gt
      LS.RelGte -> u256Geq
      LS.RelLt -> u256Lt
      LS.RelLte -> u256Leq
      LS.RelEq -> S.eq
      LS.RelNeq -> \p q -> S.not (S.eq p q)
    getSort p = flip fmap (gets esDelta) $ \delta ->
      case getPredSort p (tcEnvToSortEnv env delta) of
        Just s -> s
        Nothing -> error $ "could not find sort of " <> show p <> "\n" <> show delta <> "\n" <> show (LS.localEnvMap (const ()) env)


encBind
  :: MonadIO m
  => LocalEnv LS.Pred -- ^ environment
  -> LS.Pred -- ^ term to bind the refinement type variable to
  -> LS.RType LS.Pred -- ^ refinement type
  -> SmtEncodeT m (DList S.SExpr)
encBind env e (LS.RType v ty p) = do
  -- let tag = show (pretty x <> " ↦ " <> pretty liSkel) in
  pr <- DList.singleton <$> predEncode env (LS.predSubst v e p)
  prs <- case ty of
    LS.TyStruct _ flds -> do
      -- TODO: dependent scoping
      res <- forM flds $ \(f, t) -> encBind env (LS.PField e f) t
      pure (mconcat res)
    _ -> pure DList.empty
  pure (pr <> prs)

envEncode :: MonadIO m => LocalEnv LS.Pred -> SmtEncodeT m S.SExpr
envEncode env@(LS.LocalEnv vars preds) = do
  smtVars <- forM (Map.toList vars) $ \(x, t) -> do
    -- initialize sort properties
    -- liftIO $ putStrLn $ "init " <> show x
    _ <- getVar env x
    encBind env (LS.PVar x) t
  smtPreds <- traverse (predEncode env) preds
  pure (S.andMany (DList.toList (mconcat smtVars) <> smtPreds))

getAuxExpr :: MonadIO m => LS.Sort -> SmtEncodeT m [(S.SExpr, String -> SmtEncodeT m S.SExpr)]
getAuxExpr _ =  pure []

getUnintFunSorts :: MonadIO m => LS.Sort -> SmtEncodeT m [(String, S.SExpr)]
getUnintFunSorts = \case
  LS.SortMapping _ t2 -> do
    repr <- getMapRepr_ t2
    sums <- getMapSums_ t2
    nnz <- getMapNnz_ t2
    pure (repr : nnz <> Map.elems sums)
  LS.SortArray t _ -> do
    (len, repr) <- getArrayProps_ t
    pure [len, repr]
  LS.SortStruct n -> do
    flds <- gets ((`unsafeLookup` n) . LS.delta_structs . esDelta)
    concatMapM getUnintFunSorts [LS.rtypeToSort t | (_, t) <- flds]
  _ -> pure []
