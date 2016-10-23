{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DoAndIfThenElse #-}
module  AbsMachine (eval) where

import qualified Control.Arrow (second)
import           Control.Monad (unless,foldM)
import qualified CoreSyn
import           Data.List(foldl',find)
import           Data.Map (Map)
import qualified Data.Map.Strict as M
import           Data.Maybe (fromJust)
import           Debug.Trace
import           GhcPlugins hiding (Tick)
import           Literal (literalType)
import           System.Directory (canonicalizePath,doesFileExist)
import           TysWiredIn
import           Unique (mkUnique)
import           Utils

--------------------------------------------------------------------------------
-- Extended version of Core ----------------------------------------------------
--------------------------------------------------------------------------------
data ExtCore b =
    Core (Expr b)
  | Marker Id         -- only used in the stack
  | C (ExtCore b) (ExtCore b) | Nil
  | T (ExtCore b) (ExtCore b)
  | B Bool            -- support for Booleans
  | Tick (ExtCore b)  -- ticks for using in the algebra
  deriving (Outputable)

instance Show ExtCoreExpr where
  show = ppExtCore

-- | Unwrapping ExtCore
fromExtCore :: ExtCoreExpr -> CoreExpr
fromExtCore (Core e) = e
fromExtCore (Tick e) = fromExtCore e
fromExtCore (B b)    = if b then Var $ buildId "GHC.Types.True" 1 else Var $ buildId "GHC.Types.False" 2
fromExtCore (T a b) = tuple a b
fromExtCore (C x xs) = App (App (Var (buildId "GHC.Types.:" 5)) (fromExtCore x)) (fromExtCore xs)
fromExtCore Nil = Var (buildId "GHC.Types.[]" 4)
fromExtCore x   = error $ "Wrong Translation -- " ++ ppExtCore x


tuple a b = App (App (Var (buildId "GHC.Tuple.(,)" 3)) (fromExtCore a)) (fromExtCore b)


isExtCoreVal :: Heap -> ExtCoreExpr -> Bool
isExtCoreVal _ (B _)            = True
isExtCoreVal h (Core (Var x))   = (x == trueDataConId || x == falseDataConId) || (
  case M.lookup x h of
    Nothing  -> False
    _        -> True)
isExtCoreVal _ (C _ _)          = True
isExtCoreVal _ Nil              = True
isExtCoreVal _ (Core (Lam _ _)) = True
isExtCoreVal _ (T _ _)          = True
isExtCoreVal _ (Core Case {}) = True
isExtCoreVal _  _               = False


-- | Pretty print an ExtCore expression
ppExtCore (Core expr) = ppExp expr
ppExtCore (Marker i)  = "#" ++ pprCore i
ppExtCore (C x xs)    = ppExtCore x ++ " : " ++ ppExtCore xs
ppExtCore Nil         = "[]"
ppExtCore (B b)       = "B " ++ show b
ppExtCore (T a b)     = "(" ++ ppExtCore a ++ ", " ++ ppExtCore b ++ ")"
ppExtCore (Tick exp)  = "Tick (" ++ show exp ++ " )"

--------------------------------------------------------------------------------
-- The Configuration of the Abstract Machine -----------------------------------
--------------------------------------------------------------------------------
type ExtCoreExpr = ExtCore CoreBndr
type Heap = Map Id ExtCoreExpr
type Stack = [ExtCoreExpr]
type Count = Integer
type Config = (Heap, ExtCoreExpr , Stack, Count)

getCounts :: Config -> Count
getCounts (_,_,_,c) = c

--------------------------------------------------------------------------------
-- Operational Semantics -------------------------------------------------------
--------------------------------------------------------------------------------
isValue :: ExtCoreExpr -> Bool
isValue x = case x of
    Core (Lam _ _) -> True
    Core (Lit _)   -> True
    B _            -> True
    C _ _          -> True
    Nil            -> True
    T _ _          -> True
    _              -> False

isCoreValue :: CoreExpr -> Bool
isCoreValue x = case x of
    (Lam _ _) -> True
    (Lit _)   -> True
    _         -> False

-- one substitution
-- Changes all occurrences of x by y in the current expression
subst :: CoreExpr -> Id -> CoreExpr -> CoreExpr
subst y x t =
  case t of
    Var _x                    -> if x == _x then y else t -- base cases for substitution
    -- if the expr is a Type then check the substitute is also a Type and then
    -- check that it is of the correct "kind"
    Lam z _t                  -> Lam z $ subst y x _t
    App m arg                 -> App (subst y x m) (subst y x arg)
    Case exp b t alts         -> Case (subst y x exp) b t (map sub alts)
    Let  bds exp              -> Let (sublet bds) (subst y x exp)
    CoreSyn.Tick tickish exp  -> CoreSyn.Tick tickish (subst y x exp)
    _                         -> t
    where sub (alt, bs, exp) = (alt, bs, subst y x exp)
          sublet (NonRec b exp) = NonRec b (subst y x exp)
          sublet (Rec xs) = Rec $ map (\(b,e) -> (b,subst y x e)) xs

-- One step of the semantics
op_sem :: Config -> (Config -> IO Config) -> IO Config
-- Lookup
op_sem conf@(h, Core (Var x), s, c) sem =
    case M.lookup x h of
     Nothing -> do
       putStrLn $ print_msg "Lookup item in Prelude"
       !conf' <- prim_ops conf sem
       putStrLn (ppConfig conf')
       return conf'
     Just m -> do
       putStrLn $ "Updating " ++ ppExtCore m
       putStrLn $ print_msg "Lookup item in Heap"
       putStrLn "***** Evaluation inside Lookup Start *****" -- evaluate m and then push marker onto stack
       putStrLn (ppConfig (h, m, s, c))
       (h'',m',s', c') <- sem (h, m, s, c)
       putStrLn "***** Evaluation inside Lookup End *****"
       let mx = if '.' `elem` pprCore x
                then Marker $  buildId (pprCore x ++ "_result") 6
                else Marker x
       let conf' = (h'', m', mx:s', c' + 1)                      -- increment count
       putStrLn (ppConfig conf')
       return conf'

-- Update
op_sem conf@(h, v, Marker x :s, c) _ = do
  putStrLn $ print_msg "Update"
  if isValue v
    then do
      let conf' = (M.insert x v h, v, s, c + 1)                        -- increment count
      putStr (ppConfig conf')
      return conf'
    else sem_error "cant apply update on a non-value term" conf

-- Unwind
op_sem (h, Core (App m x), s, c) _ = do
  putStrLn $ print_msg "Unwind"
  let conf = (h, Core m, Core x:s, c + 1)                            -- increment count
  putStr (ppConfig conf)
  return conf

-- Subst
op_sem cf@(h, Core (Lam x m), Core y:s, c) _ = do
  -- putStrLn $ print_msg "Subst"
  -- putStrLn $ show "Substituting " ++ pprCore y ++ "for " ++ pprCore x ++ "in " ++ pprCore m
  let conf = (h, Core (subst y x m), s, c + 1)                       -- increment count
  putStr (ppConfig conf)
  return conf


-- Case (remember case in Core is Strict)
-- Case (Expr b) b Type [Alt b]
-- type Alt b = (AltCon, [b], Expr b)
-- AltCon is DEFAULT, DataAlt, LitAlt
-- TODO: Handle LitAlts and DEFAULT
op_sem (h, Core (Case cexp bind t alts), s, c) sem = do
  let cf = (h, Core cexp, s, c) -- eval case exp
  putStrLn "Evaluating CASE EXPRESSION START"
  cnf@(h', cexp', s', c') <- sem cf
  putStrLn "CASE EXPR Evaluated"
  putStrLn $ ppConfig cnf
  let branch =
        case cexp' of
          -- FIXME: laziness
            (T a b) ->
              let (d',vars,alt) = head $
                    filter (\(DataAlt d,_,_) -> isTupleDataCon d) alts
              in  subst (fromExtCore a) (head vars)
                    (subst (fromExtCore b) (last vars) alt)
            Nil  ->
              let (d',vars,alt) = head $
                    filter (\(DataAlt d,_,_) -> nilDataCon == d) alts
              in alt
            (C x xs) ->
              let (d',vars,alt) = head $
                    filter (\(DataAlt d,_,_) -> consDataCon == d) alts
              in subst (fromExtCore x) (head vars) (subst (fromExtCore xs) (last vars) alt)
            (Core x) ->
              let (d',vars,alt) = head $
                    filter (\(DataAlt d,_,_) -> consDataCon == d) alts
              in subst x (head vars) (subst (fromExtCore Nil) (last vars) alt)
            _ ->
              let alts' = map (\(alt,b,exp) -> (altConToBool alt, b, exp)) alts
              in  select_branch cexp' alts'
  putStrLn "SELECTED BRANCH"
  let ret = (h', Core branch, s', c' + 2)
  putStrLn $ ppConfig ret
  return ret
  where
    select_branch :: ExtCoreExpr -> [(Bool, [Var], CoreExpr)] -> CoreExpr
    select_branch (B b) alts = (\(_,_,exp) -> exp) . fromJust $ find (\(a,_,_) -> a == b) alts
    select_branch _ [alt] = (\(_,_,exp) -> exp) alt
    select_branch exp alts = error $ "Can't select alts that are not boolean" ++ ppExtCore exp

    altConToBool :: AltCon -> Bool
    altConToBool (DataAlt d)
      | trueDataCon  == d = True
      | falseDataCon == d = False
      | otherwise         = error "Not an altCon that we can process"
    altConToBool _ = error "Not an AltCon that we can process"


-- Letrec
-- Lets are the only ones that can allocate things in the heap
op_sem (h, Core (Let defs m), s, c) _ = do
  putStrLn $ print_msg "Let"
  case defs of
    (NonRec def exp) -> do
      let conf = (M.insert def (Core exp) h, Core m, s, c + 1)       -- increment count
      putStr (ppConfig conf)
      return conf
    (Rec defs')      -> do
      mapM_ (putStrLn . (\(id,exp) -> pprCore id ++ " " ++ ppExp exp)) defs'
      -- FIXME: Lazy evaluation is hitting me here I think. It doesn't load all
      -- the bindings to the heap only the ones needed!
      let h' = foldr (\(x,n) he -> M.insert x (Core n) he) h defs'
          conf = (h', Core m, s, c + 1)                              -- increment count
      putStr (ppConfig conf)
      return conf

-- Tick
-- There two kinds of Ticks the internal Ticks of a CoreExpr and the Ticks of a
-- ExtCoreExpr
-- This is because I can't nest the ExtCoreExpr Ticks inside a CoreExpr so we
-- just use the Ticks defined there.
-- These two functions simply take care of removing the ticks and icrementing
-- the tick counts by 1
op_sem (h, Core (CoreSyn.Tick tickish exp), s, c) _ =  do
  putStrLn $ print_msg "CoreSyn Tick"
  let conf = (h, Core exp, s, c + 1)
  putStr (ppConfig conf)
  return conf

op_sem (h, Tick exp, s, c) _ = do
  putStrLn $ print_msg "Tick"
  let conf = (h, exp, s, c + 1)
  putStr (ppConfig conf)
  return conf

-- Error if not any of the above
op_sem conf _ = sem_error "Don't know how to interpret this" conf


--------------------------------------------------------------------------------
-- Running the interpreter -----------------------------------------------------
--------------------------------------------------------------------------------
-- | Init config works by loading all top level bindings from the Core Program
-- into the heap and loading the last binder as the current expression
-- This means that interpretation always starts with a "lookup". This is so that
-- when the expression gets evaluated we can save the result in the heap
init_conf :: CoreProgram -> Config
init_conf binds = (init_h, Core $ Var m, [], 0)
  where unwrapped = concatMap unwrapBinds binds
        init_h = M.fromList unwrapped
        m = fst $ last unwrapped -- load the first expression

-- TODO: REFACTOR semantics and semantics' code duplication is BAD
semantics :: Config -> IO Config
semantics conf@(h, m, s, c)
  | isValue m && null s = return conf                                             -- finish only when value and stack empty
  | not (isExtCoreVal h m) && exprIsBottom (fromExtCore m) =
      error $ "Expr " ++ ppExtCore m  ++ " is BOTTOM"
  | otherwise = do
        putStrLn "Continue interpretation? (y/n)"
        yn <- getLine
        case yn of
          "y" -> semantics =<< op_sem conf semantics
          _   -> return conf

semantics' :: Config -> IO Config
semantics' conf@(h, m, s, c)
  | isValue m && null s = return conf  -- finish only when value and stack empty
  | not (isExtCoreVal h m) && exprIsBottom (fromExtCore m) =
      error $ "Expr " ++ ppExtCore m  ++ " is BOTTOM"
  | otherwise =  semantics' =<< op_sem conf semantics'

-- | Main entry point. Interprets the whole program
eval :: CoreProgram -> IO ()
eval exp = do
  let conf = init_conf exp                                           -- load the program onto the heap
  putStrLn $ print_msg "Initial Conf"
  putStrLn (ppConfig conf)
  putStrLn "Interactive mode? (y/n)"
  mode <- getLine
  case mode of
    "y" -> eval' conf semantics -- non interactive interpretation
    _   -> eval' conf semantics' -- interactive interpretation

-- | Evaluation loop for interactivity
-- We can select which expression to evaluate at any time
eval' :: Config -> (Config -> IO Config) -> IO ()
eval' conf@(h, _, s, c) sem = do
  let keys = M.fromList . zip [1..] $ M.keys h  -- add options to select key
  putStrLn "Select which expr you want to interpret: "
  mapM_ (putStrLn . \(x,e) -> show x ++ ": " ++ pprCore e) (M.toList keys)
  opt <- getLine                                -- FIXME: error if a non int char is entered
  case M.lookup (read opt) keys of
    Just v -> do
      let cfg = (h, Core $ Var v, s, c)
      putStrLn "Interpreting: "
      let exp = fromJust $ M.lookup v h
      putStrLn (ppExtCore exp)
      conf'@(h', m', s', _) <- sem cfg          -- start interpretation
      putStrLn $ "===== Ending conf: \n" ++ ppConfig conf'
      putStrLn "To quit press q"
      quit <- getLine
      case quit of
        "q" -> return ()
        _   -> eval' (h', m', s', 0) sem
    Nothing -> do
      putStrLn "Wrong option."
      eval' conf sem

--------------------------------------------------------------------------------
-- Core Prelude ----------------------------------------------------------------
--------------------------------------------------------------------------------
prim_ops :: Config -> (Config -> IO Config) -> IO Config
prim_ops conf@(h, Core (Var m), s, c) sem =
    case pprCore m of
      "GHC.Types.True"   -> return (h, B True, s, c)
      "GHC.Types.False"  -> return (h, B False, s, c)
      "GHC.Num.fromInteger" ->
        do
          let s' = dropWhile (\x -> not (isExtCoreVal h x) && not ((isLitorApp . fromExtCore) x)) s
          return (h, head s', safeTail s', c)
      "GHC.Num.+"        -> apply_add conf sem  add
      "GHC.Num.-"        -> apply_add conf sem sub
      "GHC.Real./"       -> apply_add conf sem div
      "GHC.Num.*"        -> apply_add conf sem mult
      "GHC.Classes.=="   -> apply_add conf sem eq
      "GHC.Classes.>"   -> apply_add conf sem gt
      "GHC.Classes.>="  -> apply_add conf sem gte
      "GHC.Classes.<"   -> apply_add conf sem lt
      "GHC.Classes.<="  -> apply_add conf sem lte
      "GHC.Types.D#"    -> return (h, head s, safeTail s, c)
      "GHC.Types.:"     -> apply_add conf sem cons
      "GHC.Types.[]"    -> return (h, Nil, safeTail s, c)
      "GHC.Tuple.(,)"   -> apply_prim conf sem _tuple
      _                 -> sem_error (pprCore m ++ " is not a prim op") conf
     where
        _tuple          = T
        cons     e1 Nil = e1
        cons     Nil _  = error "Consing a list to something"
        cons     e1 e2  = C e1 e2
        add     ( Core (Lit (LitInteger x tx ) )) (Core (Lit (LitInteger y ty))) = Core . Lit $ mkLitInteger (x+y) tx
        add     ( Core (Lit (MachDouble a))) (Core (Lit (MachDouble b)))         = Core . Lit $ mkMachDouble (a + b)
        add     ( Core (Lit (MachFloat a))) (Core (Lit (MachFloat b)))           = Core . Lit $ mkMachFloat (a + b)
        sub     ( Core (Lit (LitInteger x tx ) )) (Core (Lit (LitInteger y ty))) = Core . Lit $ mkLitInteger (x-y) tx
        sub     ( Core (Lit (MachDouble a))) (Core (Lit (MachDouble b)))         = Core . Lit $ mkMachDouble (a - b)
        sub     ( Core (Lit (MachFloat a))) (Core (Lit (MachFloat b)))           = Core . Lit $ mkMachFloat (a - b)
        mult    ( Core (Lit (LitInteger x tx ) )) (Core (Lit (LitInteger y ty))) = Core . Lit $ mkLitInteger (x*y) tx
        mult    ( Core (Lit (MachDouble a))) (Core (Lit (MachDouble b)))         = Core . Lit $ mkMachDouble (a * b)
        mult    ( Core (Lit (MachFloat a))) (Core (Lit (MachFloat b)))           = Core . Lit $ mkMachFloat (a * b)
        div     ( Core (Lit (MachDouble a))) (Core (Lit (MachDouble b)))         = Core . Lit $ mkMachDouble (a / b)
        div     ( Core (Lit (MachFloat a))) (Core (Lit (MachFloat b)))           = Core . Lit $ mkMachFloat (a / b)
        gt      ( Core (Lit (LitInteger x _  ) )) (Core (Lit (LitInteger y _)))  = B $ x > y
        gt      ( Core (Lit (MachDouble a))) (Core (Lit (MachDouble b)))         = B (a > b)
        gt      ( Core (Lit (MachFloat a))) (Core (Lit (MachFloat b)))           = B (a > b)
        gte     ( Core (Lit (LitInteger x _  ) )) (Core (Lit (LitInteger y _)))  = B $ x >= y
        gte     ( Core (Lit (MachDouble a))) (Core (Lit (MachDouble b)))         = B (a >= b)
        gte     ( Core (Lit (MachFloat a))) (Core (Lit (MachFloat b)))           = B (a >= b)
        lt      ( Core (Lit (LitInteger x _  ) )) (Core (Lit (LitInteger y _)))  = B $ x < y
        lt      ( Core (Lit (MachDouble a))) (Core (Lit (MachDouble b)))         = B (a < b)
        lt      ( Core (Lit (MachFloat a))) (Core (Lit (MachFloat b)))           = B (a < b)
        lte     ( Core (Lit (LitInteger x _  ) )) (Core (Lit (LitInteger y _)))  = B $ x <= y
        lte     ( Core (Lit (MachDouble a))) (Core (Lit (MachDouble b)))         = B (a <= b)
        lte     ( Core (Lit (MachFloat a))) (Core (Lit (MachFloat b)))           = B (a <= b)
        eq      ( Core (Lit (LitInteger x _  ) )) (Core (Lit (LitInteger y _)))  = B $ x == y
        eq      ( Core (Lit (MachDouble a))) (Core (Lit (MachDouble b)))         = B (a == b)
        eq      ( Core (Lit (MachFloat a))) (Core (Lit (MachFloat b)))           = B (a == b)

apply_add (h, exp, s, c) sem add = do
    let s' = dropWhile (\x -> not (isExtCoreVal h x) && not ((isLitorApp . fromExtCore) x)) s
    (h', arg1, _, c') <- prepareArg sem (h, head s', [], 0)
    let s'' = safeTail s'
    (h'', arg2, _, c'')  <- prepareArg sem (h', head s'', [], 0)
    let s''' = safeTail s''
    return (h'', add arg1 arg2, s''', c + c' + c'')

-- | Collect the needed arguments from the stack
-- Pass True if you need two arguments, False if you need only one
get_args conf@(h, exp, s', c) b sem = do
    putStrLn "Preparing Arguments"
    putStrLn (ppConfig (h, exp, s', c))
    let s'' = safeTail s'
    if b then (do
      let s''' = safeTail s''
      putStrLn "Applying correct prelude operation"
      let conf' = (h, exp,  s''', c)
      putStrLn $ ppConfig conf'
      return $ Left (conf', head s', head s''))
    else (do
      let conf' = (h, exp, s'', c)
      putStrLn $ ppConfig conf'
      return $ Right (conf', head s'))

apply_prim :: Config -> (Config -> IO Config) -> (ExtCoreExpr -> ExtCoreExpr -> ExtCoreExpr) -> IO Config
apply_prim (h, Core (Var m), s, c) sem op = do
  let s' = dropWhile (\x -> not (isExtCoreVal h x) && not ((isLitorApp . fromExtCore) x)) s
  if null s'
  then
    if m == falseDataConId
    then return (h, B False, s, c)
    else if m == trueDataConId
         then return (h, B True, s, c)
         else sem_error (pprCore m ++ " is not a prim op") (h, Core (Var m), s, c)
  else do
    let conf' = (h, Core (Var m), s', c)
    args <- get_args conf' True sem
    case args of
      Left ((h,exp, s''',c''), arg1, arg2) -> do
        let cff = (h, op arg1 arg2, s''', c'')
        putStrLn $ ppConfig cff
        return cff
      _ -> error "Not enough arguments to apply"

-- | Evaluates arguments all the way down to literals to be used by the
-- primitive operations
-- This is a bit hacky but Core handles only Literals as primitive types
-- Defined here:
-- http://downloads.haskell.org/~ghc/7.10.3/docs/html/libraries/ghc-7.10.3/Literal.html#t:Literal
prepareArg :: (Config -> IO Config) ->  Config -> IO Config
prepareArg sem (h, Core (Lit l), s, c)        = return (h, Core (Lit l), s, c)
prepareArg sem conf@(_, Core (App _ _), _, _) = prepareArg sem =<< sem conf
prepareArg sem conf@(_, Core (Var _), _, _)   = prepareArg sem =<< sem conf
prepareArg sem conf@(_, Core Case{}, _, _)   = prepareArg sem =<< sem conf
prepareArg sem (h, B b, s, c)                 = return (h, B b, s, c)
prepareArg sem (h, Core (Lam b exp), s, c)    = return (h, Core (Lam b exp),s, c)
prepareArg sem (h, T a b, s, c)               = return (h, T a b, s, c)
prepareArg sem (h, C a b, s, c)               = return (h, C a b, s, c)
prepareArg sem (h, Nil, s, c)               = return (h, Nil, s, c)
prepareArg _ conf@(_,_,_,_)                   = sem_error "Can't prepareArg" conf

--------------------------------------------------------------------------------
-- Utils -----------------------------------------------------------------------
--------------------------------------------------------------------------------
-- | Pretty printing configurations
ppConfig :: Config -> String
ppConfig (h, m, s, c) =
  "Heap -----> " ++ heap ++
  "Current expr -----> " ++ show m ++ "\n" ++
  "Stack -----> " ++ stack ++ "\n" ++
  "Ticks -----> " ++ show c ++ "\n"
    where
      heap = if M.null h
             then "[]\n"
             else concatMap (\x -> indent ++ pprCore x) (M.keys h) ++ "\n"
      indent = "    "
      stack = if null s
              then "[]\n"
              else "\n" ++ concatMap (\x -> indent ++ show x ++ " \n") s


-- | More informative error for the semantics
sem_error msg conf = error $ msg ++  "\n Last conf was \n" ++ ppConfig conf

-- | Pretty prints a message
-- This function is used inside the op_sem to print out which rule are we
-- applying
print_msg msg = "====== " ++ msg ++ " ======"

-- | Get the binders and CorExprs from a CoreBind
unwrapBinds :: CoreBind -> [(CoreBndr,ExtCoreExpr)]
unwrapBinds (NonRec b exp) = [(b,Core exp)]
unwrapBinds (Rec exps) = map (Control.Arrow.second Core) exps

-- | Check if CoreExpr is an App or a Literal
-- Used in prelude
isLitorApp :: CoreExpr -> Bool
isLitorApp l =
  case l of
    (Lit _)    -> True
    (App _ _)  -> True
    _          -> False

safeTail :: [a] -> [a]
safeTail [] = []
safeTail (_:xs) = xs

-- | Builds an Id with varName
buildId varName uniq = mkGlobalVar VanillaId name typ vanillaIdInfo
  where
    name           = mkInternalName dunique (varOccName varName) noSrcSpan
    dunique        = mkUnique '_' uniq
    varOccName     = mkVarOcc
    typ            = mkTyVarTy tyvar
    tyvar          = mkTyVar name anyKind

buildId' varName = mkGlobalVar VanillaId name typ vanillaIdInfo
  where
    name           = mkInternalName dunique (varOccName varName) noSrcSpan
    dunique        = mkUnique '_' 0
    varOccName     = mkVarOcc
    typ            = mkTyVarTy tyvar
    tyvar          = mkTyVar name anyKind

-- | Builds a CoreSyn Tickish
buildTickish tickName = SourceNote { sourceSpan = srcSpan, sourceName = tickName }
  where
    srcSpan = mkRealSrcSpan srcLoc srcLoc
    srcLoc  = mkRealSrcLoc (mkFastString tickName) 0 1

-- | Builds a Type with the given typeName
buildType typeName = mkTyVarTy tyvar
  where tyvar          = mkTyVar name anyKind
        name           = mkInternalName dunique (varOccName typeName) noSrcSpan
        varOccName     = mkVarOcc
        dunique        = mkUnique '_' 0

buildCoreTick :: String -> CoreExpr -> CoreExpr
buildCoreTick tickName = CoreSyn.Tick (buildTickish tickName)

empty_conf :: ExtCoreExpr -> Config
empty_conf exp = (M.empty, exp, [], 0)
