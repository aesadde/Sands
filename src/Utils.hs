module Utils where

import           Data.Text (Text)
import qualified Data.Text as T
import           Outputable
import           DynFlags (unsafeGlobalDynFlags)
import System.Directory
import Control.Exception
import CoreSyn
import Literal

--------------------------------------------------------------------------------
-- Misc ------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- | Executes an IO action in the given directory and reverts back to original
--   dir after the action finishes
withCurDir :: FilePath -> IO a -> IO a
withCurDir dir act =
    bracket getCurrentDirectory setCurrentDirectory . const $ do
        setCurrentDirectory dir; act

--------------------------------------------------------------------------------
-- Pretty Printing expressions -------------------------------------------------
--------------------------------------------------------------------------------
-- | Pretty prints a CoreBind specifying if it is Rec or NonRec
ppBind :: CoreBind -> String
ppBind (NonRec b exp) = "{NonRec " ++ pprCore b ++ " = " ++ ppExp exp ++ "}"
ppBind (Rec xes)      = "{Rec " ++ concatMap ppRec xes ++ "}"
 where
   ppRec (b,exp) = "(" ++ pprCore b ++ " = " ++ ppExp exp ++ ")"


-- | Pretty prints a Core Expr specifying the "type"
ppExp :: CoreExpr -> String
ppExp expr = case expr of
  Var x        -> "(Var " ++ pprCore x ++ ")"
  Lit i        -> "(Literal" ++ pprCore i ++ ")"
  App exp arg  -> "(App " ++ ppExp exp ++ ppExp arg ++ ")"
  Lam b exp    -> "(Lam "  ++ pprCore b ++ " ->\n" ++ ppExp exp ++ ")"
  Let b exp    -> "(Let " ++ ppBind b ++ " in \n" ++ ppExp exp ++ ")"
  Case exp b t alts      -> "(Case " ++ pprCore b ++ " = " ++ ppExp exp ++ " of ->\n" ++ (concatMap ppAlt alts) ++ ")"
  Cast _ _     -> "Cast"
  Tick _ exp   -> "(Tick " ++ ppExp exp ++ ")"
  Type  t      -> "(Type " ++ pprCore t ++ ")"
  Coercion _   -> "Coercion"

-- type Alt b = (AltCon, [b], Expr b)
ppAlt (a, bs, exp) = ppAltCon a ++ " -> \n" ++ concatMap (\x -> " " ++ pprCore x ++ ", ") bs ++ ", " ++ ppExp exp ++ " )\n"

ppAltCon alt = case alt of
  DataAlt d  ->  " DataAlt " ++ pprCore d
  LitAlt l   ->  "LitAlt " ++ pprCore l
  DEFAULT    ->  "Default "

-- | Render Core names to String
-- use reallyAlwaysQualify instead of alwaysQualify to get also information
-- about the package in which the names are defined!
pprCore :: Outputable a => a -> String
pprCore ex = renderWithStyle unsafeGlobalDynFlags (ppr ex) style

style :: PprStyle
style = mkUserStyle alwaysQualify AllTheWay

-- | Prints to Text any Outputable object. Used for debugging.
prettyPrint :: Outputable a => a -> Text
prettyPrint ex = T.pack $ renderWithStyle unsafeGlobalDynFlags (ppr ex) style


whichLit (Lit lit) =
  case lit of
   MachChar _  -> "MachChar"
   MachStr  _  -> "MachStr"
   MachNullAddr -> "NullPtr"
   MachInt     _ -> "MachInt"
   MachInt64   _ -> "MachInt64"
   MachWord    _ -> "MachWord"
   MachWord64  _ -> "MachWord64"
   MachFloat   _ -> "MachFloat"
   MachDouble  _ -> "MachDouble"
   MachLabel   _ _ _ -> "MachLabel"
   LitInteger _ _ -> "LitInteger"
