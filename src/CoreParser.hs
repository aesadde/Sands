{-# LANGUAGE OverloadedStrings #-}

module  CoreParser where

import           CoreSyn
import           CoreUtils (exprType)
import qualified Data.Map.Strict as M (fromList,toList,empty,insert)
import           Data.Text (Text)
import qualified Data.Text as T
import           DynFlags
import           HscMain
import           Outputable
import           PprCore
import           TidyPgm
import           Var
import           Name hiding (varName,getName)
import qualified Data.HashSet as S
import qualified Data.Set as Set (empty)
import qualified CabalParser as C
import qualified GHC
import           GHC.Paths (libdir)
import           Control.Monad
import           HscTypes
import           Digraph (flattenSCCs)
import           Utils
import           Types
import           Language.Haskell.Extension (Extension)
import           MonadUtils
import           System.Directory
import           System.FilePath
import           Data.List ((\\),nub,find)
import           DataCon (dataConWorkId)
import           TyCon
import           Visitor
import           Data.Foldable (foldl')
import           Packages (initPackages)
import           System.IO.Temp (withSystemTempDirectory)
import           Control.Exception

--------------------------------------------------------------------------------
-- Parser entry point ----------------------------------------------------------
--------------------------------------------------------------------------------
-- | looks for a cabal file in the given filepath.
--   If found, parses it and tries to compile to Core all files in the package
parsePkg :: FilePath -> IO Package
parsePkg dir = do
  pkg <- C.parseCabalFile dir
  let files = map (\x -> dir ++ "/" ++ x) (packageFiles pkg)
  files' <- mapM resolvePath files
  modules <- mapM (getFull pkg) files'
  return $ pkg { modules = modules }


-- | Adds the .hs extension if the file actually exsists and makes the path
-- full.
-- TODO: Add error handling
resolvePath :: FilePath -> IO FilePath
resolvePath fp = do
  let hs = fp `addExtension` "hs"
  canonicalizePath hs

-- | Attempts to compile to Core a single module not in a package
compileSingleModule :: FilePath ->  IO ModuleInfo
compileSingleModule fpath = getFull pkg fpath
  where pkg = Package
          {
            packageName = "Empty"
          , packageVersion = "0.0"
          , packageDependencies = Set.empty
          , packageFiles = [fpath]
          , includeDirs = []
          , packageExtensions = []
          , modules = []
          }

--------------------------------------------------------------------------------
-- GHC Interface ---------------------------------------------------------------
--------------------------------------------------------------------------------
-- Pretty much copying what LiquidH does

-- | Given a path to a file (module) this function runs the GHC engine and
-- extract the 'ModGuts' from the file.
compileToCore :: FilePath -> Package -> IO ModGuts
compileToCore target pkg = runEngingeGhc pkg $ getGhcInfo target

-- | Set up the GHC environment
runEngingeGhc :: Package -> GHC.Ghc a -> IO a
runEngingeGhc pkg act =
  GHC.defaultErrorHandler defaultFatalMessager defaultFlushOut .
    withSystemTempDirectory "engine" $ \tmp ->
    GHC.runGhc (Just libdir) $ do
      df <- GHC.getSessionDynFlags
      let df' = df { importPaths  = nub $ includeDirs pkg ++ importPaths df
                   , libraryPaths = nub $ includeDirs pkg ++ libraryPaths df
                   , includePaths = nub $ includeDirs pkg ++ includePaths df
                   , packageFlags = [ ExposePackage (PackageArg "ghc-prim")
                                                    (ModRenaming True [])
                                    , ExposePackage (PackageArg "ghc-paths")
                                                    (ModRenaming True [])]
                                    ++ packageFlags df
                   , ghcLink      = LinkInMemory
                   -- , hscTarget    = HscInterpreted -- HscNothing
                   , ghcMode      = CompManager
                   , objectDir    = Just tmp
                   , hiDir        = Just tmp
                   , stubDir      = Just tmp
                     }
      -- Turn on all extensions
      let df'' = foldr  (\ext fs ->  fs `xopt_set` ext) df' glasgowExtsFlags
      _ <- GHC.setSessionDynFlags df'
      act


-- | Load the current targets and invoke the compilation
-- NOTE: Panic happens inside this function. Added a wrapper around the loading.
-- Seems to avoid quitting on the "non-exposed" modules error but there are
-- plenty of new errors!
getGhcInfo :: FilePath -> GHC.Ghc ModGuts
getGhcInfo target = do
  tgt <- GHC.guessTarget target Nothing
  GHC.addTarget tgt
  -- attempt at handling errors with the compilation. This still fails but less
  -- badly than before
  loading <- handleSourceError (\_ -> return GHC.Failed) (GHC.load GHC.LoadAllTargets)
  case loading of
    GHC.Failed -> return $ error "Can't load targets"
    GHC.Succeeded -> makeModGuts target


-- get the dependencies
allDepNames :: [ModSummary] -> [String] -- from LiquidH
allDepNames = concatMap (map declNameString . ms_textual_imps)

declNameString :: GHC.Located (GHC.ImportDecl GHC.RdrName) -> String -- from LiquidH
declNameString = GHC.moduleNameString . GHC.unLoc . GHC.ideclName . GHC.unLoc

-- | Get the core of the module via ModGuts
makeModGuts :: FilePath -> GHC.Ghc ModGuts
makeModGuts f = do
  modGraph <- GHC.getModuleGraph
  case find (\m -> not (isBootSummary m) && f == msHsFilePath m) modGraph of
    Just modSummary -> do
      parsed   <- GHC.parseModule modSummary
      d <- GHC.desugarModule =<< GHC.typecheckModule parsed
      l <- GHC.loadModule d -- Doesn't seem to affect anything (from Haskell wiki)
      return $! GHC.coreModule d
    Nothing ->
      panic "Ghc Interface: Unable to get GhcModGuts"

--------------------------------------------------------------------------------
-- Core Parsing ----------------------------------------------------------------
--------------------------------------------------------------------------------
-- | A Custom conversion from TyCons to simple type constructors
getTyCon :: TyCon -> DataType
getTyCon ty
  | isAlgTyCon ty && isDataTyCon ty  = Data
  | isAlgTyCon ty                    = NewType
  | isClassTyCon ty                  = ClassInst
  | isTypeSynonymTyCon ty            = Synonym
  | otherwise                        = OtherData

-- | Retrieves data constructors from the compiled module and converts them to
-- our format
getTyCons :: ModGuts -> [([Text],DataType)]
getTyCons modguts = map (\x -> (map prettyPrint (tyConDataCons x), getTyCon x)) (mg_tcs modguts)

-- FIXME: Should not depend on Package!
getFull ::  Package -> FilePath -> IO ModuleInfo
getFull pkg fpath = do
  modguts <- compileToCore fpath pkg
  print $ "Compiling " ++ fpath
  let coreProgram = mg_binds modguts
      dataCons    = getTyCons modguts
      modName     = (T.pack . GHC.moduleNameString) . GHC.moduleName $ mg_module modguts
      dataCons'   = concatMap (map dataConWorkId . tyConDataCons) (mg_tcs modguts)
      impVs       = importVars coreProgram
      defVs       = definedVars coreProgram
      useVs       = readVars coreProgram
      letVs       = letVars coreProgram

  return ModuleInfo {
                      moduleName = modName --
                    , imports    = map prettyPrint impVs --
                    -- , functions  = foldl' (\m f@(n,_,_) -> M.insert (prettyPrint n) (mkFun f) m) M.empty defVs
                    , functions  = map (mkFun (packageName pkg) modName) defVs
                    , dataDefs   = dataCons
                    -- , contents   = map (\(b,e) -> (prettyPrint b, prettyPrint e)) coreProgram --
                    , contents = []
                    }

mkFun ::Outputable a => Text -> Text -> (a, GHC.Type, CoreExpr) -> CoreFunc
mkFun pkgN modN (name,typ,expr) = CoreFunc
  {
    funName       = prettyPrint name
  , funType       = prettyPrint typ
  , funDef        = prettyPrint expr
  , calls         = map prettyPrint (readVars expr \\ letVars expr)
  , internalCalls = 0
  , externalCalls = 0
  , calledBy = []
  , modN          =  modN
  , packageN      = pkgN
  }

-- | Given two functions this function checks if the first one is called by the
-- other one and updates the fields accordingly
funCalled :: (Text, CoreFunc) -> (Text,CoreFunc) -> (Text,CoreFunc)
funCalled (n,fun) (_,caller) =
  if notElem caller (calledBy fun) && (n `elem` calls caller)
  then
    if modN fun == modN caller
    then (n, fun {internalCalls = internalCalls fun + 1, calledBy = caller : calledBy fun})
    else (n,fun {externalCalls = externalCalls fun  + 1, calledBy = caller : calledBy fun})
  else (n,fun)

-- | Checks if a function is called by a list of functions
funsCalled :: Foldable t => (Text,CoreFunc) -> t (Text,CoreFunc) -> (Text,CoreFunc)
funsCalled = foldl' funCalled

importVars :: CoreProgram -> [Id]
importVars = freeVars S.empty

definedVars :: CoreProgram -> [(CoreBndr, GHC.Type, CoreExpr)]
definedVars = concatMap defs
  where
    defs (NonRec b e) = [(b, exprType e, e)]
    defs (Rec xes)    = map (\(b,e) -> (b, exprType e, e)) xes
