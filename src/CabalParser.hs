{-# LANGUAGE OverloadedStrings #-}
module CabalParser  where

import           Data.Foldable (maximumBy)
import           Data.List (sortBy)
import qualified Data.Map.Strict as M (filterWithKey,keys,fromList,insertWith,findMax,toList,(!))
import           Data.Map.Strict(Map)
import           Data.Ord (comparing)
import           Data.Set (Set)
import qualified Data.Set as S (fromList,foldl')
import qualified Data.Text as T (pack,append)
import           Data.Text(Text)
import           Data.Maybe (fromMaybe)
import           GHC.Exts (Down(..))
import           Scraper (buildFilePathWCabal)
import           System.Directory
import           System.FilePath
import           System.IO

-- Taking advantage of Stack
import qualified Stack.Package as S
import qualified Stack.Types.Version as S
import qualified Stack.Types.PackageName as S (PackageName,fromCabalPackageName,packageNameText)

-- Interface to Cabal.
import           Distribution.ModuleName(toFilePath)
import qualified Distribution.Package as Cabal
import           Distribution.Package hiding (Package, PackageName, packageName, packageVersion)
import qualified Distribution.PackageDescription as Cabal
import           Distribution.PackageDescription (GenericPackageDescription, PackageDescription(..), BuildInfo)
import           Distribution.PackageDescription.Configuration (flattenPackageDescription)
import           Distribution.PackageDescription.Parse(readPackageDescription)
import           Distribution.Verbosity(silent)
import           Distribution.Simple.Utils (tryFindPackageDesc)
import           Language.Haskell.Extension (Extension)
import           Types (Package(..))


-- | Looks for a cabal file in the given dir and if found parses it.
parseCabalFile :: FilePath -> IO Package
parseCabalFile dir = tryFindPackageDesc dir >>= fmap (findPieces dir) . readPackageDescription silent

parseCabalFile' :: FilePath -> FilePath -> IO Package
parseCabalFile' dir fpath = fmap (findPieces dir) (readPackageDescription silent fpath)

isLibrary :: PackageDescription -> Bool
isLibrary pkg = case library pkg of
  Just _ -> True
  Nothing -> False

-- | Gather the informative bits from the package description
findPieces:: FilePath -> GenericPackageDescription -> Package
findPieces dir gpkg = Package
  { packageName         = T.pack $ show name
  , packageVersion      = T.pack $ show (getPackageVersion pkg)
  , packageDependencies = getPackageDeps pkg name
  , packageFiles        = getAllFiles pkg
  , includeDirs         = getIncludeDirs dir pkg
  , packageExtensions   = map (T.pack . show) (getExtensions pkg)
  , modules             = []
  }
    where pkg = flattenPackageDescription gpkg
          name = getPackageName pkg

getBuildInfo :: PackageDescription -> BuildInfo
getBuildInfo pkg = case library pkg of
                     Just p -> Cabal.libBuildInfo p
                    -- shouldn't be a problem to use head here since it should
                    -- always be an exe if no library
                     Nothing -> Cabal.buildInfo (head $ Cabal.executables pkg)

getIncludeDirs :: FilePath -> PackageDescription -> [FilePath]
getIncludeDirs dir pkg = map (\x -> dir </> x) $ Cabal.includeDirs (getBuildInfo pkg)

getExtensions :: PackageDescription -> [Extension]
getExtensions pkg = Cabal.defaultExtensions bi ++ Cabal.otherExtensions bi
  where bi = getBuildInfo pkg


-- | Get the name of a package
getPackageName :: PackageDescription -> S.PackageName
getPackageName = S.fromCabalPackageName . pkgName . package

getPackageVersion :: PackageDescription -> S.Version
getPackageVersion = S.fromCabalVersion . pkgVersion . package

-- | Get the Dependencies of a package
-- TODO: We could get more accurate dependencies using the
-- GenericPackageDescription and the fields condExecutable,
-- https://github.com/snoyberg/packdeps/blob/web/Distribution/PackDeps.hs#L179
getPackageDeps :: PackageDescription -> S.PackageName -> Set Text
getPackageDeps pkg name =  S.fromList $ map (T.pack . show) (M.keys deps)
    where deps = M.filterWithKey (const . (/= name)) (S.packageDependencies pkg)


-- | Get the exposed modules of a Library
getAllFiles :: PackageDescription -> [FilePath]
getAllFiles pkg = map toFilePath (exposed ++ other)
  where exposed = Cabal.exposedModules lib
        other   = Cabal.otherModules (Cabal.libBuildInfo lib)
        lib     = fromMaybe (error $ "Package " ++ show (getPackageName pkg) ++ "not a lib") (library pkg)

-- | Initialises a map with all packages seen only once
packagesMap :: [String] -> IO (Map Text Int)
packagesMap contents = do
  let pkgs = map T.pack contents
  return . M.fromList $ zip pkgs (repeat 1)

-- | Given a package it adds all its dependencies to the map
addToMap :: Map Text Int -> Package -> Map Text Int
addToMap mp pkg = S.foldl' insrt mp (packageDependencies pkg)
  where insrt m p = M.insertWith (+) p 1 m -- FIXME

-- | Find the maximum (k,v) pair comparing by value.
findMaximum :: Map a Int -> (a,Int)
findMaximum mp = head $ collectMostUsed 1 mp

-- | Get the n biggest pairs sorted by value
collectMostUsed :: Int -> Map a Int -> [(a, Int)]
collectMostUsed n mp
  | n < length l  = take n l
  | otherwise     = []
  where l = sortBy (comparing (Down . snd)) (M.toList mp) -- sort in reverse order to get the maximum this makes the function be O(n)

-- | parses the cabal files of all the packages defined in the file. It also check for their dependencies
-- and returns the most used package
-- NOTE: This assumes that all the packages defined in fpath are available in dir
getMostUsedPackages :: Int -> FilePath -> FilePath -> IO [Package]
getMostUsedPackages n dir fpath = do
  contents <- readFile fpath                                          --  TODO: Check if file empty?
  let pkgs = words contents
  pkgMap <- packagesMap pkgs                                          -- initialise the packages map
  let pkgs' = map (buildFilePathWCabal dir) pkgs
  list <- mapM (parseCabalFile' dir) pkgs'                            -- get all the Packages
  let completeMap = M.fromList (map (\x -> (packageName x, x)) list)  -- Build a map with the package Name and content
      finalMap = foldl addToMap pkgMap list                           -- Get most used packages
      mostUsed = collectMostUsed n finalMap
      mostUsedPkgs  = map (\p -> completeMap M.! fst p) mostUsed      -- return the contents of the most used packages
  outh <- openFile "test.txt" WriteMode
  hPrint outh mostUsed
  hClose outh
  return mostUsedPkgs

main = do
  let dir = "../../Stats/CabalFiles"
  let fpath = "../../Stats/all_packages.txt"
  _ <- getMostUsedPackages 9684 dir fpath
  return ()

