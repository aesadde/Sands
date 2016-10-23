module Scraper where

import Network.HTTP
import System.IO
import System.FilePath
import System.Directory
import Control.Monad (unless)
import Types (Package(..))
import qualified Data.Text as T
import Text.HTML.TagSoup
import Data.Char
import Text.HTML.TagSoup.Match
import Data.Text (Text)
import qualified Data.Text (pack)

-- | Gets the contents of the URL
get :: String -> IO String
get url = simpleHTTP (getRequest url) >>= getResponseBody

-- | Build the URL from where to get the cabal file for a package
buildCabalUrl :: String -> String
buildCabalUrl pkgName = "http://hackage.haskell.org/package/" ++ pkgName ++ "/" ++ pkgName ++ ".cabal"

-- | Construct the filepath from where to retrieve the stored cabal files
buildFilePath :: FilePath -> String -> FilePath
buildFilePath fpath pkgName = fpath </> pkgName

buildFilePathWCabal :: FilePath -> String -> FilePath
buildFilePathWCabal fpath pkgName = fpath </> (pkgName ++ ".cabal")

buildPkgFilePath :: Package -> FilePath
buildPkgFilePath pkg = "http://hackage.haskell.org/package/" ++ pkg' ++ "/" ++ pkg' ++ ".tar.gz"
  where pkg' = T.unpack (packageName pkg) ++ "-" ++ T.unpack (packageVersion pkg)

-- | Given a package name this function gets the contents of the cabal file
getCabalFile :: FilePath -> String -> IO ()
getCabalFile dir pkgName = do
  createDirectoryIfMissing True dir
  let fname = buildFilePathWCabal dir pkgName
  exist <- doesFileExist fname
  unless exist $ get (buildCabalUrl pkgName) >>= writeFile fname

-- | Get all the cabal files. This assumes that we have an existing list of all
-- packages.
getAllCabalFiles :: FilePath -> FilePath -> IO ()
getAllCabalFiles dir file = do
  exist <- doesFileExist file
  if exist then do
      contents <- readFile file
      let pkgNames = words contents
      mapM_ (getCabalFile dir) pkgNames
  else error "File with cabal names does not exist"

scrapeDownloads :: String -> IO Int
scrapeDownloads pkg = do
  let url = buildPkgUrl pkg
  src <- get url
  let downloads = fromFooter $ parseTags src
  return $ (read downloads :: Int)

  where fromFooter = takeWhile (/= ' ') . innerText .  takeWhile (not . isTagCloseName "td") . dropWhile (not . isTagOpenName "td") . dropWhile (\x -> not $ isTagText x && fromTagText x == "Downloads")

buildPkgUrl pkgName = "http://hackage.haskell.org/package/" ++ pkgName

main = scrapeDownloads
