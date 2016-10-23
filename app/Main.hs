module Main where

import AbsMachine
import CoreParser (compileToCore,parsePkg)

main :: IO ()
main = do
  print "Enter the path to the file we are going to compile"
  -- fpath' <- getLine
  let fpath' = "Vectors.hs"
  let fpath = "../other/improvement/" ++ fpath'
  guts <- compileToCore fpath (epkg fpath)
  let binds = mg_binds guts
  putStrLn " === Semantics === "
  eval binds
