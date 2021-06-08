import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)

import AbsCPP
import LexCPP
import ParCPP
import ErrM
import TypeChecker
import Codegen
import Auss
import qualified LLVM.AST as L

initModule :: L.Module
initModule = emptyModule "codegen"

process :: String -> IO ()
process s = do
  case pProgram (myLexer s) of
    Bad err  -> do
      putStrLn "SYNTAX ERROR"
      putStrLn err
      exitFailure
    Ok  tree -> do
      case typecheck tree of
        Bad errS -> do
          putStrLn "TYPE ERROR"
          putStrLn errS
          exitFailure
        Ok (treeChecked, structs) -> do
          -- putStrLn ("OK")
          llvmIR <- codegen initModule treeChecked structs
          putStrLn llvmIR
          exitSuccess

main :: IO ()
main = do args <- getArgs
          case args of
            [file] -> readFile file >>= process
            _      -> getContents >>= process
