module Main where

import qualified System.IO.UTF8

import Text.Regex.PDeriv.ByteString.RightToLeft

import qualified Data.ByteString.Char8 as S

import System

com p =
    case compile defaultCompOpt defaultExecOpt p of
      Left e -> error $ " compilation failed . " ++ show e
      Right r -> r

run p s = regexec p s

main :: IO ()
main = do { [arg1,arg2] <- getArgs
          ; pat         <- S.readFile arg1
          ; print pat
          ; case parsePat $ S.unpack pat of
            { Left _ -> return ()
            ; Right p' -> print p'
            }
          ; input       <- S.readFile arg2
          ; let strs = S.lines input
          ; let p_ = com pat
          ; case strs of
              { (str:_) -> putStrLn $ show (run p_ str)
              ; _ -> print "No input"
              }
          }
