module Main where

import Text.Regex.PDeriv.ByteString.RightToLeft

import qualified Data.ByteString.Char8 as S

import System.Environment (getArgs)

com :: S.ByteString -> Regex
com p =
    case compile defaultCompOpt defaultExecOpt p of
      Left e -> error $ " compilation failed . " ++ show e
      Right r -> r

strip :: IO S.ByteString -> IO S.ByteString
strip ss = do {
    s <- ss;
    return (S.pack $ filter (/='\n') (S.unpack s))
}

main :: IO ()
main = do { [arg1,arg2] <- getArgs
          ; pat         <- strip $ S.readFile arg1
          ; print pat
          ; case parsePat $ S.unpack pat of
            { Left _ -> return ()
            ; Right p' -> print p'
            }
          ; input       <- S.readFile arg2
          ; let strs = S.lines input
          ; let p_ = com pat
          ; case strs of
              { (str:_) -> print (regexec p_ str)
              ; _ -> print "No input"
              }
          }
