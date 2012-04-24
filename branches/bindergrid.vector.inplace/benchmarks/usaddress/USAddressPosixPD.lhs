> module Main where

> import Text.Regex.PDeriv.ByteString.Posix
> import Data.Maybe
> import qualified Data.ByteString.Char8 as S

> usPat = S.pack "^(.*) ([A-Za-z]{2}) ([0-9]{5})(-[0-9]{4})?$"

> addr = S.pack "Mountain View, CA 90410"

> parseUSAddrCompiled compiled s = case regexec compiled s of 
>                                  (Right (Just (_,_,_,l))) -> Just l
>                                  _ -> Nothing

> main :: IO ()
> main = do { f <- S.readFile "/tmp/addr.txt"
>           ; let ls = S.lines f
>                 compiled = case compile defaultCompOpt defaultExecOpt usPat of
>                            Left _ -> error " compilation failed . "
>                            Right r -> r
>                 results = (map (parseUSAddrCompiled compiled) ls)
>           ; putStrLn $ show results
>           -- ; putStrLn $ show (length (filter isJust results))
>           }


