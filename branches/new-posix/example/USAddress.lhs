> module Main where

> import Text.Regex.PDeriv.ByteString.PosixEfficient

> import qualified Data.ByteString.Char8 as S

> usPat = S.pack "^(.*) ([A-Za-z]{2}) ([0-9]{5})(-[0-9]{4})?$"

> addr = S.pack "Mountain View, CA 90410"

> compiled = case compile defaultCompOpt defaultExecOpt usPat of
>            Left _ -> error " compilation failed . "
>            Right r -> r

> parseUSAddrCompiled s = 
>     let res = regexec compiled s 
>     in case res of 
>            { (Right (Just (_,_,_,l@[addr_with_city,state,zip,szip]) )) -> Just l
>            ; _ -> Nothing
>            }

> main :: IO ()
> main = do { f <- S.readFile "/tmp/addr.txt"
>             ; let ls = S.lines f
>             ; putStrLn $ show (map parseUSAddrCompiled ls)
>             }
