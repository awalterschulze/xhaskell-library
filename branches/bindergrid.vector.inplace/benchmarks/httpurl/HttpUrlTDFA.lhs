> module Main where

> import Text.Regex.TDFA.ByteString
> import Text.Regex.TDFA
> import qualified Data.ByteString.Char8 as S
> import Data.Maybe

> pat = S.pack "^(([^:]+)://)?([^:/]+)(:([0-9]+))?(/.*)"


> url = S.pack "http://www.linux.com/\nhttp://www.thelinuxshow.com/main.php3"

> parse compiled s = 
>                   let res = regexec compiled s
>                   in case res of 
>                          { (Right (Just (_,_,_,l))) -> Just l
>                          ; _ -> Nothing
>                          }

> main :: IO ()
> main = do { f <- S.readFile "/tmp/access.log"
>           ; let ls = S.lines f
>                 compiled = case compile defaultCompOpt defaultExecOpt pat of
>                            Left _ -> error " compilation failed . "
>                            Right r -> r
>                 results = map (parse compiled) ls
>           ; putStrLn $ show results
>           ; putStrLn $ show (length (filter isJust results))
>           }
