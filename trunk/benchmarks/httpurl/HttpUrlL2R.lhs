> module Main where

> import Text.Regex.PDeriv.ByteString.LeftToRight -- AKA RightToLeft
> import Data.Maybe
> import qualified Data.ByteString.Char8 as S

> pat = S.pack "^(([^:]+)://)?([^:/]+)(:([0-9]+))?(/.*)"

-> pat = S.pack "^(([a-zA-Z0-9]+)://)?(.+)(:([0-9]+))?(/.*)"


> url = S.pack "http://www.linux.com/\nhttp://www.thelinuxshow.com/main.php3"

> parse compiled s = case regexec compiled s of 
>                    (Right (Just (_,_,_,l))) -> Just l
>                    _ -> Nothing

> main :: IO ()
> main = do { f <- S.readFile "/tmp/access.log"
>           ; let ls = S.lines f
>                 compiled = case compile defaultCompOpt defaultExecOpt pat of
>                            Left _ -> error " compilation failed . "
>                            Right r -> r
>                 results = (map (parse compiled) ls)
>           ; putStrLn $ show results
>           ; putStrLn $ show (length (filter isJust results))
>           }
