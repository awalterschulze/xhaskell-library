> module Main where

> import Text.Regex.PCRE.ByteString  -- AKA RightToLeft
> import Data.Maybe
> import qualified Data.ByteString.Char8 as S

> pat = S.pack "^(([^:]+)://)?([^:/]+)(:([0-9]+))?(/.*)"


> url = S.pack "http://www.linux.com/\nhttp://www.thelinuxshow.com/main.php3"

> parse compiled s = 
>     do { res <- regexec compiled s
>        ; case res of 
>          { (Right (Just (_,_,_,l))) -> return (Just l)
>          ;  _ -> return Nothing
>          }
>        }

> main :: IO ()
> main = do { f <- S.readFile "/tmp/access.log"
>	    ; let ls = S.lines f
>	    ; (Right compiled) <- compile compBlank execBlank pat
>	    ; results <- mapM (parse compiled) ls
>           ; putStrLn $ show results
>           ; putStrLn $ show (length (filter isJust results))
>           }
