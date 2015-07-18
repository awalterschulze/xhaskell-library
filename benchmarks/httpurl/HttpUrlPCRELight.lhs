> module Main where

> import Text.Regex.PCRE.Light
> import Data.Maybe
> import qualified Data.ByteString.Char8 as S

> pat :: S.ByteString
> pat = S.pack "^(([^:]+)://)?([^:/]+)(:([0-9]+))?(/.*)"

> url :: S.ByteString
> url = S.pack "http://www.linux.com/\nhttp://www.thelinuxshow.com/main.php3"

> parse :: Regex -> S.ByteString -> IO (Maybe [S.ByteString])
> parse compiled s =
>     do { let res = match compiled s []
>        ; case res of
>          { Just l -> return (Just l)
>          ;  _ -> return Nothing
>          }
>        }

> main :: IO ()
> main = do { f <- S.readFile "/tmp/access.log"
>	    ; let ls = S.lines f
>	          (Right compiled) = compileM pat []
>	    ; results <- mapM (parse compiled) ls
>           ; putStrLn $ show results
>           ; putStrLn $ show (length (filter isJust results))
>           }
