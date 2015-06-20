> module Main where

> import Text.Regex.PDeriv.ByteString

> import qualified Data.ByteString.Char8 as S

> pat = S.pack "^([0-9]{1,3}?)([0-9]{5,7})$"

> input = S.pack "90121486"

> compiled = case compile defaultCompOpt defaultExecOpt pat of
>            Left _ -> error " compilation failed . "
>            Right r -> r

> run s = regexec compiled s

> main :: IO ()
> main = do { putStrLn $ show (run input) }
