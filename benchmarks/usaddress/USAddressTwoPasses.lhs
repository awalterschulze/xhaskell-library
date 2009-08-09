> module Main where

> import Text.Regex.PDeriv.ByteString.TwoPasses
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
>           ; putStrLn $ show (length (filter isJust results))
>           }


70198
   2,891,481,464 bytes allocated in the heap
      65,623,996 bytes copied during GC
      27,227,732 bytes maximum residency (4 sample(s))
         783,932 bytes maximum slop
              47 MB total memory in use (0 MB lost due to fragmentation)

  Generation 0:  5448 collections,     0 parallel,  0.33s,  0.42s elapsed
  Generation 1:     4 collections,     0 parallel,  0.04s,  0.07s elapsed

  INIT  time    0.00s  (  0.00s elapsed)
  MUT   time    5.12s  (108.76s elapsed)
  GC    time    0.38s  (  0.48s elapsed)
  EXIT  time    0.00s  (  0.00s elapsed)
  Total time    5.50s  (109.25s elapsed)

  %GC time       6.8%  (0.4% elapsed)

  Alloc rate    564,527,247 bytes per MUT second

  Productivity  93.1% of total user, 4.7% of total elapsed