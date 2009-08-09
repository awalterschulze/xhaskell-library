> module Main where

> import Text.Regex.Posix.ByteString
> import Data.Maybe 
> import qualified Data.ByteString.Char8 as S

> usPat = S.pack "^(.*) ([A-Za-z]{2}) ([0-9]{5})(-[0-9]{4})?$"

> addr = S.pack "Mountain View, CA 90410"


> parseUSAddrCompiled pat raw_addr =
>     do { res <- regexec pat raw_addr
>	 ; case res of 
>	   { (Right (Just (_,_,_,l@[addr_with_city,state,zip,szip]) )) -> return (Just l)
>	   ; _ -> return Nothing
>	   }
>	 }



> main :: IO ()
> main = do { f <- S.readFile "/tmp/addr.txt"
>	    ; let ls = S.lines f
>	    ; (Right usPatCompiled) <- compile compExtended execBlank usPat
>	    ; results <- mapM (parseUSAddrCompiled usPatCompiled) ls
>	    ; putStrLn $ show results
>           ; putStrLn $ show (length (filter isJust results))
>	    }


70230
     511,829,668 bytes allocated in the heap
      70,448,400 bytes copied during GC
      30,460,296 bytes maximum residency (3 sample(s))
       1,679,524 bytes maximum slop
              48 MB total memory in use (0 MB lost due to fragmentation)

  Generation 0:   832 collections,     0 parallel,  0.41s,  0.44s elapsed
  Generation 1:     3 collections,     0 parallel,  0.04s,  0.05s elapsed

  INIT  time    0.00s  (  0.00s elapsed)
  MUT   time   18.75s  ( 27.88s elapsed)
  GC    time    0.45s  (  0.50s elapsed)
  EXIT  time    0.00s  (  0.00s elapsed)
  Total time   19.20s  ( 28.38s elapsed)

  %GC time       2.3%  (1.8% elapsed)

  Alloc rate    27,297,783 bytes per MUT second

  Productivity  97.7% of total user, 66.1% of total elapsed