> module Main where

> import Text.Regex.PCRE.ByteString
> import qualified Data.ByteString.Char8 as S
> import Data.Maybe

> usPat = S.pack "^(.*) ([A-Za-z]{2}) ([0-9]{5})(-[0-9]{4})?$"

 usPat = S.pack "^(.*) ([A-Za-z]{2}) ([01]{5})"

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
>	    ; (Right usPatCompiled) <- compile compBlank execBlank usPat
>	    ; results <- mapM (parseUSAddrCompiled usPatCompiled) ls
>	    ; putStrLn $ show results
>           -- ; putStrLn $ show (length (filter isJust results))
>	    }


70230
     487,120,504 bytes allocated in the heap
      73,270,216 bytes copied during GC
      30,381,568 bytes maximum residency (3 sample(s))
       1,682,480 bytes maximum slop
              52 MB total memory in use (1 MB lost due to fragmentation)

  Generation 0:   831 collections,     0 parallel,  0.44s,  0.48s elapsed
  Generation 1:     3 collections,     0 parallel,  0.04s,  0.06s elapsed

  INIT  time    0.00s  (  0.00s elapsed)
  MUT   time    1.43s  ( 11.59s elapsed)
  GC    time    0.48s  (  0.54s elapsed)
  EXIT  time    0.00s  (  0.00s elapsed)
  Total time    1.91s  ( 12.13s elapsed)

  %GC time      25.2%  (4.4% elapsed)

  Alloc rate    340,902,127 bytes per MUT second

  Productivity  74.8% of total user, 11.8% of total elapsed