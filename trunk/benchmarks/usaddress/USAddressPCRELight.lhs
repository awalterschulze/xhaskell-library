> module Main where

> import Text.Regex.PCRE.Light
> import qualified Data.ByteString.Char8 as S

> usPat = S.pack "^(.*) ([A-Za-z]{2}) ([0-9]{5})(-[0-9]{4})?$"

> addr = S.pack "Mountain View, CA 90410"


> parseUSAddrCompiled pat raw_addr =
>     do { let res = match pat raw_addr []
>	 ; case res of 
>	   { Just l@[addr_with_city,state,zip,szip] -> return (Just l)
>	   ; _ -> return Nothing
>	   }
>	 }



> main :: IO ()
> main = do { f <- S.readFile "/tmp/addr.txt"
>	    ; let ls = S.lines f
>	          (Right usPatCompiled) = compileM usPat []
>	    ; results <- mapM (parseUSAddrCompiled usPatCompiled) ls
>	    ; putStrLn $ show results
>	    }


     550,872,424 bytes allocated in the heap
      38,086,916 bytes copied during GC
      29,193,504 bytes maximum residency (3 sample(s))
       1,626,876 bytes maximum slop
              45 MB total memory in use (1 MB lost due to fragmentation)

  Generation 0:   952 collections,     0 parallel,  0.19s,  0.21s elapsed
  Generation 1:     3 collections,     0 parallel,  0.04s,  0.06s elapsed

  INIT  time    0.00s  (  0.00s elapsed)
  MUT   time  270.72s  (277.79s elapsed)
  GC    time    0.24s  (  0.27s elapsed)
  EXIT  time    0.00s  (  0.00s elapsed)
  Total time  270.95s  (278.06s elapsed)

  %GC time       0.1%  (0.1% elapsed)

  Alloc rate    2,034,856 bytes per MUT second

  Productivity  99.9% of total user, 97.4% of total elapsed
