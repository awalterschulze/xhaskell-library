> module Main where

> import Text.Regex.TDFA.ByteString
> import Text.Regex.TDFA

> import qualified Data.ByteString.Char8 as S

> usPat = S.pack "^(.*) ([A-Za-z]{2}) ([0-9]{5})(-[0-9]{4})?$"

> addr = S.pack "Mountain View, CA 90410"

> compiled = case compile defaultCompOpt defaultExecOpt usPat of
>            Left _ -> error " compilation failed . "
>            Right r -> r

> parseUSAddrCompiled s = regexec compiled s 

> main :: IO ()
> main = do { f <- S.readFile "/tmp/addr.txt"
>             ; let ls = S.lines f
>             ; putStrLn $ show (map parseUSAddrCompiled ls)
>             }


./USAddressTDFA +RTS -sstderr 
  21,519,117,176 bytes allocated in the heap
      76,298,104 bytes copied during GC
      15,272,152 bytes maximum residency (2 sample(s))
         561,240 bytes maximum slop
              16 MB total memory in use (0 MB lost due to fragmentation)

  Generation 0: 41134 collections,     0 parallel,  0.57s,  0.69s elapsed
  Generation 1:     2 collections,     0 parallel,  0.00s,  0.00s elapsed

  INIT  time    0.00s  (  0.00s elapsed)
  MUT   time   18.17s  ( 18.71s elapsed)
  GC    time    0.57s  (  0.69s elapsed)
  EXIT  time    0.00s  (  0.00s elapsed)
  Total time   18.74s  ( 19.40s elapsed)

  %GC time       3.1%  (3.6% elapsed)

  Alloc rate    1,184,407,232 bytes per MUT second

  Productivity  96.9% of total user, 93.7% of total elapsed