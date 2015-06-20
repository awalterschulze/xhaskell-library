A library implementation of XHaskell. We exploit the idea of partial derivatives in building efficient regular expression pattern matching algorithms.

## Documentation ##

The ideas can be found in Kenny's and Martin's blogs
http://luzhuomi.blogspot.com/
http://sulzmann.blogspot.com/

## News ##
  * For referential implementation of Glushkov and Thompson NFA, please visit [here](http://code.google.com/p/xhaskell-library/source/browse/#svn%2Ftrunk%2Freference_impl) and [here](http://luzhuomi.blogspot.com/2012/06/extending-glushkov-nfa-with-sub.html).
  * version 0.1.0 is released.
  * I fixed most of the bugs in the POSIX match algo thanks to Chris Kuklewicz's help and his unit test suites. The posix algo should tally with the test cases (most of them). Except for different interpretation of "no match". We consistently use (-1,0) to denote "no match" for a sub pattern, instead of keeping track of the last match position.
  * Some outstanding problems with "^" and "$" being interpreted wrongly when they are used in the middle of the regex.

## Downloads ##
  * To download the latest tar-ball please visit http://hackage.haskell.org/package/regex-pderiv ; or
  * Use `cabal install regex-pderiv`, haskell-platform is required.

## Benchmark ##

  * Latest [benchmark ](https://spreadsheets.google.com/pub?hl=en&hl=en&key=0AsJzxtc70DgEdEJUMVVCWkpvVVpVcVAxSElUVHRVUVE&output=html)


## Supporting Features ##
  * Literals
  * Wildcard
  * Line anchors
  * Repeats
  * Non-greedy repeats
  * Parathesis
  * Alternatives
  * Character literals
  * Character range
  * Escape Operator
  * Non-marking parenthesis
  * Unicode

## Missing Features ##
  * Forward lookahead asserts
  * Back reference
  * Locale
  * Character class
  * Collating element
  * Equivalent class
  * Character by code
  * Word operators
  * Buffer operators
  * Single character escape sequences

(Definitions of the above features can be found [here](http://www.araxis.com/merge/topic_regexpreference.html).)

## Example ##
```
> module Main where

this example shows that the overhead with this pure approach is
coming from the uncons operation for bytestring

> import System
> import Text.Regex.PDeriv.ByteString
> import Data.Maybe
> import qualified Data.ByteString.Char8 as S

> pat = S.pack "^.*$"

> parse compiled s = case regexec compiled s of
>                      (Right (Just (_,_,_,l))) -> Just l
>                      _ -> Nothing

> main :: IO ()
> main = do
>   { [ i ] <- getArgs
>   ; let
>         x = read i
>         ls = S.replicate x 'a'
>         compiled = case compile defaultCompOpt defaultExecOpt pat of
>                    Left _  -> error " compilation failed . "
>                    Right r -> r
>   ; let result = parse compiled ls
>   ; putStrLn (show result)
>   }

```
