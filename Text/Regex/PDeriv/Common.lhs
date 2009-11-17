> -- | this module contains the defs of common data types and type classes
> module Text.Regex.PDeriv.Common where

> import Data.Char (ord)
> import qualified Data.IntMap as IM

> type Range  = (Int,Int)      -- ^ (sub)words represent by range
> type Letter = (Char,Int)     -- ^ a character and its index (position)

> class IsEmpty a where
>     isEmpty :: a -> Bool

> my_hash :: Int -> Char -> Int
> my_hash i x = (ord x) + 1000 * i

the lookup function

> my_lookup :: Int -> Char -> IM.IntMap [Int] -> [Int]
> my_lookup i x dict = case IM.lookup (my_hash i x) dict of
>                      Just ys -> ys
>                      Nothing -> []



> -- | The greediness flag
> data GFlag = Greedy    -- ^ greedy
>            | NotGreedy -- ^ not greedy
>              deriving Eq

> instance Show GFlag where
>     show Greedy = ""
>     show NotGreedy = "?"

> class IsGreedy a where
>     isGreedy :: a -> Bool


