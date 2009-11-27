> -- | this module contains the defs of common data types and type classes
> module Text.Regex.PDeriv.Common where

> import Data.Char (ord)
> import qualified Data.IntMap as IM
> import Data.List (nubBy)

> type Range  = (Int,Int)      -- ^ (sub)words represent by range
> type Letter = (Char,Int)     -- ^ a character and its index (position)

> class IsEmpty a where
>     isEmpty :: a -> Bool

> my_hash :: Int -> Char -> Int
> my_hash i x = (ord x) + 256 * i

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



> -- | remove duplications in a list of pairs whose, using the first components as key.
> nub2 :: [(Int,a)] -> [(Int,a)]
> nub2 [] = []
> nub2 [x] = [x]                                        -- optimization
> nub2 ls@[x,y] = nubBy (\ (x,_,) (y,_,) -> x == y) ls  -- optimization
> nub2 ls = nub2sub IM.empty ls
> nub2sub im [] = []
> nub2sub im (x@(k,_):xs) = 
>     case IM.lookup k im of
>     Just _  -> nub2sub im xs
>     Nothing -> let im' = IM.insert k () im 
>                in x:(nub2sub im' xs)


> -- | remove duplications in a list of tripple, using the first components as key.
> -- nub3 = nubBy (\ (x,_,_) (y,_,_) -> x == y)
> nub3 :: [(Int,a,b)] -> [(Int,a,b)]
> nub3 [] = []
> nub3 [x] = [x]                                         -- optimization
> nub3 ls@[x,y] = nubBy (\ (x,_,_) (y,_,_) -> x == y) ls -- optimization
> nub3 ls       = nub3sub IM.empty ls
> nub3sub im [] = []
> nub3sub im (x@(k,_,_):xs) = 
>     case IM.lookup k im of
>     Just _  -> nub3sub im xs
>     Nothing -> let im' = IM.insert k () im 
>                in x:(nub3sub im' xs)






