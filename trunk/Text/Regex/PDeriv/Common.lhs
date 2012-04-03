> {-# LANGUAGE BangPatterns #-}
> -- | this module contains the defs of common data types and type classes
> module Text.Regex.PDeriv.Common 
>     ( Range(..), range, minRange, maxRange
>     , Letter
>     , PosEpsilon (..)
>     , IsEpsilon (..)
>     , IsPhi (..)
>     , Simplifiable (..)
>     , my_hash
>     , my_lookup
>     , GFlag (..)
>     , IsGreedy (..)
>     , nub2
>     , nub3
>     , preBinder
>     , preBinder_
>     , subBinder
>     , mainBinder
>     ) where

> import Data.Char (ord)
> import qualified Data.IntMap as IM
> import qualified Data.BitSet as BS
> import Data.List (nubBy)

> -- | (sub)words represent by range
> -- type Range  = (Int,Int)      
> data Range = Range !Int !Int deriving Show

> instance Eq Range where
>   (==) (Range x y) (Range w z) = (x == w) && (y == z)

> range :: Int -> Int -> Range
> range = Range

> minRange = fst
> maxRange = snd

> -- | a character and its index (position)
> type Letter = (Char,Int)     

> -- | test for 'epsilon \in a' epsilon-possession
> class PosEpsilon a where
>     posEpsilon :: a -> Bool

> -- | test for epsilon == a
> class IsEpsilon a where
>     isEpsilon :: a -> Bool

> -- | test for \phi == a
> class IsPhi a where
>     isPhi :: a -> Bool

> class Simplifiable a where
>     simplify :: a -> a


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


> -- | remove duplications in a list of pairs, using the first components as key.
> nub2 :: [(Int,a)] -> [(Int,a)]
> nub2 [] = []
> nub2 [x] = [x]                                        -- optimization
> -- nub2 ls@[x,y] = nubBy (\ (x,_) (y,_) -> x == y) ls    -- optimization
> nub2 ls = nub2sub IM.empty ls
>           -- nub2aux BS.empty ls []


> nub2sub im [] = []
> nub2sub im (x@(k,_):xs) = 
> --    im `seq` k `seq` 
>            case IM.lookup k im of
>            Just _  -> xs `seq` nub2sub im xs
>            Nothing -> let im' = IM.insert k () im 
>                       in im' `seq` xs `seq` x:(nub2sub im' xs)

> {-
> nub2sub im [] = []
> nub2sub im (x@(k,_):xs) = 
> --    im `seq` k `seq` 
>            if not (IM.notMember k im)
>            then xs `seq` nub2sub im xs
>            else let im' = IM.insert k () im 
>                 in im' `seq` xs `seq` x:(nub2sub im' xs)
> -}

> nub2aux bs [] acc = reverse acc 
> nub2aux bs (x@(k,_):xs) acc = 
>     case bs `seq` k `seq` BS.member k bs of 
>       True  -> xs `seq` nub2aux bs xs acc
>       False -> let bs' = BS.insert k bs
>                in bs' `seq` xs `seq` (nub2aux bs' xs (x:acc))


> nub3 :: [(Int,a,Int)] -> [(Int,a,Int)]
> nub3 [] = []
> nub3 [x] = [x]                                            -- optimization
> nub3 ls = nub3subsimple IM.empty ls

     let (_,ls') = nub3sub IM.empty ls
     in ls'

> nub3subsimple :: IM.IntMap () -> [(Int,a,Int)] -> [(Int,a,Int)]
> nub3subsimple im [] = []
> nub3subsimple im [ x ] = [ x ]
> nub3subsimple im (x@(k,f,0):xs) = x:(nub3subsimple im xs)
> nub3subsimple im (x@(k,f,1):xs) = let im' = IM.insert k () im
>                                   in im' `seq` x:(nub3subsimple im' xs)
> nub3subsimple im (x@(k,f,n):xs) = case IM.lookup k im of 
>                                   Just _ -> nub3subsimple im xs
>                                   Nothing -> let im' = IM.insert k () im
>                                              in im' `seq` xs `seq` x:(nub3subsimple im' xs)

> nub3sub :: IM.IntMap () -> [(Int,a,Int)] -> (IM.IntMap (), [(Int,a,Int)])
> {-# INLINE nub3sub #-}
> nub3sub im [] = (im,[])
> nub3sub im [(k,f,0)] = (im, [(k,f,0)]) -- 0 means deterministic
> nub3sub im [(k,f,1)] = let im' = IM.insert k () im  -- 1 means greedy
>                        in (im', [(k,f,1)])
> nub3sub im (x@(k,f,0):xs) = let (im',xs') = nub3sub im xs
>                             in (im',x:xs')
> nub3sub im (x@(k,f,1):xs) = let im' = IM.insert k () im
>                                 (im'', xs') = nub3sub im' xs
>                             in (im'', x:xs')
> nub3sub im (x@(k,f,n):xs) = case IM.lookup k im of 
>                               Just _ -> nub3sub im xs
>                               Nothing -> let (im', xs') = nub3sub im xs
>                                          in case IM.lookup k im' of 
>                                               Just _ -> (im', xs')
>                                               Nothing -> (im', x:xs')


The smallest binder index capturing the prefix of the unanchored regex

> preBinder :: Int
> preBinder = -1

> preBinder_ :: Int
> preBinder_ = -2

The largest binder index capturing for the suffix of the unanchored regex

> subBinder :: Int
> subBinder = 2147483647


The binder index capturing substring which matches by the unanchored regex

> mainBinder :: Int
> mainBinder = 0