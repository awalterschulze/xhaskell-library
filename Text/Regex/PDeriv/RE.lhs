
> {-# LANGUAGE GADTs, MultiParamTypeClasses, FunctionalDependencies,
>     FlexibleInstances, TypeSynonymInstances, FlexibleContexts #-} 

> module Text.Regex.PDeriv.RE where


> import Data.List (nub)

> import Text.Regex.PDeriv.Empty

------------------------
-- regular expresions

> data RE = Phi 
>  | Empty        -- empty lang
>  | L Char	  -- literal
>  | Choice RE RE -- r1 + r2
>  | Seq RE RE    -- (r1,r2)
>  | Star RE      -- r*
> --   deriving Eq

> instance Eq RE where
>     (==) Empty Empty = True
>     (==) (L x) (L y) = x == y
>     (==) (Choice r1 r2) (Choice r3 r4) = (r1 == r3) && (r2 == r4)
>     (==) (Seq r1 r2) (Seq r3 r4) = (r1 == r3) && (r2 == r4)
>     (==) (Star r1) (Star r2) = r1 == r2
>     (==) _ _ = False


A pretty printing function for regular expression

> instance Show RE where
>     show Phi = "{}"
>     show Empty = "<>"
>     show (L c) = show c
>     show (Choice r1 r2) = ("(" ++ show r1 ++ "|" ++ show r2 ++ ")")
>     show (Seq r1 r2) = ("<" ++ show r1 ++ "," ++ show r2 ++ ">")
>     show (Star r) = (show r ++ "*")

Summig up a list of regular expressions with choice operation.

> resToRE :: [RE] -> RE
> resToRE (r:res) = foldl Choice r res
> resToRE [] = Phi

Check whether regular expressions are empty

> instance IsEmpty RE where
>   isEmpty Phi = False
>   isEmpty Empty = True
>   isEmpty (Choice r1 r2) = (isEmpty r1) || (isEmpty r2)
>   isEmpty (Seq r1 r2) = (isEmpty r1) && (isEmpty r2)
>   isEmpty (Star r) = True
>   isEmpty (L _) = False
        

the partial derivative operations

> partDeriv :: RE -> Char -> [RE]
> partDeriv Phi l = []
> partDeriv Empty l = []
> partDeriv (L l') l 
>     | l == l'   = [Empty]
>     | otherwise = []
> partDeriv (Choice r1 r2) l = nub ((partDeriv r1 l) ++ (partDeriv r2 l))
> partDeriv (Seq r1 r2) l 
>     | isEmpty r1 = 
>           let s1 = [ (Seq r1' r2) | r1' <- partDeriv r1 l ]
>               s2 = partDeriv r2 l
>           in nub (s1 ++ s2)
>     | otherwise = [ (Seq r1' r2) | r1' <- partDeriv r1 l ]
> partDeriv (Star r) l = [ (Seq r' (Star r)) | r' <- partDeriv r l ]



> sigmaRE :: RE -> [Char]
> sigmaRE (L l) = [l]
> sigmaRE (Seq r1 r2) = nub ((sigmaRE r1) ++ (sigmaRE r2))
> sigmaRE (Choice r1 r2) = nub ((sigmaRE r1) ++ (sigmaRE r2))
> sigmaRE (Star r) = sigmaRE r
> sigmaRE Phi = []
> sigmaRE Empty = []

