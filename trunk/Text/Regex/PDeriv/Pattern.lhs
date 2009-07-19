> module Text.Regex.PDeriv.Pattern where

> import Data.List

> import Text.Regex.PDeriv.Common
> import Text.Regex.PDeriv.RE
> import Text.Regex.PDeriv.Empty
> import Text.Regex.PDeriv.Pretty


regular expression patterns

> data Pat = PVar Int (Maybe Range) RE
>   | PPair Pat Pat
>   | PChoice Pat Pat
>   | PEmpty Pat -- used intermally to indicate that mkEmpty function has been applied.
>   deriving Show


NOTE: We ignore the 'consumed word' when comparing patterns
      (ie we only compare the pattern structure).
      Essential for later comparisons among patterns.      

> instance Eq Pat where
>   (==) (PVar x1 _ r1) (PVar x2 _ r2) = (x1 == x2) && (r1 == r2)
>   (==) (PPair p1 p2) (PPair p1' p2') = (p1 == p1') && (p2 == p2')
>   (==) (PChoice p1 p2) (PChoice p1' p2') = (p1 == p1') && (p2 == p2')
>   (==) _ _ = False


> instance Pretty Pat where
>     pretty (PVar x1 _ r1) = "(" ++ show x1 ++ ":" ++ show r1 ++ ")"
>     pretty (PPair p1 p2) = "<" ++ pretty p1 ++ "," ++ pretty p2 ++ ">"
>     pretty (PChoice p1 p2) = "(" ++ pretty p1 ++ "|" ++ pretty p2 ++ ")"
>     pretty (PEmpty p) = "[" ++ pretty p ++ "]"

strip away the binding from a pattern

> strip :: Pat -> RE 
> strip (PVar _ w r) = r
> strip (PPair p1 p2) = Seq (strip p1) (strip p2)
> strip (PChoice p1 p2) = Choice (strip p1) (strip p2)
> strip (PEmpty p) = strip p

make an empty pattern

> mkEmpPat :: Pat -> Pat
> mkEmpPat (PVar x w r) 
>  | isEmpty r = PVar x w Empty
>  | otherwise = PVar x w Phi
> mkEmpPat (PPair p1 p2) = PPair (mkEmpPat p1) (mkEmpPat p2)
> mkEmpPat (PChoice p1 p2) = PChoice (mkEmpPat p1) (mkEmpPat p2)

> pdPat :: Pat -> Letter -> [Pat]
> pdPat (PVar x w r) (l,idx) = 
>          let pd = partDeriv r l 
>          in if null pd then []
>             else case w of
>                    Nothing    -> [PVar x (Just (idx,idx)) (resToRE pd)] 
>                    Just (i,j) -> [PVar x (Just (i,j+1)) (resToRE pd)] 
> pdPat (PPair p1 p2) l = 
>   if (isEmpty (strip p1))
>   then   nub ([ PPair p1' p2 | p1' <- pdPat p1 l] ++ 
>               [ PPair (mkEmpPat p1) p2' | p2' <- pdPat p2 l])
>   else [ PPair p1' p2 | p1' <- pdPat p1 l ]
> pdPat (PChoice p1 p2) l = 
>    nub ((pdPat p1 l)  ++ (pdPat p2 l)) -- nub doesn't seem to be essential

