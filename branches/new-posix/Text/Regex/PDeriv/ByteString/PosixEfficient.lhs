> {- By Kenny Zhuo Ming Lu and Martin Sulzmann, 2013, BSD License -}

A bytestring implementation of reg exp pattern matching using partial derivative / derivative
The POSIX matching policy is implemented by following the 'structure' of the reg-exp.
The pattern is follow annotated. 
We do not break part the sub-pattern of the original reg, they are always grouped under the same var pattern.


> {-# LANGUAGE GADTs, MultiParamTypeClasses, FunctionalDependencies,
>     FlexibleInstances, TypeSynonymInstances, FlexibleContexts #-} 


> module Text.Regex.PDeriv.ByteString.Posix
> {-    ( Regex
>     , CompOption(..)
>     , ExecOption(..)
>     , defaultCompOpt
>     , defaultExecOpt
>     , compile
>     , execute
>     , regexec
>     ) -} where 


> import System.IO.Unsafe


> import Data.List 
> import Data.Char (ord)
> import GHC.Int
> import GHC.Arr 
> import qualified Data.IntMap as IM
> import qualified Data.ByteString.Char8 as S


> import Text.Regex.Base(RegexOptions(..),RegexLike(..),MatchArray)


> import Text.Regex.PDeriv.RE
> import Text.Regex.PDeriv.Pretty (Pretty(..))
> import Text.Regex.PDeriv.Common (Range(..), Letter, PosEpsilon(..), my_hash, my_lookup, GFlag(..), IsGreedy(..), preBinder, subBinder, mainBinder)
> import Text.Regex.PDeriv.IntPattern (Pat(..), pdPat, toBinder, Binder(..), strip, listifyBinder)
> import Text.Regex.PDeriv.Parse
> import qualified Text.Regex.PDeriv.Dictionary as D (Dictionary(..), Key(..), insertNotOverwrite, lookupAll, empty, isIn, nub)



> logger io = unsafePerformIO io


> data SBinder = SChoice [SBinder]                   
>           | SPair SBinder SBinder              
>           | SVar (Int,[Range]) SBinder [SBinder] --  [SBinder] is carrying the carry-forward env due to the simplification
>           | SStar -- no need to store anything
>           | SRE
>    deriving Show

> toSBinder :: Pat -> SBinder
> toSBinder (PVar x w p) = SVar (x,[]) (toSBinder p) []
> toSBinder (PE r) = SRE
> toSBinder (PStar p g) = SStar
> toSBinder (PPair p1 p2) = SPair (toSBinder p1) (toSBinder p2)
> toSBinder (PChoice p1 p2 g) = SChoice [toSBinder p1, toSBinder p2]


The invariance: 
The shapes of the input/output Pat and SBinder should be identical.
                   
> dPat0 :: Pat -> Letter -> [(Pat, Int -> SBinder -> SBinder)]  -- the lists are always singleton,
> dPat0 (PVar x w p) (l, idx) = 
>    do { (p',f) <- dPat0 p (l, idx)  
>       ; return (PVar x [] p', (\i sb -> 
>                              case sb of 
>                              { SVar (v, r) sb' cf -> SVar (v, updateRange i r) (f i sb') cf
>                              ; _ -> error ("dPat0 failed with pattern " ++ (show (PVar x w p))  ++ " and binding " ++ (show sb))
>                              }) ) }

> dPat0 (PE r) (l, idx) =
>    let pds = partDeriv r l
>    in pds `seq` if null pds then []
>                 else [ (PE (resToRE pds), (\_ -> id) )]  
> dPat0 (PStar p g) l = 
>    do { (p', f) <- dPat0 p l        
>       ; let emp = toSBinder p                     
>       ; return (PPair p' (PStar p g), (\i sb -> 
>                     case sb of { SStar -> SPair (f i emp) sb } ) ) 
>       }
> dPat0 (PPair p1 p2) l = 
>    if (posEpsilon (strip p1))
>    then let pf1 = dPat0 p1 l -- we need to remove the empty pattern (potentially)
>             pf2 = dPat0 p2 l 
>         in case (pf1, pf2) of 
>         { ([], []) -> [] 
>         ; ([], _ ) -> do 
>            { (p2', f2) <- pf2 -- we drop the sb1, because it reaches no state
>            ; let rm = removeNonEmpty p1
>            ; return (p2', (\i sb -> case sb of 
>                           { SPair sb1 sb2 -> 
>                              let sb1' = rm sb1 
>                              in carryForward sb1' (f2 i sb2) }))
>            }
>         ; (_ , []) -> do 
>            { (p1', f1) <- pf1 
>            ; return ( PPair p1' p2, (\i sb -> case sb of 
>                           { SPair sb1 sb2 -> SPair (f1 i sb1) sb2 }))
>            }
>         ; (_, _) -> do
>            { (p1',f1) <- dPat0 p1 l 
>            ; (p2',f2) <- dPat0 p2 l
>            ; let rm = removeNonEmpty p1
>            ; return ( PChoice (PPair p1' p2) p2' Greedy
>                     , (\i sb -> case sb of 
>                         { SPair sb1 sb2 -> 
>                            let sb1' = rm sb1
>                            in SChoice [ SPair (f1 i sb1) sb2, carryForward sb1' (f2 i sb2) ] -- TODO: we need to shift the sb1 to sb2 in the (f2 i sb2)
>                         } )
>                     ) }
>         }
>    else do { (p1',f1) <- dPat0 p1 l
>            ; return ( PPair p1' p2 
>                     , (\i sb -> case sb of 
>                         { SPair sb1 sb2 -> SPair (f1 i sb1) sb2 } )
>                     ) }
> dPat0 (PChoice p1 p2 g) l = 
>    let pf1 = dPat0 p1 l 
>        pf2 = dPat0 p2 l         
>    in case (pf1,pf2) of 
>    { ([], []) -> [] 
>    ; ([], _ ) -> do 
>       { (p2', f2) <- pf2
>       ; return (p2', (\i sb -> case sb of 
>                      { SChoice [sb1,sb2] -> f2 i sb2 }))
>       }
>    ; (_ , []) -> do 
>       { (p1', f1) <- pf1
>       ; return (p1', (\i sb -> case sb of 
>                      { SChoice [sb1,sb2] -> f1 i sb1 }))
>       }
>    ; _ -> do   
>       { (p1',f1) <- pf1
>       ; (p2',f2) <- pf2
>       ; return (PChoice p1' p2' g, (\i sb ->                       
>              case sb of { SChoice [sb1,sb2] -> SChoice [f1 i sb1, f2 i sb2] }))
>       }
>    }

> carryForward :: SBinder -> SBinder -> SBinder
> carryForward sb1 (SVar (v, r) sb' cf) = SVar (v, r) sb' (sb1:cf)
> carryForward sb1 _ = error "trying to carry forward into a non-annotated pattern binder"

> removeNonEmpty :: Pat -> SBinder -> SBinder                                           
> removeNonEmpty (PVar x w p) (SVar (_,b) sb cf) 
>       | posEpsilon (strip p) = SVar (x,b) (removeNonEmpty p sb) cf
>       | otherwise = SVar (x,[]) SRE cf
> removeNonEmpty (PE r) SRE = SRE
> removeNonEmpty (PStar p g) SStar = SStar
> removeNonEmpty (PPair p1 p2) (SPair sb1 sb2) = SPair (removeNonEmpty p1 sb1) (removeNonEmpty p2 sb2) 
> removeNonEmpty (PChoice p1 p2 g) (SChoice [sb1, sb2]) = 
>       SChoice [removeNonEmpty p1 sb1, removeNonEmpty p2 sb2]


> updateRange :: Int -> [Range] -> [Range]
> updateRange pos (rs_@((Range b e):rs)) = 
>           let e' = e + 1    
>           in case e' of
>              _ | pos == e' -> ((Range b e'):rs)
>                | pos > e'  -> ((Range pos pos):rs_)
>                | otherwise -> error "impossible, the current letter position is smaller than the last recorded letter" 
> updateRange pos [] = [(Range pos pos)]


> matchInner :: [(Pat, SBinder)] -> [(Char,Int)] -> [(Pat, SBinder)]
> matchInner pb [] = pb
> matchInner pb (l:ls) = 
>   do { (p,sb) <- pb  
>      ; (p',f) <- dPat0 p l
>      ; matchInner [(p', f (snd l) sb)] ls 
>      }



> p4 = PVar 0 [] (PPair (PVar 1 [] ((PPair p_x p_y))) p_z)
>    where p_x = PVar 2 [] (PE (Choice (L 'A') (Seq (L 'A') (L 'B')) Greedy))      
>          p_y = PVar 3 [] (PE (Choice (Seq (L 'B') (Seq (L 'A') (L 'A'))) (L 'A') Greedy))
>          p_z = PVar 4 [] (PE (Choice (Seq (L 'A') (L 'C')) (L 'C') Greedy))






