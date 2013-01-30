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
> import qualified Data.Map as M


> import Text.Regex.Base(RegexOptions(..),RegexLike(..),MatchArray)


> import Text.Regex.PDeriv.RE
> import Text.Regex.PDeriv.Pretty (Pretty(..))
> import Text.Regex.PDeriv.Common (Range(..), Letter, PosEpsilon(..), my_hash, my_lookup, GFlag(..), IsGreedy(..), preBinder, subBinder, mainBinder)
> import Text.Regex.PDeriv.IntPattern (Pat(..), pdPat, toBinder, Binder(..), strip, listifyBinder, Key(..))
> import Text.Regex.PDeriv.Parse
> import qualified Text.Regex.PDeriv.Dictionary as D (Dictionary(..), Key(..), insertNotOverwrite, lookupAll, empty, isIn, nub)



> logger io = unsafePerformIO io

> type SRange = (Int,[Range])


> data SBinder = SChoice [SBinder] [SRange]                
>           | SPair SBinder SBinder [SRange]               
>           | SVar SRange SBinder [SRange] --  [SBinder] is carrying the carry-forward env due to the simplification
>           | SStar [SRange] -- no need to store anything
>           | SRE [SRange]
>    deriving Show

> toSBinder :: Pat -> SBinder
> toSBinder (PVar x w p) = SVar (x,[]) (toSBinder p) []
> toSBinder (PE r) = SRE []
> toSBinder (PStar p g) = SStar []
> toSBinder (PPair p1 p2) = SPair (toSBinder p1) (toSBinder p2) []
> toSBinder (PChoice ps g) = SChoice (map toSBinder ps) []


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
>                     case sb of { SStar cf -> SPair (f i emp) sb cf} ) ) 
>       }
> dPat0 (PPair p1 p2) l = 
>    if (posEpsilon (strip p1))
>    then let pf1 = dPat0 p1 l -- we need to remove the empty pattern (potentially)
>             pf2 = dPat0 p2 l 
>         in case (pf1, pf2) of 
>         { ([], []) -> [] 
>         ; ([], _ ) -> do 
>            { (p2', f2) <- pf2 -- we drop the sb1, because it reaches no state
>            ; let rm = extract p1
>            ; return (p2', (\i sb -> case sb of 
>                           { SPair sb1 sb2 cf -> 
>                              let sb1' = rm sb1 
>                              in carryForward (sb1'++cf) (f2 i sb2) }))
>            }
>         ; (_ , []) -> do 
>            { (p1', f1) <- pf1 
>            ; return ( PPair p1' p2, (\i sb -> case sb of 
>                           { SPair sb1 sb2 cf -> SPair (f1 i sb1) sb2 cf }))
>            }
>         ; (_, _) -> do
>            { (p1',f1) <- dPat0 p1 l 
>            ; (p2',f2) <- dPat0 p2 l
>            ; let rm = extract p1
>            ; return ( PChoice [PPair p1' p2, p2'] Greedy
>                     , (\i sb -> case sb of 
>                         { SPair sb1 sb2 cf -> 
>                            let sb1' = rm sb1
>                            in SChoice [ SPair (f1 i sb1) sb2 cf, carryForward (sb1'++cf) (f2 i sb2) ] [] -- TODO: we need to shift the sb1 to sb2 in the (f2 i sb2)
>                         } )
>                     ) }
>         }
>    else do { (p1',f1) <- dPat0 p1 l
>            ; return ( PPair p1' p2 
>                     , (\i sb -> case sb of 
>                         { SPair sb1 sb2 cf -> SPair (f1 i sb1) sb2 cf } )
>                     ) }
> dPat0 (PChoice ps g) l 
>    | null ps = []
>    | otherwise = 
>    let pfs = map (\p -> dPat0 p l) ps
>        nubPF :: [[(Pat, Int -> SBinder -> SBinder)]] -> [(Pat, Int -> SBinder -> SBinder)] 
>        nubPF pfs = nub2Choice pfs M.empty
>    in nubPF pfs 
> {-
>        pf2 = dPat0 p2 l         
>    in case (pf1,pf2) of 
>    { ([], []) -> [] 
>    ; ([], _ ) -> do 
>       { (p2', f2) <- pf2
>       ; return (p2', (\i sb -> case sb of 
>                      { SChoice [sb1,sb2] cf -> carryForward cf (f2 i sb2) }))
>       }
>    ; (_ , []) -> do 
>       { (p1', f1) <- pf1
>       ; return (p1', (\i sb -> case sb of 
>                      { SChoice [sb1,sb2] cf -> carryForward cf (f1 i sb1) }))
>       }
>    ; _ -> do   
>       { (p1',f1) <- pf1
>       ; (p2',f2) <- pf2
>       ; return (PChoice p1' p2' g, (\i sb ->                       
>              case sb of { SChoice [sb1,sb2] cf -> SChoice [f1 i sb1, f2 i sb2] cf }))
>       }
>    }
> -}


Turns a list of pattern x coercion pairs into a pchoice and a func, duplicate patterns are removed.

> nub2Choice :: [[(Pat, Int -> SBinder -> SBinder)]] -> M.Map Pat (Int -> SBinder -> SBinder) -> [(Pat, Int -> SBinder -> SBinder)] -- the return type is a singleton list.
> nub2Choice [] pDict = return (PChoice [] Greedy, (\i-> id)) -- the base case is the identity
> nub2Choice ([]:pfs) pDict = do 
>      { (PChoice ps g, f'') <- nub2Choice pfs pDict
>      ; let f' i sb = case sb of
>            { SChoice (s:ss) cf ->
>                 f'' i (SChoice ss cf)
>            ; _ -> error "nub2Choice coercion is applied to a non SChoice"
>            }
>      ; return (PChoice ps g, f')
>      }                                  
> nub2Choice ([(p,f)]:pfs) pDict  
>   | p `M.member` pDict = do 
>      { (PChoice ps g, f'') <- nub2Choice pfs pDict
>      ; let f' i sb = case sb of
>            { SChoice (s:ss) cf ->
>                 f'' i (SChoice ss cf)
>            ; _ -> error "nub2Choice coercion is applied to a non SChoice"
>            }
>      ; return (PChoice ps g, f')
>      }                                  
>   | otherwise = do   
>      { (PChoice ps g, f'') <- nub2Choice pfs (M.insert p f pDict)
>      ; let f' i sb = case sb of
>            { SChoice (s:ss) cf ->
>                let (SChoice ss' cf') = f'' i (SChoice ss cf)
>                in SChoice ((f i s):ss') cf'
>            ; _ -> error "nub2Choice coercion is applied to a non SChoice"
>            }
>      ; return (PChoice (p:ps) g, f')
>      }


> carryForward :: [SRange] -> SBinder -> SBinder
> carryForward sr (SVar (v, r) sb' cf) = SVar (v, r) sb' (cf++sr)
> carryForward sr (SRE cf) = SRE (cf++sr)
> carryForward sr (SStar cf) = SStar (cf++sr)
> carryForward sr (SPair sb1 sb2 cf) = SPair sb1 sb2 (cf++sr)
> carryForward sr (SChoice sbs cf) = SChoice sbs (cf++sr)
> carryForward sr sb2 = error ("trying to carry forward into a non-annotated pattern binder " ++ (show sb2))

> instance Ord Pat where
>   compare p1 p2 = compare (hash p1) (hash p2) -- todo: this is not safe.


> {-
> removeNonEmpty :: Pat -> SBinder -> SBinder                                           
> removeNonEmpty (PVar x w p) (SVar (_,b) sb cf) 
>       | posEpsilon (strip p) = SVar (x,b) (removeNonEmpty p sb) cf
>       | otherwise = SVar (x,[]) SRE cf
> removeNonEmpty (PE r) SRE = SRE
> removeNonEmpty (PStar p g) SStar = SStar 
> removeNonEmpty (PPair p1 p2) (SPair sb1 sb2) = SPair (removeNonEmpty p1 sb1) (removeNonEmpty p2 sb2) 
> removeNonEmpty (PChoice p1 p2 g) (SChoice [sb1, sb2]) = 
>       SChoice [removeNonEmpty p1 sb1, removeNonEmpty p2 sb2]
> -}

> extract :: Pat -> SBinder -> [SRange]
> extract (PVar x w p) (SVar (_,b) sb cf)
>      | posEpsilon (strip p) = (x,b):(extract p sb) ++ cf
>      | otherwise = [] -- cf?
> extract (PE r) (SRE cf) = cf
> extract (PStar p g) (SStar cf) = cf
> extract (PPair p1 p2) (SPair sb1 sb2 cf) = (extract p1 sb1) ++ (extract p2 sb2) ++ cf
> extract (PChoice ps g) (SChoice sbs cf) = (concatMap (\(p,sb) -> extract p sb) (zip ps sbs)) ++ cf


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



x0 :: (x1 :: ( x2 :: (ab|a), x3 :: (baa|a)), x4 :: (ac|c))

> p4 = PVar 0 [] (PPair (PVar 1 [] ((PPair p_x p_y))) p_z)
>    where p_x = PVar 2 [] (PE (Choice [(L 'A'),(Seq (L 'A') (L 'B'))] Greedy))      
>          p_y = PVar 3 [] (PE (Choice [(Seq (L 'B') (Seq (L 'A') (L 'A'))), (L 'A')] Greedy))
>          p_z = PVar 4 [] (PE (Choice [(Seq (L 'A') (L 'C')), (L 'C')] Greedy))


x0 :: ( x1 :: (  x2 :: (x3:: a | x4 :: ab) | x5 :: b)* )


> p3 = PVar 0 [] (PStar ( PVar 1 [] ( PChoice [(PVar 2 [] (PChoice [p3,p4] Greedy)), p5] Greedy)) Greedy)
>    where p3 = PVar 3 [] (PE (L 'A'))
>          p4 = PVar 4 [] (PE (Seq (L 'A') (L 'B')))           
>          p5 = PVar 5 [] (PE (L 'B'))