> {- By Kenny Zhuo Ming Lu and Martin Sulzmann, 2013, BSD License -}

A bytestring implementation of reg exp pattern matching using partial derivative / derivative
The POSIX matching policy is implemented by following the 'structure' of the reg-exp.
The pattern is follow annotated. 
We do not break part the sub-pattern of the original reg, they are always grouped under the same var pattern.


> {-# LANGUAGE GADTs, MultiParamTypeClasses, FunctionalDependencies,
>     FlexibleInstances, TypeSynonymInstances, FlexibleContexts #-} 


> module Text.Regex.PDeriv.ByteString.PosixEfficient
>     ( Regex
>     , CompOption(..)
>     , ExecOption(..)
>     , defaultCompOpt
>     , defaultExecOpt
>     , compile
>     , execute
>     , regexec
>     ) where 


> import System.IO.Unsafe


> import Data.List 
> import Data.Char (ord)
> import GHC.Int
> import GHC.Arr 
> import qualified Data.IntMap as IM
> import qualified Data.ByteString.Char8 as S
> import qualified Data.Map as M

> import Control.Monad

> import Text.Regex.Base(RegexOptions(..),RegexLike(..),MatchArray)


> import Text.Regex.PDeriv.RE 
> import Text.Regex.PDeriv.Common (IsPhi(..), IsEpsilon(..))
> import Text.Regex.PDeriv.Pretty (Pretty(..))
> import Text.Regex.PDeriv.Common (Range(..), Letter, PosEpsilon(..), my_hash, my_lookup, GFlag(..), IsGreedy(..), preBinder, subBinder, mainBinder)
> import Text.Regex.PDeriv.IntPattern (Pat(..), toBinder, Binder(..), strip, listifyBinder, Key(..))
> import Text.Regex.PDeriv.Parse
> import qualified Text.Regex.PDeriv.Dictionary as D (Dictionary(..), Key(..), insertNotOverwrite, lookupAll, empty, isIn, nub)



> logger io = unsafePerformIO io

> type SRange = (Int,[Range])

> type CarryForward = IM.IntMap [Range] -- we only keep the first choice (i.e. the posix)  hence it is always mapping one variable to one env
> emptyCF = IM.empty

> combineCF :: CarryForward -> CarryForward -> CarryForward
> combineCF cf1 cf2 = IM.unionWith combineRange cf1 cf2

> combineRange :: [Range] -> [Range] -> [Range]
> combineRange [] rs2 = rs2
> combineRange rs1 [] = rs1
> combineRange ((r1@(Range b1 e1)):rs1) ((r2@(Range b2 e2)):rs2) 
>   | b1 == b2 && e1 >= e2 = (Range b1 e1):(combineRange rs1 rs2)
>   | b1 == b2 && e2 >= e1 = (Range b2 e2):(combineRange rs1 rs2)
>   | b1 == e2+1 = (Range b2 e1):(combineRange rs1 rs2)
>   | b2 == e1+1 = (Range b1 e2):(combineRange rs1 rs2)
>   | b1 > e2+1 = (Range b2 e2):(combineRange (r1:rs1) rs2)
>   | b2 > e1+1 = (Range b1 e1):(combineRange rs1 (r2:rs2))
>   | otherwise = error $ "unhandle combineRange:" ++ show (r1:rs1) ++ " vs " ++ show (r2:rs2)

> combineCFs :: [CarryForward] -> CarryForward 
> combineCFs cfs = foldl' (\cf1 cf2 -> cf1 `combineCF` cf2) emptyCF cfs

> insertCF :: SRange -> CarryForward -> CarryForward 
> insertCF (x,r) cf = IM.insert x r cf


> data SBinder = SChoice [SBinder] CarryForward                
>           | SPair SBinder SBinder CarryForward              
>           | SVar SRange SBinder CarryForward
>           | SStar CarryForward -- no need to store any SBinder, but 
>           | SRE CarryForward
>    deriving Show

> toSBinder :: Pat -> SBinder
> toSBinder (PVar x w p) = SVar (x,[]) (toSBinder p) emptyCF
> toSBinder (PE rs) = SRE emptyCF
> toSBinder (PStar p g) = SStar emptyCF
> toSBinder (PPair p1 p2) = SPair (toSBinder p1) (toSBinder p2) emptyCF
> toSBinder (PChoice ps g) = SChoice (map toSBinder ps) emptyCF



The invariance: 
The shapes of the input/output Pat and SBinder should be identical.




> dPat0 :: Pat -> Char -> [(Pat, Int -> SBinder -> SBinder)] -- the result is always singleton or empty
> dPat0 y@(PVar x w p) l = 
>    do { (p',f) <- dPat0 p l  
>       ; let f' i sb = case sb of 
>                       { SVar (v,r) sb' cf -> SVar (v, updateRange i r) (f i sb') cf 
>                       ; senv -> error $ "invariance is broken: " ++ show y ++ " vs " ++ show senv 
>                       }
>       ; (p'',f'') <- simpFix (PVar x w p')
>       ; if (p'' == (PVar x w p')) 
>         then return (PVar x w p', f')
>         else return (p'', \i -> (f'' i) . (f' i))
>       }
> dPat0 (PE rs) l = 
>    let pds = nub (concatMap (\r -> partDeriv r l) rs)
>    in pds `seq` 
>       if null pds then mzero
>       else return (PE pds, (\_ -> id) )
> dPat0 (PStar p g) l = 
>    do { (p', f) <- dPat0 p l        
>       ; let emp = toSBinder p                     
>       ; return (PPair p' (PStar p g), (\i sb -> 
>                     case sb of { SStar cf -> SPair (f i emp) sb cf} ) ) 
>       }
> dPat0 (PPair p1 p2) l 
>    | (posEpsilon (strip p1)) =
>       let pf1 = dPat0 p1 l                           
>           pf2 = dPat0 p2 l
>       in case (pf1, pf2) of
>       { ([], []) -> mzero
>       ; ([], [(p2',f2')]) ->
>          let rm = extract p1
>              f i sb = case sb of 
>                 { SPair sb1 sb2 cf -> 
>                      let sb1' = rm sb1  
>                      in carryForward (combineCF sb1' cf) (f2' i sb2) }
>          in do { (p2'',f2'') <- simpFix p2'
>                ; if p2'' == p2'
>                  then return (p2', f)
>                  else return (p2'', \i -> (f2'' i) . (f i))
>                }
>       ; ([(p1',f1')], []) -> -- todo
>          let f i sb = case sb of 
>                 { SPair sb1 sb2 cf -> SPair (f1' i sb1) sb2 cf }
>          in do { (p1'',f1'') <- simpFix (PPair p1' p2)
>                ; if (p1'' == (PPair p1' p2))
>                  then return (PPair p1' p2, f)
>                  else return (p1'', \i -> (f1'' i) . (f i)) 
>                }
>       ; _ | {- True -> do -} isGreedy p1 -> do 
>         { (p1',f1) <- dPat0 p1 l
>         ; (p2',f2) <- dPat0 p2 l
>         ; let rm = extract p1
>               f i sb = case sb of
>                 { SPair sb1 sb2 cf ->
>                     let sb1' = rm sb1
>                     in SChoice [ SPair (f1 i sb1) sb2 cf, carryForward (sb1' `combineCF` cf) (f2 i sb2)] emptyCF }
>         ; (p',f') <- simpFix (PChoice [PPair p1' p2, p2'] Greedy) 
>         ; if (p' == (PChoice [PPair p1' p2, p2'] Greedy))
>           then return (PChoice [PPair p1' p2, p2'] Greedy, f)
>           else return (p', \i -> (f' i) . (f i))          
>         }
>           | otherwise -> do 
>         { (p1',f1) <- dPat0 p1 l
>         ; (p2',f2) <- dPat0 p2 l
>         ; let rm = extract p1
>               f i sb = case sb of
>                 { SPair sb1 sb2 cf ->
>                     let sb1' = rm sb1
>                     in SChoice [carryForward (sb1' `combineCF` cf) (f2 i sb2),  SPair (f1 i sb1) sb2 cf ] emptyCF }
>         ; (p',f') <- simpFix (PChoice [p2' , PPair p1' p2] Greedy) 
>         ; if (p' == (PChoice [p2' , PPair p1' p2] Greedy))
>           then return (PChoice [p2' , PPair p1' p2] Greedy, f)
>           else return (p', \i -> (f' i) . (f i))          
>         }
>       }
>    | otherwise =
>       do { (p1',f1) <- dPat0 p1 l
>          ; let f i sb = case sb of { SPair sb1 sb2 cf -> SPair (f1 i sb1) sb2 cf } 
>          ; (p',f') <- simpFix (PPair p1' p2)
>          ; if (p' == (PPair p1' p2))
>            then return (PPair p1' p2, f)
>            else return (p', \i -> (f' i) . (f i))
>          }
> dPat0 (PChoice [] g) l = mzero
> dPat0 y@(PChoice [p] g) l = do
>       { (p',f') <- dPat0 p l
>       ; let f i sb = case sb of { SChoice [sb'] cf -> carryForward cf (f' i sb') 
>                                 ; senv -> error $ "invariance is broken: " ++ pretty y ++ " vs "  ++ show senv 
>                                 }
>       ; (p'',f'') <- simpFix p'
>       ; if (p'' == p')
>         then return (p', f)
>         else return (p'', \i -> (f'' i) . (f i))                     
>       }
> dPat0 (PChoice ps g) l = 
>    let pfs = map (\p -> dPat0 p l) ps
>        nubPF :: [[(Pat, Int -> SBinder -> SBinder)]] -> [(Pat, Int -> SBinder -> SBinder)] 
>        nubPF pfs = nub2Choice pfs M.empty 
>    in do 
>    { (p,f) <- nubPF pfs
>    ; (p',f') <- simpFix p
>    ; if (p' == p) 
>      then return (p, f)
>      else return (p', \i -> (f' i) . (f i)) 
>    }

Turns a list of pattern x coercion pairs into a pchoice and a func, duplicate patterns are removed.
The first arg is a list of list of pair, because of the list monad generated by dPat0, each non-empty sub list is a singleton list.
The resulting func accept a SChoice pattern (cf to the input list of pattern). 


-----------------------------------
{}, d |-nub PChoice {}, \i -> id


pfs .... todo
--------------------------------------------
{[]}\cup pfs , d |-nub PChoice {}, \i -> id

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
> nub2Choice ([(p,f)]:pfs) pDict  -- recall the invarance of nub2Choice and dPat0, the return value of f shares the same shape of p
>   | isPhi (strip p) || p `M.member` pDict = do  -- simplification
>      { (PChoice ps g, f'') <- nub2Choice pfs pDict
>      ; let f' i sb = case sb of
>            { SChoice (s:ss) cf ->
>                 f'' i (SChoice ss cf)
>            ; _ -> error "nub2Choice coercion is applied to a non SChoice"
>            }
>      ; return (PChoice ps g, f')
>      } 
>   | otherwise = 
>     case p of 
>       { PChoice ps' g' -> do 
>         { let fs' :: [Int -> SBinder -> SBinder]
>               fs' = repeat (\i -> id) --  identity functions
>         ; (p', f'') <- nub2Choice ((map (\x -> [x]) (zip ps' fs'))++pfs) pDict -- todo
>         ; let f' i sb = case sb of  
>                         { (SChoice (s:ss) cf) ->
>                             case (f i s) of
>                             { SChoice ss'' cf' -> let ss''' = map (\x -> carryForward cf' x) ss''
>                                                   in f'' i (SChoice (ss''' ++ ss) cf) 
>                             ; _ -> error "nub2Choice coercion is applied to a non SChoice" }
>                         ;  _ -> error "nub2Choice coercion is applied to a non SChoice" }
>         ; return (p', f')
>         }
>       ; _ ->   
>         do
>         { (PChoice ps g, f'') <- nub2Choice pfs (M.insert p f pDict)
>         ; let f' i sb = case sb of
>                         { SChoice (s:ss) cf ->
>                              let (SChoice ss' cf') = f'' i (SChoice ss cf)
>                              in SChoice ((f i s):ss') cf'
>                         ; _ -> error "nub2Choice coercion is applied to a non SChoice"
>                         }
>         ; return (PChoice (p:ps) g, f')
>         }
>       }

simplification

> {-
> simplify :: [(Pat, Int -> SBinder -> SBinder)] -> [(Pat, Int -> SBinder -> SBinder)]
> simplify [] = []
> simplify pfs@[(PPair p1 p2, f)] 
>   | (isPhi (strip p1)) || (isPhi (strip p2)) = [] 
> {-   | (isEpsilon (strip p1)) =
>        let rm = extract p1
>            f i sb = case sb of { SPair sb1 sb2 cf -> let cf' = rm sb1 in carryForward (cf'++cf) sb2 }
>        in [(p2,f)]
>   | (isEpsilon (strip p2)) =
>        let rm = extract p2
>            f i sb = case sb of { SPair sb1 sb2 cf -> let cf' = rm sb2 in carryForward (cf'++cf) sb1 }
>        in [(p1,f)] -}
>   | otherwise = pfs
> simplify pfs = pfs
> -}

> simpFix :: Pat -> [(Pat, Int -> SBinder -> SBinder)]
> simpFix p =  simp p -- simpFix' p (\i -> id)

> simpFix' p f = 
>   case simp p of
>   { [] -> []  
>   ; [(p',f')] ->
>      if p' == p
>      then [(p,f)]
>      else simpFix' p' (\i -> (f' i) . (f i))
>   }


invariance: input / outoput of Int -> SBinder -> SBinder agree with simp's Pat input/ output

> simp :: Pat -> [(Pat, Int -> SBinder -> SBinder)] -- the output list is singleton 
> simp (PVar x w p) = do
>   { (p',f') <- simp p
>   ; case p' of
>     { _ | p == p' -> return (PVar x w p,\i -> id)
>         | isPhi (strip p') -> mzero
>         | otherwise -> let f i sb = case sb of 
>                                     {SVar vr sb' cf -> SVar vr (f' i sb') cf}
>                        in return (PVar x w p', f)
>     }
>   }
> simp y@(PPair p1 p2) = do
>    { (p1',f1') <- simp p1
>    ; (p2',f2') <- simp p2
>    ; case (p1',p2') of       
>      { _ | isPhi p1' || isPhi p2' -> mzero
>          | isEpsilon p1'          -> 
>              let rm = extract p1
>                  f i sb = case sb of
>                     { SPair sb1 sb2 cf -> let cf' = rm sb1 in carryForward (cf' `combineCF` cf) (f2' i sb2) }
>              in return (p2',f)
>          | isEpsilon p2'          ->
>              let rm = extract p2
>                  f i sb = case sb of 
>                     { SPair sb1 sb2 cf -> let cf' = rm sb2 in carryForward (cf' `combineCF` cf) (f1' i sb1) }
>              in return (p1',f)
>          | otherwise              ->
>              let f i sb = case sb of
>                     { SPair sb1 sb2 cf -> SPair (f1' i sb1) (f2' i sb2) cf
>                     ; senv -> error $ "invariance broken: " ++ pretty y ++ " vs " ++ show senv }
>              in return (PPair p1' p2', f)
>       }
>    }
> simp (PChoice [] g) = mzero
> simp (PChoice [p] g) = do 
>    { (p',f') <- simp p
>    ; if isPhi p' 
>      then mzero
>      else 
>       let f i sb = case sb of { SChoice [sb'] cf -> carryForward cf (f' i sb') }
>       in return (p',f)
>    }
> simp (PChoice ps g) = 
>    let pfs = map simp ps  
>        nubPF :: [[(Pat, Int -> SBinder -> SBinder)]] -> [(Pat, Int -> SBinder -> SBinder)] 
>        nubPF pfs = nub2Choice pfs M.empty
>    in nubPF pfs
> simp p = return (p,\i -> id)


> carryForward :: CarryForward -> SBinder -> SBinder
> carryForward sr (SVar (v, r) sb' cf) = SVar (v, r) sb' $ combineCF cf sr
> carryForward sr (SRE cf) = SRE $ combineCF cf sr
> carryForward sr (SStar cf) = SStar $ combineCF cf sr
> carryForward sr (SPair sb1 sb2 cf) = SPair sb1 sb2 $ combineCF cf sr
> carryForward sr (SChoice sbs cf) = SChoice sbs $ combineCF cf sr
> carryForward sr sb2 = error ("trying to carry forward into a non-annotated pattern binder " ++ (show sb2))



> instance Ord Pat where
>   compare (PVar x1 _ p1) (PVar x2 _ p2) 
>      | x1 == x2 = compare p1 p2
>      | otherwise = compare x1 x2
>   compare (PE r1) (PE r2) = compare r1 r2 
>   compare (PStar p1 _) (PStar p2 _) = compare p1 p2 
>   compare (PPair p1 p2) (PPair p3 p4) = let r = compare p1 p3 in case r of 
>      { EQ -> compare p2 p4
>      ; _  -> r }
>   compare (PChoice ps1 _) (PChoice ps2 _) = 
>      compare ps1 ps2
>   compare p1 p2 = compare (assignInt p1) (assignInt p2) 
>     where assignInt (PVar _ _ _) = 0
>           assignInt (PE _) = 1
>           assignInt (PStar _ _) = 2
>           assignInt (PPair _ _) = 3
>           assignInt (PChoice _ _) = 4


extract a carry foward from the sbinder

> extract :: Pat -> SBinder -> CarryForward
> extract (PVar x w p) (SVar (_,b) sb cf)
>      | posEpsilon (strip p) = (insertCF (x,b) (extract p sb)) `combineCF` cf
>      | otherwise = IM.empty -- cf?
> extract (PE rs) (SRE cf) = cf
> extract (PStar p g) (SStar cf) = cf
> extract (PPair p1 p2) (SPair sb1 sb2 cf) = (extract p1 sb1) `combineCF` (extract p2 sb2) `combineCF` cf
> extract (PChoice ps g) (SChoice sbs cf) = (combineCFs $ map (\(p,sb) -> extract p sb) (zip ps sbs)) `combineCF` cf
> extract p sb = error $ "Error: trying to extract" ++ (show sb) ++ " from " ++ (show p)


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
>      ; (p',f) <- dPat0 p (fst l)
>      ; matchInner [(p', f (snd l) sb)] ls 
>      }


> type Env = [SRange]

> match :: Pat -> [Char] -> [Env]
> match p w = do { (p',sb) <- matchInner [(p, toSBinder p)] (zip w [1..])  
>                ; sbinderToEnv p' sb }

> posixMatch :: Pat -> [Char] -> Maybe Env
> posixMatch p w = case match p w of
>   { (e:_) -> Just e ; _ -> Nothing }


> match2 :: (Pat,FollowBy,IM.IntMap()) -> [Char] -> [MatchArray]
> match2 (p,fb,posixBinder) w = 
>   map (\env -> sbinderToMatchArray (length w) fb posixBinder (IM.fromList env)) (match p w)


get all envs from the sbinder

> sbinderToEnv :: Pat -> SBinder -> [Env]
> sbinderToEnv p sb = 
>   let envs = sbinderToEnv' p sb
>   in map sortEnvByVar envs

> sbinderToEnv' :: Pat -> SBinder -> [Env]
> sbinderToEnv' _ (SChoice [] _) = []
> sbinderToEnv' (PChoice (p:ps) g) (SChoice (sb:sbs) cf) 
>   | posEpsilon (strip p) = 
>   do { env <- sbinderToEnv' p sb
>      ; return (env ++ (IM.toList cf)) }
>   | otherwise = sbinderToEnv' (PChoice ps g) (SChoice sbs cf)
> sbinderToEnv' (PPair p1 p2) (SPair sb1 sb2 cf) =
>   do { e1 <- sbinderToEnv' p1 sb1 
>      ; e2 <- sbinderToEnv' p2 sb2
>      ; return (e1 ++ e2) }
> sbinderToEnv' (PVar x _ p) (SVar sr sb cf) 
>   | posEpsilon (strip p) = do { env <- sbinderToEnv' p sb
>                       ; return ((sr:env) ++ (IM.toList cf)) }
>   | otherwise = []
> sbinderToEnv' (PStar _ _) (SStar cf) = [IM.toList cf]
> sbinderToEnv' (PE _) (SRE cf) = [IM.toList cf]
> sbinderToEnv' p sb = error $ (pretty p) ++ " and " ++ (show sb)


> sortEnvByVar :: Env -> Env 
> sortEnvByVar env = let im = sortEnvByVar' env IM.empty 
>                    in map (\(i,rs) -> (i, nub (sort rs) )) (IM.toList im)

> sortEnvByVar' :: Env -> IM.IntMap [Range] -> IM.IntMap [Range]
> sortEnvByVar' [] im = im
> sortEnvByVar' ((i,rs):srgs) im = 
>    case IM.lookup i im of 
>     { Just _ -> let im' = IM.update (\rs' -> Just $ rs ++ rs') i im
>                 in sortEnvByVar' srgs im' 
>     ; Nothing -> sortEnvByVar' srgs (IM.insert i rs im) }  


> type DfaTable = IM.IntMap (Int, Int -> SBinder -> SBinder, SBinder -> [Env])


> compilePat :: Pat -> (DfaTable,SBinder, SBinder -> [Env], [Int])
> compilePat p = let (t, sb, toEnv, finals) = buildDfaTable p 
>                in (t, sb, toEnv, finals)


> buildDfaTable :: Pat -> (DfaTable, SBinder, SBinder -> [Env], [Int])
> buildDfaTable p = 
>   let sig = sigmaRE (strip p)
>       init_dict = M.insert p 0 M.empty        
>       (allStates, delta, mapping) = builder sig [] [] init_dict 0 [p] -- 0 is already used by p
>       pat2id p = case M.lookup p mapping of 
>              { Just i -> i 
>              ; Nothing -> error ("pattern not found, this should not happen." ++ (show p) ++ (show (M.toList mapping))) }
>       delta' = map (\ (s,c,d,f) -> (pat2id s, c, pat2id d, f, sbinderToEnv d) ) delta
>       table = IM.fromList (map (\ (s,c,d,f,sb2env) -> (my_hash s c, (d,f,sb2env))) delta')
>       finals = map pat2id (filter (\p -> posEpsilon (strip p) ) allStates)
>   in (table, toSBinder p, sbinderToEnv p, finals)

testing 

> testp = 
>    let (Right (pp,posixBnd)) = parsePatPosix "X(.?){0,4}Y"
>    in pp


> testp2 = 
>    let (Right (pp,posixBnd)) = parsePatPosix "X(.?){0,4}Y"
>        fb                    = followBy pp
>    in (pp,fb,posixBnd)


let sig = sigmaRE (strip testp)
let init_dict = M.insert testp (0::Int) M.empty
let (allStates, delta, mapping) = builder sig [] [] init_dict (0::Int) [testp]
mapM_ (\p -> putStrLn (show p)) (sort allStates)

> {-
> f p = 
>   let sig = sigmaRE (strip p)
>       init_dict = M.insert p 0 M.empty        
>      f (allStates, delta, mapping) = builder sig [] [] init_dict 0 [p]
>       pat2id p = case M.lookup p mapping of 
>              { Just i -> i 
>              ; Nothing -> error "pattern not found, this should not happen." }
>       delta' = map (\ (s,c,d,f) -> (pat2id s, c, pat2id d, f, sbinderToEnv d) ) delta
>       table = IM.fromList (map (\ (s,c,d,f,sb2env) -> (my_hash s c, (d,f,sb2env))) delta')
>   in (map (\p -> (p, pat2id p)) allStates) -- (table, allStates, delta, delta')
> -}

> builder :: [Char] 
>         -> [Pat] 
>         -> [ (Pat,Char,Pat,Int -> SBinder -> SBinder) ] 
>         -> M.Map Pat Int
>         -> Int
>         -> [Pat]
>         -> ([Pat], [ (Pat,Char,Pat,Int -> SBinder -> SBinder) ], M.Map Pat Int)
> builder sig acc_pats acc_delta dict max_id curr_pats 
>    | null curr_pats = (acc_pats, acc_delta, dict)
>    | otherwise = 
>       let all_sofar_pats = acc_pats ++ curr_pats
>       --    io             = logger (print all_sofar_pats)
>           new_delta      = [ (p,l,p',f') | p <- curr_pats, l <- sig, (p',f') <- dPat0 p l  ]
>           new_pats       = D.nub [ p' | (p,l,p',f') <- new_delta, not (p' `M.member` dict) ]
>           acc_delta_next = acc_delta ++ new_delta
>           (dict',max_id') = foldl' (\(d,id) p -> (M.insert p (id+1) d, id + 1)) (dict,max_id) new_pats
>       in {- io `seq` -} builder sig all_sofar_pats acc_delta_next dict' max_id' new_pats     

> type Word = S.ByteString

> execDfa :: Int -> DfaTable -> Word -> [(Int, SBinder, SBinder -> [Env])] -> [(Int,SBinder, SBinder -> [Env])] -- the list is always singleton, since it is a dfa
> execDfa cnt dfaTable w' [] = []
> execDfa cnt dfaTable w' currDfaStateSBinders = 
>      case S.uncons w' of
>        Nothing -> currDfaStateSBinders
>        Just (l,w) -> 
>           let ((i,sb,_):_) = currDfaStateSBinders
>               k              = my_hash i l
>           in case IM.lookup k dfaTable of
>               { Nothing -> [] -- error (" k not found " ++ show i ++ " " ++  show l)
>               ; Just (j, f, sb2env) -> 
>                  let sb' = cnt `seq` sb `seq` f cnt sb
>                      nextDfaStateSBinders =  [(j, sb',sb2env)] 
>                      cnt' = cnt + 1
>                  in nextDfaStateSBinders `seq` cnt' `seq` w `seq` 
>                     execDfa cnt' dfaTable w nextDfaStateSBinders
>               }

x0 :: (x1 :: ( x2 :: (ab|a), x3 :: (baa|a)), x4 :: (ac|c))

> execPatMatch :: (DfaTable, SBinder, SBinder -> [Env], [Int], FollowBy, IM.IntMap ()) -> Word -> Maybe Env
> execPatMatch (dt, init_sbinder, init_sb2env, finals, _, posixBinder) w = 
>   let r = execDfa 0 dt w [(0, init_sbinder, init_sb2env)]
>   in case r of 
>    { [] -> Nothing 
>    ; ((i,sb,sb2env):_) -> case (sb2env sb) of -- todo: check i `elem` finals?
>                           { [] -> Nothing 
>                           ; (e:_) -> let e' = filter (\(x,_) -> x  `IM.notMember` posixBinder) e 
>                                      in Just e'
>                           } }


> p4 = PVar 0 [] (PPair (PVar 1 [] ((PPair p_x p_y))) p_z)
>    where p_x = PVar 2 [] (PE [(Choice [(L 'A'),(Seq (L 'A') (L 'B'))] Greedy)])      
>          p_y = PVar 3 [] (PE [(Choice [(Seq (L 'B') (Seq (L 'A') (L 'A'))), (L 'A')] Greedy)])
>          p_z = PVar 4 [] (PE [(Choice [(Seq (L 'A') (L 'C')), (L 'C')] Greedy)])


x0 :: ( x1 :: (  x2 :: (x3:: a | x4 :: ab) | x5 :: b)* )


> p3 = PVar 0 [] (PStar ( PVar 1 [] ( PChoice [(PVar 2 [] (PChoice [p3,p4] Greedy)), p5] Greedy)) Greedy)
>    where p3 = PVar 3 [] (PE [(L 'A')])
>          p4 = PVar 4 [] (PE [(Seq (L 'A') (L 'B'))])           
>          p5 = PVar 5 [] (PE [(L 'B')])


> -- | The PDeriv backend spepcific 'Regex' type
> -- | the IntMap keeps track of the auxillary binder generated because of posix matching, i.e. all sub expressions need to be tag
> -- | the FollowBy keeps track of the order of the pattern binder 
> type Regex = (DfaTable, SBinder, SBinder -> [Env], [Int], FollowBy, IM.IntMap ())


-- todo: use the CompOption and ExecOption

> compile :: CompOption -- ^ Flags (summed together)
>         -> ExecOption -- ^ Flags (summed together) 
>         -> S.ByteString -- ^ The regular expression to compile
>         -> Either String Regex -- ^ Returns: the compiled regular expression
> compile compOpt execOpt bs =
>     case parsePatPosix (S.unpack bs) of
>     Left err -> Left ("parseRegex for Text.Regex.PDeriv.ByteString failed:"++show err)
>     Right (pat,posixBnd) -> 
>        Right (patToRegex pat posixBnd compOpt execOpt)


> patToRegex p posixBnd compOpt execOpt  =  
>     let (t, sb, toEnv, finals) = compilePat p
>         fb = followBy p
>     in (t, sb, toEnv, finals, fb, posixBnd)



> execute :: Regex      -- ^ Compiled regular expression
>        -> S.ByteString -- ^ ByteString to match against
>        -> Either String (Maybe Env)
> execute r bs = Right (execPatMatch r bs)

> regexec :: Regex      -- ^ Compiled regular expression
>        -> S.ByteString -- ^ ByteString to match against
>        -> Either String (Maybe (S.ByteString, S.ByteString, S.ByteString, [S.ByteString]))
> regexec r bs =
>  case execPatMatch r bs of
>    Nothing -> Right Nothing
>    Just env ->
>      let pre = case lookup preBinder env of { Just e -> rg_collect_many bs e ; Nothing -> S.empty }
>          post = case lookup subBinder env of { Just e -> rg_collect_many bs e ; Nothing -> S.empty }
>          full_len = S.length bs
>          pre_len = S.length pre
>          post_len = S.length post
>          main_len = full_len - pre_len - post_len
>          main_and_post = S.drop pre_len bs
>          main = main_and_post `seq` main_len `seq` S.take main_len main_and_post
>          matched = map ((rg_collect_many bs) . snd) (filter (\(v,w) -> v > mainBinder && v < subBinder ) env)
>      in -- logger (print (show env)) `seq` 
>             Right (Just (pre,main,post,matched))

> rg_collect :: S.ByteString -> Range -> S.ByteString
> rg_collect w (Range i j) = S.take (j' - i' + 1) (S.drop i' w)
>	       where i' = fromIntegral i
>	             j' = fromIntegral j

> rg_collect_many w rs = foldl' S.append S.empty $ map (rg_collect w) rs


> -- | Control whether the pattern is multiline or case-sensitive like Text.Regex and whether to
> -- capture the subgroups (\1, \2, etc).  Controls enabling extra anchor syntax.
> data CompOption = CompOption {
>       caseSensitive :: Bool    -- ^ True in blankCompOpt and defaultCompOpt
>     , multiline :: Bool 
>   {- ^ False in blankCompOpt, True in defaultCompOpt. Compile for
>   newline-sensitive matching.  "By default, newline is a completely ordinary
>   character with no special meaning in either REs or strings.  With this flag,
>   inverted bracket expressions and . never match newline, a ^ anchor matches the
>   null string after any newline in the string in addition to its normal
>   function, and the $ anchor matches the null string before any newline in the
>   string in addition to its normal function." -}
>     , rightAssoc :: Bool       -- ^ True (and therefore Right associative) in blankCompOpt and defaultCompOpt
>     , newSyntax :: Bool        -- ^ False in blankCompOpt, True in defaultCompOpt. Add the extended non-POSIX syntax described in "Text.Regex.TDFA" haddock documentation.
>     , lastStarGreedy ::  Bool  -- ^ False by default.  This is POSIX correct but it takes space and is slower.
>                                -- Setting this to true will improve performance, and should be done
>                                -- if you plan to set the captureGroups execoption to False.
>     } deriving (Read,Show)

> data ExecOption = ExecOption  {
>   captureGroups :: Bool    -- ^ True by default.  Set to False to improve speed (and space).
>   } deriving (Read,Show)

> instance RegexOptions Regex CompOption ExecOption where
>     blankCompOpt =  CompOption { caseSensitive = True
>                                , multiline = False
>                                , rightAssoc = True
>                                , newSyntax = False
>                                , lastStarGreedy = False
>                                  }
>     blankExecOpt =  ExecOption { captureGroups = True }
>     defaultCompOpt = CompOption { caseSensitive = True
>                                 , multiline = True
>                                 , rightAssoc = True
>                                 , newSyntax = True
>                                 , lastStarGreedy = False
>                                   }
>     defaultExecOpt =  ExecOption { captureGroups = True }
>     setExecOpts e r = undefined
>     getExecOpts r = undefined 



> instance RegexLike Regex S.ByteString where 
> -- matchAll :: regex -> source -> [MatchArray]
>    matchAll = execPatMatchArray
> -- matchOnce :: regex -> source -> Maybe MatchArray
>    matchOnce = posixPatMatchArray
> -- matchCount :: regex -> source -> Int
> -- matchTest :: regex -> source -> Bool
> -- matchAllText :: regex -> source -> [MatchText source]
> -- matchOnceText :: regex -> source -> Maybe (source, MatchText source, source)
>     

> instance RegexLike Regex String where 
> -- matchAll :: regex -> source -> [MatchArray]
>    matchAll r s = execPatMatchArray r (S.pack s)
> -- matchOnce :: regex -> source -> Maybe MatchArray
>    matchOnce r s = posixPatMatchArray r (S.pack s)
> -- matchCount :: regex -> source -> Int
> -- matchTest :: regex -> source -> Bool
> -- matchAllText :: regex -> source -> [MatchText source]
> -- matchOnceText :: regex -> source -> Maybe (source, MatchText source, source)




> execPatMatchArray ::  (DfaTable, SBinder, SBinder -> [Env], [Int], FollowBy, IM.IntMap ()) -> Word -> [MatchArray]
> execPatMatchArray (dt, init_sbinder, init_sb2env, finals, fb, posixBinder)  w =
>   let r = execDfa 0 dt w [(0, init_sbinder, init_sb2env)]
>   in case r of 
>    { [] -> [] 
>    ; ((i,sb,sb2env):_) -> map (\ env -> sbinderToMatchArray (S.length w) fb posixBinder (IM.fromList env)) (sb2env sb) 
>    }

> updateEmptyBinder b fb = 
>     let 
>         up b (x,y) = case IM.lookup x b of 
>                      { Just (_:_) -> -- non-empty, nothing to do
>                        b
>                      ; Just [] ->  -- lookup the predecessor
>                        case IM.lookup y b of
>                        { Just r@(_:_) -> let i = snd (last r)
>                                          in IM.update (\_ -> Just [(i,i)]) x b
>                        ; _ -> b }
>                      ; Nothing -> b }
>     in foldl' up b fb

> sbinderToMatchArray l fb posixBnd b  = 
>     let -- b'        = updateEmptyBinder b fb
>         subPatB   = filter (\(x,_) -> x > mainBinder && x < subBinder && x `IM.notMember` posixBnd ) (listifyBinder b)
>         mbPrefixB = IM.lookup preBinder b
>         mbSubfixB = IM.lookup subBinder b
>         mainB     = case (mbPrefixB, mbSubfixB) of
>                       (Just [(Range _ x)], Just [(Range y _)]) -> (x, y - x)
>                       (Just [(Range _ x)], _)            -> (x, l - x)
>                       (_, Just [(Range y _)])            -> (0, y) 
>                       (_, _)                       -> (0, l)
>                       _                            -> error (show (mbPrefixB, mbSubfixB) ) 
>         rs        = map snd subPatB      
>         rs'       = map lastNonEmpty rs
>         io = logger (print $ "\n" ++ show rs ++ " || " ++ show rs' ++ "\n")
>     in -- io `seq` 
>        listToArray (mainB:rs')
>     where fromRange (Range b e) = (b, e-b+1) 
>           -- chris' test cases requires us to get the last result even if it is a reset point,
>           -- e.g. input:"aaa"	 pattern:"((..)|(.))*" expected match:"(0,3)(2,3)(-1,-1)(2,3)" note that (..) matches with [(0,2),(2,2)], we return [(2,2)]
>           lastNonEmpty [] = (-1,0)
>           lastNonEmpty rs = fromRange (last rs)

> listToArray l = listArray (0,length l-1) l

> posixPatMatchArray :: (DfaTable, SBinder, SBinder -> [Env], [Int], FollowBy, IM.IntMap ()) -> Word -> Maybe MatchArray
> posixPatMatchArray compiled w =
>      first (execPatMatchArray compiled w)
>   where
>     first (env:_) = return env
>     first _ = Nothing


> -- | from FollowBy, we recover the right result of the variable that bound (-1,-1) to fit Chris' test case
> 

> type FollowBy = [(Int,Int)]

> followBy :: Pat -> FollowBy
> followBy p = map (\p -> (snd p, fst p)) (fst $ buildFollowBy p ([],[]))

> -- | describe the "followedBy" relation between two pattern variable
> buildFollowBy :: Pat -> ([(Int,Int)], [Int]) -> ([(Int,Int)], [Int])
> buildFollowBy (PVar x w p) (acc, lefts) = let (acc', lefts') = buildFollowBy p (acc,lefts)
>                                           in ([ (l,x) | l <- lefts] ++ acc', [x])
> buildFollowBy (PE r) x                  = x
> buildFollowBy (PStar p g) (acc, lefts)  = buildFollowBy p (acc,lefts)
> buildFollowBy (PPair p1 p2) (acc, lefts) = let (acc',lefts') = buildFollowBy p1 (acc,lefts)
>                                            in buildFollowBy p2 (acc',lefts')
> buildFollowBy (PChoice ps _) (acc, lefts) = 
>   foldl' (\(acc', lefts') p -> let (acc'', lefts'') = buildFollowBy p (acc',lefts) -- all choice share the same lefts comming from the parent
>                               in (acc'', lefts' ++ lefts'')) (acc, []) ps
