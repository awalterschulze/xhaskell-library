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
                   
> dPat0 :: Pat -> Char -> [(Pat, Int -> SBinder -> SBinder)]  -- the lists are always singleton,
> dPat0 (PVar x w p) l = 
>    do { (p',f) <- dPat0 p l
>       ; return (PVar x [] p', (\i sb -> 
>                              case sb of 
>                              { SVar (v, r) sb' cf -> SVar (v, updateRange i r) (f i sb') cf
>                              ; _ -> error ("dPat0 failed with pattern " ++ (show (PVar x w p))  ++ " and binding " ++ (show sb))
>                              }) ) }

> dPat0 (PE r) l =
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
>                            in SChoice [ SPair (f1 i sb1) sb2 cf, carryForward (sb1'++cf) (f2 i sb2) ] [] -- we shift the sb1 to sb2 in the (f2 i sb2)
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
>    | length ps == 1 = do -- singleton choice, we eliminate the choice
>       { p <- ps  
>       ; (p',f) <- dPat0 p l                
>       ; let f' = \i sb -> case sb of { SChoice [sb'] cf -> carryForward cf (f i sb')  }
>       ; return (p', f')
>       }  
>    | otherwise = 
>    let pfs = map (\p -> dPat0 p l) ps
>        nubPF :: [[(Pat, Int -> SBinder -> SBinder)]] -> [(Pat, Int -> SBinder -> SBinder)] 
>        nubPF pfs = nub2Choice pfs M.empty 
>    in nubPF pfs 


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
>   compare (PVar x1 _ p1) (PVar x2 _ p2) 
>      | x1 == x2 = compare p1 p2
>      | otherwise = compare x1 x2
>   compare (PE r1) (PE r2) = compare r1 r2 -- todo: this is not safe
>   compare (PStar p1 _) (PStar p2 _) = compare p1 p2 
>   compare (PPair p1 p2) (PPair p3 p4) = let r = compare p1 p3 in case r of 
>      { EQ -> compare p2 p4
>      ; _  -> r }
>   compare (PChoice ps1 _) (PChoice ps2 _) = 
>      compare ps1 ps2
>   compare p1 p2 = compare (hash p1) (hash p2) -- todo: this is not safe.


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

get all envs from the sbinder

> sbinderToEnv :: Pat -> SBinder -> [Env]
> sbinderToEnv _ (SChoice [] _) = []
> sbinderToEnv (PChoice (p:ps) g) (SChoice (sb:sbs) cf) 
>   | posEpsilon (strip p) = 
>   do { env <- sbinderToEnv p sb
>      ; return (env ++ cf) }
>   | otherwise = sbinderToEnv (PChoice ps g) (SChoice sbs cf)
> sbinderToEnv (PPair p1 p2) (SPair sb1 sb2 cf) = do { e1 <- sbinderToEnv p1 sb1 
>                                                    ; e2 <- sbinderToEnv p2 sb2
>                                                    ; return (e1 ++ e2) }
> sbinderToEnv (PVar x _ p) (SVar sr sb cf) 
>   | posEpsilon (strip p) = do { env <- sbinderToEnv p sb
>                       ; return ((sr:env) ++ cf) }
>   | otherwise = []
> sbinderToEnv (PStar _ _) (SStar cf) = [cf]
> sbinderToEnv (PE _) (SRE cf) = [cf]


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
>              ; Nothing -> error "pattern not found, this should not happen." }
>       delta' = map (\ (s,c,d,f) -> (pat2id s, c, pat2id d, f, sbinderToEnv d) ) delta
>       table = IM.fromList (map (\ (s,c,d,f,sb2env) -> (my_hash s c, (d,f,sb2env))) delta')
>       finals = map pat2id (filter (\p -> posEpsilon (strip p) ) allStates)
>   in (table, toSBinder p, sbinderToEnv p, finals)


> {-
> f p = 
>   let sig = sigmaRE (strip p)
>       init_dict = M.insert p 0 M.empty        
>       (allStates, delta, mapping) = builder sig [] [] init_dict 0 [p]
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
>           new_delta      = [ (p,l,p',f') | p <- curr_pats, l <- sig, (p',f') <- dPat0 p l  ]
>           new_pats       = D.nub [ p' | (p,l,p',f') <- new_delta, not (p' `M.member` dict) ]
>           acc_delta_next = acc_delta ++ new_delta
>           (dict',max_id') = foldl' (\(d,id) p -> (M.insert p (id+1) d, id + 1)) (dict,max_id) new_pats
>       in builder sig all_sofar_pats acc_delta_next dict' max_id' new_pats     

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
> execPatMatch (dt, init_sbinder, init_sb2env, finals, _, _) w = 
>   let r = execDfa 0 dt w [(0, init_sbinder, init_sb2env)]
>   in case r of 
>    { [] -> Nothing 
>    ; ((i,sb,sb2env):_) -> case (sb2env sb) of -- todo: check i `elem` finals?
>                           { [] -> Nothing 
>                           ; (e:_) -> Just e } }


> p4 = PVar 0 [] (PPair (PVar 1 [] ((PPair p_x p_y))) p_z)
>    where p_x = PVar 2 [] (PE (Choice [(L 'A'),(Seq (L 'A') (L 'B'))] Greedy))      
>          p_y = PVar 3 [] (PE (Choice [(Seq (L 'B') (Seq (L 'A') (L 'A'))), (L 'A')] Greedy))
>          p_z = PVar 4 [] (PE (Choice [(Seq (L 'A') (L 'C')), (L 'C')] Greedy))


x0 :: ( x1 :: (  x2 :: (x3:: a | x4 :: ab) | x5 :: b)* )


> p3 = PVar 0 [] (PStar ( PVar 1 [] ( PChoice [(PVar 2 [] (PChoice [p3,p4] Greedy)), p5] Greedy)) Greedy)
>    where p3 = PVar 3 [] (PE (L 'A'))
>          p4 = PVar 4 [] (PE (Seq (L 'A') (L 'B')))           
>          p5 = PVar 5 [] (PE (L 'B'))


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
> rg_collect w (Range i j) = S.take (j' - i') (S.drop i' w)
>	       where i' = fromIntegral i
>	             j' = fromIntegral j

> rg_collect_many w rs = foldl S.append S.empty $ map (rg_collect w) rs


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
>     in foldl up b fb

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
>     where fromRange (Range b e) = (b, e-b) 
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
>   foldl (\(acc', lefts') p -> let (acc'', lefts'') = buildFollowBy p (acc',lefts) -- all choice share the same lefts comming from the parent
>                               in (acc'', lefts' ++ lefts'')) (acc, []) ps
