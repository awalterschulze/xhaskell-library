> {- By Kenny Zhuo Ming Lu and Martin Sulzmann, 2009, BSD License -}

A bytestring implementation of reg exp pattern matching using partial derivative

> {-# LANGUAGE GADTs, MultiParamTypeClasses, FunctionalDependencies,
>     FlexibleInstances, TypeSynonymInstances, FlexibleContexts #-} 


> module Text.Regex.PDeriv.ByteString 
>     ( Regex
>     , CompOption(..)
>     , ExecOption(..)
>     , defaultCompOpt
>     , defaultExecOpt
>     , compile
>     , execute
>     , regexec
>     ) where 

> import List 
> -- import Data.Bits
> import Char (ord)
> -- import GHC.IOBase
> import GHC.Int
> import qualified Data.IntMap as IM
> import qualified Data.ByteString.Char8 as S

> import Text.Regex.Base(RegexOptions(..))


> import Text.Regex.PDeriv.Nfa
> import Text.Regex.PDeriv.RE
> import Text.Regex.PDeriv.Empty (isEmpty)
> import Text.Regex.PDeriv.Pretty (Pretty(..))
> import Text.Regex.PDeriv.Common
> import Text.Regex.PDeriv.Pattern 
> import Text.Regex.PDeriv.Parse


A word is a byte string.

> type Word = S.ByteString

the word matching algorithm using partDeriv

> match :: RE -> Word -> Bool
> match r w = match' [r] w
>     where 
>       match' :: [RE] -> Word -> Bool
>       match' rs w = 
>           case S.uncons w of 
>           Nothing  -> any isEmpty rs
>           Just (l,w') -> 
>               let rs' = nub (concat [ partDeriv r l | r <- rs])
>               in match' rs' w'


-- Kenny's scanner
-- right to left scanning of word to calculate reachable states

> rev_scan :: NFA Pat Letter -> Word -> [[Pat]]
> rev_scan nfa w = rev_scan_helper (S.reverse w) (delta_states nfa) (final_states nfa) []

> rev_scan_helper w delta curr_states chain =
>     case S.uncons w of
>	    Just (l,w') -> 
>			 let 
>			     pairs  = [ (p_s,p_t) | p_t <- curr_states, 
>			                (p_s, (l',_), p_t') <- delta , 
>			                l' == l, p_t == p_t' ]
>  		             (next_states', curr_states') = unzip pairs
>			     next_states'' =  nub next_states'
>		             curr_states'' =  nub curr_states'
>			     next_chain = curr_states'':chain
>		         in (rev_scan_helper w' delta $! next_states'') $! next_chain
>           Nothing -> curr_states:chain

version using the SNFA

In addtion, we pass in a lookup table that maps
target_state * letter to source_state.

> rev_scanIntState :: SNFA Pat Letter -> IM.IntMap [Int] -> Word -> [[Int]]
> rev_scanIntState snfa table w = table `seq` rev_scan_helperIntState (S.reverse w) table (sfinal_states snfa) []

> rev_scan_helperIntState w delta curr_states chain = 
>     case S.uncons w of 
>     Just (l,w') ->
>           let 
>                 pairs  =     [ (p_s,p_t) | p_t <- curr_states, 
>                                p_s <- my_lookup p_t l delta ]
>                 (next_states', curr_states') = unzip pairs
>                 next_states'' =  nub next_states'
>                 curr_states'' =  nub curr_states'
>                 next_chain = curr_states'':chain
>           in (rev_scan_helperIntState w' delta $! next_states'') $! next_chain
>     _ -> curr_states:chain

a hash table mapping (target_state,  letter) to source_state

> sdelta_table sdelta = foldl (\ dict (p,x,q) -> 
>                                let k = my_hash q (fst x)
>                                in case IM.lookup k dict of
>                                    Just ps -> IM.update (\ _ -> Just (p:ps)) k dict
>                                    Nothing -> IM.insert k [p] dict) IM.empty sdelta

the hash function

> my_hash :: Int -> Char -> Int
> my_hash i x = (ord x) + 1000 * i

the lookup function

> my_lookup :: Int -> Char -> IM.IntMap [Int] -> [Int]
> my_lookup i x dict = case IM.lookup (my_hash i x) dict of
>                      Just ys -> ys
>                      Nothing -> []



> instance Nfa Pat Letter where
>      pDeriv = pdPat
>      sigma p = map (\x -> (x,0)) (sigmaRE (strip p))
>                   -- index doesn't matter for NFA construction
>      empty p = isEmpty (strip p)


> instance Nfa RE Char where
>      pDeriv = partDeriv
>      sigma = sigmaRE
>      empty = isEmpty




----------------------------
-- (greedy) pattern matching

> type Env = [(Int,Word)]


version using symbolic pattern states

> patMatch :: Pat -> Word -> [Env]
> patMatch p w = concat (map (collectPatMatch w) allpats)
>   where
>     nfa = buildNFA p
>     filters =  rev_scan nfa w 
>     allpats = patMatches 0 w [p] filters

> patMatches :: Int -> Word -> [Pat] -> [[Pat]] -> [Pat]
> patMatches cnt w' ps fps' = 
>     case S.uncons w' of
>      Nothing -> ps
>      Just (l,w) -> 
>         let (fp:fps) = fps'
>             reachable_ps = [ p | p <- ps, elem p fp ]
>             next_ps = concat [ pdPat p (l,cnt) | p <- reachable_ps ]
>         in patMatches (cnt+1) w next_ps fps


version using Ints for state representation

> patMatchIntState :: Pat -> Word -> [Env]
> patMatchIntState p w = 
>   let
>     nfa  = buildNFA p
>     snfa = nfa `seq` toSNFA nfa
>     table = sdelta_table (sdelta_states snfa)
>     filters = snfa `seq` table `seq` rev_scanIntState snfa table $! w 
>     mapping = snfa `seq` mapping_states snfa
>     allpats = filters `seq` mapping `seq` (patMatchesIntState 0 mapping w [p]) filters
>   in concat (map (collectPatMatch w) $! allpats)

> patMatchesIntState :: Int -> (Pat -> Int) -> Word -> [Pat] -> [[Int]] -> [Pat]
> patMatchesIntState cnt mapping w' ps fps' =
>     case (S.uncons w',fps') of 
>       (Nothing,_) -> ps 
>       (Just (l,w),(fp:fps)) -> 
>           let 
>               reachable_ps = [ p | p <- ps, elem (mapping p) fp ]
>               next_ps = concat [ pdPat p (l,cnt) | p <- reachable_ps ]
>          in (patMatchesIntState (cnt+1)  mapping  w  $! next_ps) $! fps
>       (Just (_,_),[]) ->
>           error "patMatchesIntState failed: fps is empty, but input word is not empty."

> collectPatMatch :: Word -> Pat -> [Env]
> collectPatMatch w p =
>  let collect (PVar x (Just (i,j)) r)  = 
>          if isEmpty r then [[(x,rg_collect w (i,j))]] else []
>      collect (PVar x Nothing r) = 
>          if isEmpty r then [[(x,S.empty)]] else []  -- Nothing case !!!
>      collect (PEmpty p) = collect p
>      collect (PChoice p1 p2) =
>         (collect p1) ++ (collect p2)             
>             -- indet choice
>      collect (PPair p1 p2) = 
>          (collect p1) `combine` (collect p2)     
>           -- build all possible combinations
>  in collect p
>   where
>      combine xss yss = [ xs ++ ys |  xs <- xss, ys <- yss]

> rg_collect :: S.ByteString -> (Int,Int) -> S.ByteString
> rg_collect w (i,j) = S.take (j' - i' + 1) (S.drop i' w)
>	       where i' = fromIntegral i
>	             j' = fromIntegral j



actual pattern matcher

No optimization

> greedyPatMatch0 :: Pat -> Word -> Maybe Env
> greedyPatMatch0 p w =
>     first (patMatch p w) 
>   where
>     first (env:_) = return env
>     first _ = Nothing


Level 1 optimization

> greedyPatMatch1 :: Pat -> Word -> Maybe Env
> greedyPatMatch1 p w =
>      first (patMatchIntState p w)
>   where
>     first (env:_) = return env
>     first _ = Nothing



Profiling shows that greedyPatMatch1 is still not optimized.
The root cause is the use of (mapping p) in patMatchIntState.
The mapping is costly as it requires structure comparison between regexp patterns
and reg-exps for multiple times. (Size of the input word is a factor of the complexity)

Apart from that there are many partial derivative operations being performed 
during runtime. 

The idea is to elminate this mapping operations and partial derivative
operation at "run-time". 


We compile pattern to FAs. Since in patMatchIntState, we've been using Int to keep a record 
of the reachable pattern derivatives. We could leverage on these Int states.
However, we can't simply throw away the pattern because we need to compute
the bindings. We "compile" patterns to their int states and bindings.

A binder is set of (pattern var * range) pairs

> type Binder = [(Int,Maybe Range)]


turns a pattern into a binder

> toBinder :: Pat -> Binder
> toBinder  (PVar i mb_r _) = [(i,mb_r)]
> toBinder  (PPair p1 p2) = (toBinder p1) ++ (toBinder p2)
> toBinder  (PChoice p1 p2) = (toBinder p1) ++ (toBinder p2)
> toBinder  (PEmpty p) = toBinder p



a function that updates the binder given an index (that is the pattern var)
ASSUMPTION: the  var index in the pattern is linear. e.g. no ( 0 :: R1, (1 :: R2, 2 :: R3))

> updateBinderByIndex :: Int -> Binder -> Binder
> updateBinderByIndex i binder =
>     updateBinderByIndexSub 0 i binder 

> updateBinderByIndexSub :: Int -> Int -> Binder -> Binder
> updateBinderByIndexSub pos idx [] = []
> updateBinderByIndexSub pos idx (x@(idx',Just range):xs)
>     | pos `seq` idx `seq` idx' `seq` range `seq` xs `seq` False = undefined
>     | idx == idx' = (idx', Just (fst range, (snd range) + 1)):xs
>     | otherwise =  x:(updateBinderByIndexSub ((snd range) + 1) idx xs)
> updateBinderByIndexSub pos idx (x@(idx',Nothing):xs)
>     | pos `seq` idx `seq` idx' `seq` xs `seq` False = undefined
>     | idx == idx' = ((idx', Just (pos, pos)):xs)
>     | otherwise = x:(updateBinderByIndexSub pos idx xs)
        

a smarter version of mkBinderUpdate inspired by Martin's approach
It is a specialized version of pdPat0 that only constructs the binder update functions.

> pdPat0 :: Pat -> Letter -> [(Pat, Binder -> Binder)]
> pdPat0 (PVar x w r) (l,idx) =
>       let pd = partDeriv r l
>       in if null pd then []
>          else case w of 
>                 Nothing -> [(PVar x (Just (idx,idx)) (resToRE (partDeriv r l)) , updateBinderByIndex x) ]
>                 Just (i,j) -> [(PVar x (Just (i,j+1)) (resToRE pd)  ,  updateBinderByIndex x) ]
> pdPat0 (PPair p1 p2) l = 
>     if (isEmpty (strip p1))
>     then nub2 ([ (PPair p1' p2, f) | (p1' , f) <- pdPat0 p1 l ] ++ [ (PPair (mkEmpPat p1) p2', f) | (p2', f) <- pdPat0 p2 l])
>     else [ (PPair p1' p2, f) | (p1',f) <- pdPat0 p1 l ]
> pdPat0 (PChoice p1 p2) l = 
>     nub2 ((pdPat0 p1 l) ++ (pdPat0 p2 l)) -- nub doesn't seem to be essential

> nub2 = nubBy (\(p1,f1) (p2, f2) -> p1 == p2) 


we compile all the possible partial derivative operation into a table
The table maps key to a set of target integer states and their corresponding
binder update functions. 

> type PdPat0Table = IM.IntMap [(Int, Binder -> Binder)]

A function that builds the above table from the NFA and SNFA


> buildPdPat0Table :: NFA Pat Letter -> SNFA Pat Letter -> PdPat0Table
> buildPdPat0Table nfa snfa = 
>     let all = all_states nfa
>         sall = sall_states snfa
>         mapping = mapping_states snfa
>         {-
>         lists = [ (i,l,zip (map mapping ps) (map (mkBinderUpdate p) ps) ) | 
>                   (p,i)  <- zip all sall, l <- sigma p, let ps = pdPat p l, not (null ps) ]
>         -}
> --         lists = [ (i,l,zip (map (mapping . fst) pfs) (map snd pfs)) |
> --                  (p,i) <- zip all sall, l <- sigma p, let pfs = pdPat0 p l, not (null pfs) ]
>         lists = [ (i,l,zip (map (mapping . fst) pfs) (map snd pfs)) |
>                   (p,i) <- zip all sall, l <- sigma p, let pfs = nub2 (pdPat0 p l), not (null pfs) ]
>         hash_table = foldl (\ dict (p,x,q) -> 
>                                  let k = my_hash p (fst x)
>                                  in case IM.lookup k dict of 
>                                       Just ps -> error "Found a duplicate key in the PdPat0Table, this should not happend."
>                                       Nothing -> IM.insert k q dict) IM.empty lists
>     in hash_table
> 




the "partial derivative" operations among integer states + binders

> lookupPdPat0 :: PdPat0Table -> (Binder,Int) -> Letter -> [(Binder,Int)]
> lookupPdPat0 hash_table (binder,i) (l,x) = 
>     case IM.lookup (my_hash i l) hash_table of
>     Just pairs -> 
>         [ (op binder, j) | (j, op) <- pairs ]
>     Nothing -> []

collection function for binder 

> collectPatMatchFromBinder :: Word -> Binder -> Env
> collectPatMatchFromBinder w [] = []
> collectPatMatchFromBinder w ((x,Nothing):xs) = (x,S.empty):(collectPatMatchFromBinder w xs)
> collectPatMatchFromBinder w ((x,Just (i,j)):xs) = (x,rg_collect w (i,j)):(collectPatMatchFromBinder w xs)

the new pattern matching algo

> patMatchIntStatePdPat0 :: Pat -> Word -> [Env]
> patMatchIntStatePdPat0 p w = 
>   let
>     nfa  = buildNFA p
>     snfa = nfa `seq` toSNFA nfa
>     table = sdelta_table (sdelta_states snfa)
>     filters = w `seq` snfa `seq` table `seq` rev_scanIntState snfa table w 
>     mapping = snfa `seq` mapping_states snfa
>     s = p `seq` mapping `seq` mapping p
>     pdStateTable = buildPdPat0Table nfa snfa
>     b = toBinder p
>     allbinders' = b `seq` s `seq` pdStateTable `seq` filters `seq` (patMatchesIntStatePdPat0 0 pdStateTable w [(b,s)]) filters
>     allbinders = allbinders' `seq` map fst allbinders'
>   in map (collectPatMatchFromBinder w) $! allbinders


> patMatchesIntStatePdPat0 :: Int -> PdPat0Table -> Word -> [(Binder,Int)] -> [[Int]] -> [(Binder,Int)]
> patMatchesIntStatePdPat0 cnt pdStateTable  w' ps fps' =
>     case (S.uncons w', fps') of 
>       (Nothing,_) -> ps 
>       (Just (l,w),(fp:fps)) -> 
>           let 
>               reachable_ps = ps `seq` fp `seq` [ p | p@(_,s) <- ps, elem s fp ]
>               next_ps = l `seq` cnt `seq` pdStateTable `seq` reachable_ps `seq` concat [ lookupPdPat0 pdStateTable  p (l,cnt) | p <- reachable_ps ]
>               cnt' = cnt + 1
>          in cnt' `seq` pdStateTable `seq` w `seq` next_ps `seq` fps `seq` patMatchesIntStatePdPat0 cnt'  pdStateTable  w  next_ps fps
>       (Just (l,w),[]) ->
>           error "patMatchesIntStatePdPat0 failed with empty fps and non empty input word!"

Level 2 optimization (int states, reverse scanning, pre compiled pdPat)

> greedyPatMatch2 :: Pat -> Word -> Maybe Env
> greedyPatMatch2 p w =
>      first (patMatchIntStatePdPat0 p w)
>   where
>     first (env:_) = return env
>     first _ = Nothing


Level 3 optimization (int states, no reverse scanning, pre compiled pdPat)

> patMatchesIntStatePdPat0NoRevScan :: Int -> PdPat0Table -> Word -> [(Binder,Int)] -> [(Binder,Int)]
> patMatchesIntStatePdPat0NoRevScan cnt pdStateTable  w' eps =
>     case S.uncons w' of 
>       Nothing -> eps 
>       Just (l,w) -> 
>           let 
>               eps' = fast_nub [ ep' | ep <- eps, ep' <- lookupPdPat0 pdStateTable ep (l,cnt) ] 
>               -- it is expensive to nub here. nub when pdStateTable is built
>               cnt' = cnt + 1
>           in  cnt' `seq` pdStateTable `seq` w `seq` eps' `seq` patMatchesIntStatePdPat0NoRevScan cnt'  pdStateTable  w eps'

> fast_nub :: [(Binder,Int)] -> [(Binder,Int)]
> fast_nub eps = 
>     let im = IM.empty 
>     in fast_nub' im eps
>     where fast_nub' :: IM.IntMap () -> [(Binder,Int)] -> [(Binder,Int)]
>           fast_nub' im [] = []
>           fast_nub' im ((e,p):eps) = 
>               let mb_r = IM.lookup p im
>               in case mb_r of
>                  Just _ ->  fast_nub' im eps
>                  Nothing -> let im' = IM.insert p () im
>                             in (e,p):(fast_nub' im' eps)



> patMatchIntStatePdPat0NoRevScan :: Pat -> Word -> [Env]
> patMatchIntStatePdPat0NoRevScan p w = 
>   let
>     nfa  = buildNFA p
>     snfa = nfa `seq` toSNFA nfa
>     -- table = sdelta_table (sdelta_states snfa)
>     mapping = snfa `seq` mapping_states snfa
>     s = p `seq` mapping `seq` mapping p
>     pdStateTable = buildPdPat0Table nfa snfa
>     b = toBinder p
>     allbinders' = b `seq` s `seq` pdStateTable `seq` (patMatchesIntStatePdPat0NoRevScan 0 pdStateTable w [(b,s)])
>     allbinders = allbinders' `seq` map fst (filter (\(_,i) -> i `elem` (sfinal_states snfa)) allbinders' )
>   in map (collectPatMatchFromBinder w) $! allbinders


> greedyPatMatch3 :: Pat -> Word -> Maybe Env
> greedyPatMatch3 p w =
>      first (patMatchIntStatePdPat0NoRevScan p w)
>   where
>     first (env:_) = return env
>     first _ = Nothing

Compilation


> compile1 :: Pat -> (SNFA Pat Letter, Pat, IM.IntMap [Int] )
> compile1 p = nfa `seq` snfa `seq` table `seq` (snfa, p, table)
>     where nfa = buildNFA p
>           snfa = toSNFA nfa
>           table = sdelta_table (sdelta_states snfa)

> patMatchIntStateCompiled1 :: (SNFA Pat Letter, Pat, IM.IntMap [Int]) -> Word -> [Env]
> patMatchIntStateCompiled1 (snfa,p,table) w = 
>   let
>     filters = snfa `seq` table `seq` rev_scanIntState snfa table $! w 
>     mapping = snfa `seq` mapping_states snfa
>     allpats = filters `seq` mapping `seq` (patMatchesIntState 0 mapping w [p]) filters
>   in concat (map (collectPatMatch w) $! allpats)



> compile2 :: Pat -> (PdPat0Table, SNFA Pat Letter, Pat, IM.IntMap [Int])
> compile2 p =  nfa `seq` snfa `seq` pdStateTable `seq` table `seq` (pdStateTable, snfa, p, table)
>     where nfa = buildNFA p
>           snfa = toSNFA nfa
>           pdStateTable = buildPdPat0Table nfa snfa
>           table = sdelta_table (sdelta_states snfa)

> patMatchIntStateCompiled2 :: (PdPat0Table, SNFA Pat Letter,Pat, IM.IntMap [Int] ) -> Word -> [Env]
> patMatchIntStateCompiled2 (pdStateTable,snfa,p,table) w = 
>   let
>     filters = snfa `seq` rev_scanIntState snfa table $! w 
>     mapping = snfa `seq` mapping_states snfa
>     s = p `seq` mapping `seq` mapping p
>     b = toBinder p
>     allbinders' = b `seq` s `seq` pdStateTable `seq` filters `seq` (patMatchesIntStatePdPat0 0 pdStateTable w [(b,s)]) filters
>     allbinders =  map fst allbinders'
>   in map (collectPatMatchFromBinder w) allbinders

> compile3 :: Pat -> (PdPat0Table, SNFA Pat Letter, Pat, IM.IntMap [Int])
> compile3 = compile2 

> patMatchIntStateCompiled3 :: (PdPat0Table, SNFA Pat Letter,Pat, IM.IntMap [Int] ) -> Word -> [Env]
> patMatchIntStateCompiled3 (pdStateTable,snfa,p,table) w = 
>   let
>     mapping = snfa `seq` mapping_states snfa
>     s = p `seq` mapping `seq` mapping p
>     b = toBinder p
>     allbinders' = b `seq` s `seq` pdStateTable `seq` (patMatchesIntStatePdPat0NoRevScan 0 pdStateTable w [(b,s)]) 
>     allbinders = allbinders' `seq` map fst (filter (\(_,i) -> i `elem` (sfinal_states snfa)) allbinders' )
>   in map (collectPatMatchFromBinder w) allbinders




> greedyPatMatchCompiled1 :: (SNFA Pat Letter, Pat, IM.IntMap [Int]) -> Word -> Maybe Env
> greedyPatMatchCompiled1 compiled w =
>      first (patMatchIntStateCompiled1 compiled w)
>   where
>     first (env:_) = return env
>     first _ = Nothing


> greedyPatMatchCompiled2 :: (PdPat0Table, SNFA Pat Letter, Pat, IM.IntMap [Int]) -> Word -> Maybe Env
> greedyPatMatchCompiled2 compiled w =
>      first (patMatchIntStateCompiled2 compiled w)
>   where
>     first (env:_) = return env
>     first _ = Nothing

> greedyPatMatchCompiled3 :: (PdPat0Table, SNFA Pat Letter, Pat, IM.IntMap [Int]) -> Word -> Maybe Env
> greedyPatMatchCompiled3 compiled w =
>      first (patMatchIntStateCompiled3 compiled w)
>   where
>     first (env:_) = return env
>     first _ = Nothing


-- Kenny's example

> long_pat = PPair (PVar 1 Nothing (Star (L 'A'))) (PVar 2  Nothing (Star (L 'A')))
> long_string n = (take 0 (repeat 'A')) ++ (take n (repeat 'B'))

-- p4 = << x : (A|<A,B>), y : (<B,<A,A>>|A) >, z : (<A,C>|C) > 

> p4 = PPair (PPair p_x p_y) p_z
>    where p_x = PVar 1  Nothing (Choice (L 'A') (Seq (L 'A') (L 'B')))        
>          p_y = PVar 2  Nothing (Choice (Seq (L 'B') (Seq (L 'A') (L 'A'))) (L 'A'))  
>          p_z = PVar 3  Nothing (Choice (Seq (L 'A') (L 'C')) (L 'C')) 

> input = S.pack "ABAAC"  -- long(posix) vs greedy match

> -- | The PDeriv backend spepcific 'Regex' type

> newtype Regex = Regex (PdPat0Table, SNFA Pat Letter, Pat, IM.IntMap [Int]) 


-- todo: use the CompOption and ExecOption

> compile :: CompOption -- ^ Flags (summed together)
>         -> ExecOption -- ^ Flags (summed together) 
>         -> S.ByteString -- ^ The regular expression to compile
>         -> Either String Regex -- ^ Returns: the compiled regular expression
> compile compOpt execOpt bs =
>     case parsePat (S.unpack bs) of
>     Left err -> Left ("parseRegex for Text.Regex.PDeriv.ByteString failed:"++show err)
>     Right pat -> Right (patToRegex pat compOpt execOpt)
>     where 
>       patToRegex p _ _ = Regex (compile3 p)



> execute :: Regex      -- ^ Compiled regular expression
>        -> S.ByteString -- ^ ByteString to match against
>        -> Either String (Maybe Env)
> execute (Regex r) bs = Right (greedyPatMatchCompiled3 r bs)

> regexec :: Regex      -- ^ Compiled regular expression
>        -> S.ByteString -- ^ ByteString to match against
>        -> Either String (Maybe (S.ByteString, S.ByteString, S.ByteString, [S.ByteString]))
> regexec (Regex r) bs =
>  case greedyPatMatchCompiled3 r bs of
>    Nothing -> Right (Nothing)
>    Just env ->
>      let pre = S.empty  -- todo
>          main = S.empty -- todo
>          post = S.empty -- todo
>          matched = map snd (filter (\(v,w) -> v > 0) env)
>      in Right (Just (pre,main,post,matched))


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

