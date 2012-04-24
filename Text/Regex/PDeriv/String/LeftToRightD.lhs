> {- By Kenny Zhuo Ming Lu and Martin Sulzmann, 2009, BSD License -}

A string implementation of reg exp pattern matching using partial derivative
This algorithm exploits the extension of partial derivative of regular expression patterns.
This algorithm proceeds by scanning the input word from left to right until we reach 
an emptiable pattern and the input word is fully consumed.

> {-# LANGUAGE GADTs, MultiParamTypeClasses, FunctionalDependencies,
>     FlexibleInstances, TypeSynonymInstances, FlexibleContexts, BangPatterns #-} 


> module Text.Regex.PDeriv.String.LeftToRightD
>     ( Regex
>     , CompOption(..)
>     , ExecOption(..)
>     , defaultCompOpt
>     , defaultExecOpt
>     , compile
>     , execute
>     , regexec
>     ) where 

> import Data.List 
> import Data.Char (ord)
> -- import GHC.Int
> import qualified Data.IntMap as IM

> import System.IO.Unsafe (unsafePerformIO)

> import Text.Regex.Base(RegexOptions(..))

> import Text.Regex.PDeriv.RE
> import Text.Regex.PDeriv.Pretty (Pretty(..))
> import Text.Regex.PDeriv.Common (Range(..), Letter, PosEpsilon(..), Simplifiable(..), my_hash, my_lookup, GFlag(..), nub2, preBinder, mainBinder, subBinder)
> import Text.Regex.PDeriv.IntPattern (Pat(..), pdPat, pdPat0, pdPat0Sim, toBinder, Binder(..), strip, listifyBinder)
> import Text.Regex.PDeriv.Parse
> import qualified Text.Regex.PDeriv.Dictionary as D (Dictionary(..), Key(..), insert, insertNotOverwrite, lookupAll, empty, isIn, nub)


A word is a byte string.

> type Word = String


----------------------------
-- (greedy) pattern matching

> type Env = [(Int,Word)]

> rg_collect :: String -> Range -> String
> rg_collect w (Range i j) = take (j' - i' + 1) (drop i' w)
>	       where i' = fromIntegral i
>	             j' = fromIntegral j



we compile all the possible partial derivative operation into a table
The table maps key to a set of target integer states and their corresponding
binder update functions. 

> type PdPat0Table = IM.IntMap [(Int, Int -> Binder -> Binder)]

A function that builds the above table from the pattern

> buildPdPat0Table :: Pat ->  (PdPat0Table, [Int])
> buildPdPat0Table init = 
>     let sig = map (\x -> (x,0)) (sigmaRE (strip init))                              -- the sigma
>         init_dict = D.insertNotOverwrite (D.hash init) (init,0) D.empty             -- add init into the initial dictionary
>         (all, delta, dictionary) = sig `seq` builder sig [] [] [init] init_dict 1   -- all states and delta
>         final = all `seq`  [ s | s <- all, posEpsilon (strip s)]                       -- the final states
>         sfinal = final `seq` dictionary `seq` map (mapping dictionary) final
>         lists = [ (i,l,jfs) | 
>                   (p,l, qfs) <- delta, 
>                   let i = mapping dictionary p
>                       jfs = map (\(q,f) -> (mapping dictionary q, f)) qfs
>                   ]
>         hash_table = foldl' (\ dict (p,x,q) -> 
>                                  let k = my_hash p (fst x)
>                                  in case IM.lookup k dict of 
>                                       Just ps -> error "Found a duplicate key in the PdPat0Table, this should not happen."
>                                       Nothing -> IM.insert k q dict) IM.empty lists
>     in (hash_table, sfinal)


                             
Some helper functions used in buildPdPat0Table

> mapping :: D.Dictionary (Pat,Int) -> Pat -> Int
> mapping dictionary x = let candidates = D.lookupAll (D.hash x) dictionary
>                        in candidates `seq` 
>                           case candidates of
>                             [(_,i)] -> i
>                             _ -> 
>                                 case lookup x candidates of
>                                 (Just i) -> i
>                                 Nothing -> error ("this should not happen. looking up " ++ (pretty x) ++ " from " ++ (show candidates) )

> builder :: [Letter] 
>         -> [Pat] 
>         -> [(Pat,Letter, [(Pat, Int -> Binder -> Binder)] )]
>         -> [Pat] 
>         -> D.Dictionary (Pat,Int)
>         -> Int 
>         -> ([Pat], [(Pat, Letter, [(Pat, Int -> Binder -> Binder)])], D.Dictionary (Pat,Int))
> builder sig acc_states acc_delta curr_states dict max_id 
>     | null curr_states  = (acc_states, acc_delta, dict)
>     | otherwise = 
>         let 
>             all_sofar_states = acc_states ++ curr_states
>             new_delta = [ (s, l, sfs) | s <- curr_states, l <- sig, let sfs = pdPat0Sim s l]
>             new_states = all_sofar_states `seq` D.nub [ s' | (_,_,sfs) <- new_delta, (s',f) <- sfs
>                                                       , not (s' `D.isIn` dict) ]
>             acc_delta_next  = (acc_delta ++ new_delta)
>             (dict',max_id') = new_states `seq` foldl' (\(d,id) p -> (D.insertNotOverwrite (D.hash p) (p,id) d, id + 1) ) (dict,max_id) new_states
>         in {- dict' `seq` max_id' `seq` -} builder sig all_sofar_states acc_delta_next new_states dict' max_id' 




Optimizaing lookup pdpat table.
build a hash table that map [ Int ]  states + label  to [ Int ] states where 
the resulting [ Int ] is already nubbed and join, hence there is no need to run the pairing and nubbing on the fly.
This would cause some compile time overhead and trading space with time.

Technical problem, how to hash a [ Int ] in Haskell?

> type NFAStates = [ Int ]

> type DPat0Table = IM.IntMap ( Int       -- the next DFA state
>                             , NFAStates -- the next NFA states
>                             , IM.IntMap [Int -> Binder -> Binder] -- the transition function : position -> current_binders -> next_binders
>                             ) -- deterministic: one output state and one update function

> buildDPat0Table :: Pat -> (DPat0Table, [Int])
> buildDPat0Table init = 
>     let sig = map (\x -> (x,0)) (sigmaRE (strip init))                              -- the sigma
>         -- building the NFA
>         init_dict = D.insertNotOverwrite (D.hash init) (init,0) D.empty             -- add init into the initial dictionary
>         (all, delta, dictionary) = sig `seq` builder sig [] [] [init] init_dict 1   -- all states and delta
>         final = all `seq`  [ s | s <- all, posEpsilon (strip s)]                       -- the final states
>         sfinal = final `seq` dictionary `seq` map (mapping dictionary) final
>         lists = dictionary `seq` 
>                 [ (i,l,jfs) | 
>                   (p,l, qfs) <- delta, 
>                   let i   = mapping dictionary p
>                       jfs = map (\(q,f) -> (mapping dictionary q, f)) qfs
>                   ]
>         hash_table = lists `seq` 
>                      foldl' (\ dict (p,x,q) -> 
>                                  let k = my_hash p (fst x)
>                                  in case IM.lookup k dict of 
>                                       Just ps -> error "Found a duplicate key in the PdPat0Table, this should not happen."
>                                       Nothing -> IM.insert k q dict) IM.empty lists
>         -- building the DFA
>         init'       = [ 0 ]
>         init_dict'  = init' `seq` D.insert (D.hash init') (init',0) D.empty
>         (all', delta', dictionary') = hash_table `seq` init' `seq` init_dict' `seq`
>                                       builder' hash_table sig [] [] [init'] init_dict' 1
>         lists'      = delta' `seq` dictionary' `seq` 
>                       map (\(c,l,n,f) -> 
>                                let i = c `seq` mapping' dictionary' c
>                                    j = n `seq` mapping' dictionary' n
>                                in f `seq` i `seq` j `seq` n `seq` l `seq` (i, l, j, n, f)) delta'
>         hash_table' = lists' `seq` 
>                       foldl' (\ dict' (i, l, j, n, f) ->
>                              let k = my_hash i (fst l)
>                              in case IM.lookup k dict' of
>                                   Just ps -> error "Found a duplicate key."
>                                   Nothing -> IM.insert k (j,n,f) dict') IM.empty lists'
>     in hash_table' `seq` sfinal `seq` (hash_table',sfinal)


> mapping' :: D.Dictionary (NFAStates,Int) -> NFAStates -> Int
> mapping' dictionary x = let candidates = dictionary `seq` D.lookupAll (D.hash x) dictionary
>                         in candidates `seq` 
>                            case candidates of
>                                     [(_,i)] -> i
>                                     _ -> 
>                                         case lookup x candidates of
>                                         (Just i) -> i
>                                         Nothing -> error ("this should not happen. looking up " ++ (show x) ++ " from " ++ (show candidates) )


> builder' :: PdPat0Table
>          -> [ Letter ]
>          -> [ NFAStates ] -- all so far
>          -> [ ( NFAStates, Letter, NFAStates, IM.IntMap [Int -> Binder -> Binder] ) ]  -- delta
>          -> [ NFAStates ]  -- maybe new states
>          -> D.Dictionary (NFAStates, Int) -- mapping dictionary
>          -> Int -- max key
>          -> ( [ NFAStates ] -- all states
>             , [ (NFAStates, Letter, NFAStates, IM.IntMap [Int -> Binder -> Binder] ) ]  -- all delta : book keeping: IntMap, mapping input nfa state to op?
>             , D.Dictionary (NFAStates, Int) )
> builder' pdStateTable sig acc_states acc_delta [] dict max_id = (acc_states, acc_delta, dict)
> builder' pdStateTable sig acc_states acc_delta curr_states dict max_id =
>     let all_sofar_states = acc_states `seq` curr_states `seq` 
>                            acc_states ++ curr_states 
>         insert k f im    = k `seq` im `seq` 
>                            case IM.lookup k im of 
>                            { Just fs -> IM.update (\_ -> Just (fs ++ [ f ])) k im 
>                            ; Nothing -> IM.insert k [f] im
>                            }
> {-
>         new_delta        = [ next_state `seq` f_dict `seq` (curr_state, l, next_state, f_dict) |
>                              curr_state <- curr_states
>                            , l <- sig
>                            , let pairs = curr_state `seq` l `seq` nub2 (concatMap ( \n_state -> lookupPdPat1 pdStateTable n_state l ) curr_state) 
>                            , not (null pairs)
>                            , let (next_state, curr_state_and_f_pairs) = pairs `seq` unzip pairs
>                                  f_dict                               = curr_state_and_f_pairs `seq` foldl' (\im (l,f) -> insert l f im) IM.empty curr_state_and_f_pairs
>                            ] 
>  -}
>         new_delta        = pdStateTable `seq` curr_states `seq`
>                            concatMap ( \curr_state -> 
>                                          map (\l -> 
>                                                   let
>                                                       pairs = curr_state `seq` l `seq` nub2 (concatMap' ( \n_state -> lookupPdPat1 pdStateTable n_state l ) curr_state) 
>                                                       (next_state, curr_state_and_f_pairs) = pairs `seq` unzip pairs
>                                                       f_dict                               = curr_state_and_f_pairs `seq` 
>                                                                                              foldl' (\im (l,f) -> insert l f im) IM.empty curr_state_and_f_pairs
>                                                       in next_state `seq` f_dict `seq` (curr_state, l, next_state, f_dict) ) sig
>                                        )  curr_states
>         new_states       = new_delta `seq` 
>                            D.nub [ next_state | 
>                                    (_,_,next_state,_) <- new_delta
>                                  , not (next_state `D.isIn` dict) ]
>         acc_delta_next   = acc_delta `seq` new_delta `seq` 
>                            (acc_delta ++ new_delta)
>         (dict',max_id')  = new_states `seq` dict `seq` max_id `seq`  
>                            foldl' (\(d,id) p -> (D.insert (D.hash p) (p,id) d, id + 1)) (dict,max_id) new_states 
>     in all_sofar_states `seq` new_states `seq` dict' `seq` max_id'`seq` sig `seq` acc_delta_next `seq`
>            builder' pdStateTable sig all_sofar_states acc_delta_next new_states dict' max_id'






the "partial derivative" operations among integer states + binders


> lookupPdPat1 :: PdPat0Table -> Int -> Letter -> [ ( Int -- next state
>                                                   , ( Int -- current state : used as key to build the hash table
>                                                     , Int -> Binder -> Binder)) ]
> lookupPdPat1 hash_table i (l,_) = 
>     let k = my_hash i l
>     in 
>       k `seq` 
>       case IM.lookup k hash_table of 
>                { Just pairs -> 
>                      map (\ (j,op) -> 
>                               (j, (i, op))) pairs 
>                ; Nothing -> [] 
>                }

collection function for binder 

> collectPatMatchFromBinder :: Word -> Binder -> Env
> collectPatMatchFromBinder w b = 
>     collectPatMatchFromBinder_ w (listifyBinder b)

> collectPatMatchFromBinder_ w [] = []
> collectPatMatchFromBinder_ w ((x,[]):xs) = (x,""):(collectPatMatchFromBinder_ w xs)
> collectPatMatchFromBinder_ w ((x,rs):xs) = (x,foldl' (++) "" $ map (rg_collect w) (reverse rs)):(collectPatMatchFromBinder_ w xs)


orginally the type was Int -> DPat0Table -> Word -> (Int,[(Int,Binder)]) -> (Int, [(Int,Binder)])
where the first Int is the DFA state, but this leads to a mysterious Stack overflow fiasco, (which I don't have time to investigate why
or able to come out a smallish example)

> patMatchesIntStatePdPat1 :: Int -> DPat0Table -> Word -> [(Int,Int,Binder)] -> [(Int,Int,Binder)]
> patMatchesIntStatePdPat1 cnt dStateTable  w' [] = []
> patMatchesIntStatePdPat1 cnt dStateTable  w' currNfaStateBinders =
>     case  w' of 
>       [] -> currNfaStateBinders -- we are done with the matching
>       (l:w) -> 
>           let ((i,_,_):_) = currNfaStateBinders  -- i is the current DFA state
>               k           =  l `seq` i `seq` my_hash i l
>           in
>           case IM.lookup k dStateTable of
>             { Nothing -> [] -- "key missing" which means some letter exists in w but not in r.    
>             ; Just (j,next_nfaStates,fDict) -> 
>                 let 
>                     binders :: [Binder]
>                     binders = 
>                               fDict `seq` computeBinders currNfaStateBinders fDict cnt 
>                     nextNfaStateBinders = -- io `seq` 
>                                           binders `seq` next_nfaStates `seq` j `seq`
>                                           map (\(x,y) -> (j,x,y)) (zip next_nfaStates binders)
>                     cnt' = {-# SCC "cnt" #-} cnt + 1
>                 in nextNfaStateBinders `seq` cnt' `seq` w `seq`
>                        patMatchesIntStatePdPat1 cnt' dStateTable w  nextNfaStateBinders } 


fusing up the computation for binders

> computeBinders :: [(Int,Int,Binder)] -> IM.IntMap [Int -> Binder -> Binder] -> Int -> [Binder]
> computeBinders currNfaStateBinders fDict cnt = 
>     cm currNfaStateBinders
>     where 
>        cm :: [(Int,Int,Binder)] -> [Binder]
>        cm bs = foldl' k [] bs
>        k :: [Binder] -> (Int,Int,Binder) -> [Binder]
>        k !a (_,!m,!b) = case IM.lookup m fDict of { Nothing -> a; Just !gs -> ((++) a $! (map (\g -> g cnt b) gs)) }  


> 
> concatMap' :: (a -> [b]) -> [a] -> [b]
> concatMap' f x = foldr' ( \ b a -> (++) a $! (f b) ) [] x
> 


> foldr' :: (a -> b -> b) -> b -> [a] -> b
> foldr' f b [] = b
> foldr' f b (a:as) = let b' = f a b 
>                     in b' `seq` 
>                        foldr' f b' as


> 

> patMatchIntStatePdPat1 :: Pat -> Word -> [Env]
> patMatchIntStatePdPat1 p w = 
>   let
>     (dStateTable,sfinal) = buildDPat0Table p
>     s = 0
>     b = toBinder p
>     allbinders' = b `seq` s `seq` dStateTable `seq` (patMatchesIntStatePdPat1 0 dStateTable w [(0,s,b)])
>     allbinders = allbinders' `seq` map third (filter (\(_,i,_) -> i `elem` sfinal) allbinders' )
>   in map (collectPatMatchFromBinder w) $! allbinders


> greedyPatMatch' :: Pat -> Word -> Maybe Env
> greedyPatMatch' p w =
>      first (patMatchIntStatePdPat1 p w)
>   where
>     first (env:_) = return env
>     first _ = Nothing


Compilation


> compilePat :: Pat -> (DPat0Table, [Int], Binder)
> compilePat p =  (dStateTable, sfinal, b)
>     where 
>           (dStateTable,sfinal) = buildDPat0Table p
>           b = toBinder p

> patMatchIntStateCompiled :: (DPat0Table, [Int], Binder) -> Word -> [Env]
> patMatchIntStateCompiled (dStateTable,sfinal,b) w = 
>   let
>     s = 0 
>     e = [(0,0,b)]
>     allbinders' = e `seq` b `seq` s `seq` dStateTable `seq` (patMatchesIntStatePdPat1 0 dStateTable w e ) 
>     allbinders = allbinders' `seq` map third (filter (\(_,i,_) -> i `elem` sfinal) allbinders' )
>   in allbinders `seq` map (collectPatMatchFromBinder w) allbinders

> third :: (a,b,c) -> c
> third (_,_,x) = x

> greedyPatMatchCompiled :: (DPat0Table, [Int], Binder) -> Word -> Maybe Env
> greedyPatMatchCompiled compiled w =
>      first (patMatchIntStateCompiled compiled w)
>   where
>     first (env:_) = return env
>     first _ = Nothing



> -- | The PDeriv backend spepcific 'Regex' type

> newtype Regex = Regex (DPat0Table, [Int], Binder) 


-- todo: use the CompOption and ExecOption

> compile :: CompOption -- ^ Flags (summed together)
>         -> ExecOption -- ^ Flags (summed together) 
>         -> String -- ^ The regular expression to compile
>         -> Either String Regex -- ^ Returns: the compiled regular expression
> compile compOpt execOpt bs =
>     case parsePat bs of
>     Left err -> Left ("parseRegex for Text.Regex.PDeriv.ByteString failed:"++show err)
>     Right pat -> Right (patToRegex pat compOpt execOpt)
>     where 
>       patToRegex p _ _ = Regex (compilePat $ simplify p)



> execute :: Regex      -- ^ Compiled regular expression
>        -> String -- ^ String to match against
>        -> Either String (Maybe Env)
> execute (Regex r) bs = Right (greedyPatMatchCompiled r bs)

> regexec :: Regex      -- ^ Compiled regular expression
>        -> String -- ^ String to match against
>        -> Either String (Maybe (String, String, String, [String]))
> regexec (Regex r) bs = -- r `seq` Right Nothing
>  case greedyPatMatchCompiled r bs of
>    Nothing -> Right (Nothing)
>    Just env ->
>      let pre = case lookup preBinder env of { Just w -> w ; Nothing -> [] }
>          post = case lookup subBinder env of { Just w -> w ; Nothing -> [] }
>          main = case lookup mainBinder env of { Just w -> w ; Nothing -> [] }
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
>     , newSyntax :: Bool        -- ^ False in blankCompOpt, True in defaultCompOpt. 
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


