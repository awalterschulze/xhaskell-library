> {- By Kenny Zhuo Ming Lu and Martin Sulzmann, 2009, BSD License -}

A bytestring implementation of reg exp pattern matching using partial derivative
This algorithm exploits the extension of partial derivative of regular expression patterns.
This algorithm proceeds by scanning the input word from left to right until we reach 
an emptiable pattern and the input word is fully consumed.

> {-# LANGUAGE GADTs, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances, 
>     FlexibleInstances, TypeSynonymInstances, FlexibleContexts, BangPatterns #-} 


> module Text.Regex.PDeriv.ByteString.LeftToRightD
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
> import qualified Data.ByteString.Char8 as S
> import Control.DeepSeq

> import Control.Parallel 
> import Control.Parallel.Strategies 

> import Control.Monad.ST
> import Control.Monad
> import Control.Monad.Primitive
> import System.IO.Unsafe


> import System.IO.Unsafe (unsafePerformIO)

> import Text.Regex.Base(RegexOptions(..))


> import Text.Regex.PDeriv.RE
> import Text.Regex.PDeriv.Pretty (Pretty(..))
> import Text.Regex.PDeriv.Common (Range, Letter, PosEpsilon(..), Simplifiable(..), my_hash, my_lookup, GFlag(..), nub2, preBinder, mainBinder, subBinder)
> import Text.Regex.PDeriv.IntPattern (Pat(..), pdPat, pdPat0, pdPat0Sim, toBinder, toBinderList, Binder(..), strip, listifyBinder, BinderGrid, bgInit, bgGetCol)
> import Text.Regex.PDeriv.Parse
> import qualified Text.Regex.PDeriv.Dictionary as D (Dictionary(..), Key(..), insert, insertNotOverwrite, lookupAll, empty, isIn, nub)



A word is a byte string.

> type Word = S.ByteString


----------------------------
-- (greedy) pattern matching

> type Env = [(Int,Word)]

 rg_collect :: S.ByteString -> (Int,Int) -> S.ByteString

> rg_collect :: S.ByteString -> Range -> S.ByteString
> rg_collect w ((,) i j) = S.take (j' - i' + 1) (S.drop i' w)
>	       where i' = fromIntegral i
>	             j' = fromIntegral j



we compile all the possible partial derivative operation into a table
The table maps key to a set of target integer states and their corresponding
binder update functions. 

> type PdPat0Table m = IM.IntMap [(Int, Int -> Int -> BinderGrid m -> m (BinderGrid m))]

A function that builds the above table from the pattern

> buildPdPat0Table :: (PrimMonad m) => Pat ->  (PdPat0Table m, [Int])
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

> numOfStates :: Pat -> Int
> numOfStates init = 
>     let sig = map (\x -> (x,0)) (sigmaRE (strip init))                              -- the sigma
>         init_dict = D.insertNotOverwrite (D.hash init) (init,0) D.empty             -- add init into the initial dictionary
>         builderGrounded :: [Letter] 
>                         -> [Pat] 
>                         -> [(Pat,Letter, [Pat])]
>                         -> [Pat] 
>                         -> D.Dictionary (Pat,Int)
>                         -> Int 
>                         -> ([Pat], [(Pat, Letter, [Pat])], D.Dictionary (Pat,Int))
>         builderGrounded sig acc_states acc_delta curr_states dict max_id 
>                         | null curr_states  = (acc_states, acc_delta, dict)
>                         | otherwise = 
>                           let 
>                               all_sofar_states = acc_states ++ curr_states
>                               new_delta = [ (s, l, ss) | s <- curr_states, l <- sig, let ss = pdPat s l]
>                               new_states = all_sofar_states `seq` D.nub [ s' | (_,_,ss) <- new_delta, s' <- ss
>                                                       , not (s' `D.isIn` dict) ]
>                               acc_delta_next  = (acc_delta ++ new_delta)
>                               (dict',max_id') = new_states `seq` foldl' (\(d,id) p -> (D.insertNotOverwrite (D.hash p) (p,id) d, id + 1) ) (dict,max_id) new_states
>                           in builderGrounded sig all_sofar_states acc_delta_next new_states dict' max_id' 
>         (all, delta, dictionary) = sig `seq` builderGrounded sig [] [] [init] init_dict 1   -- all states and delta
>     in length all

> numOfVars :: Pat -> Int
> numOfVars init = length (toBinderList init)                           

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

> builder :: (PrimMonad m) => [Letter] 
>         -> [Pat] 
>         -> [(Pat,Letter, [(Pat, Int -> Int -> BinderGrid m -> m (BinderGrid m))] )]
>         -> [Pat] 
>         -> D.Dictionary (Pat,Int)
>         -> Int 
>         -> ([Pat], [(Pat, Letter, [(Pat, Int -> Int -> BinderGrid m -> m (BinderGrid m))])], D.Dictionary (Pat,Int))
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

> type DPat0Table m = IM.IntMap ( Int       -- the next DFA state
>                             , NFAStates -- the next NFA states
>                             , IM.IntMap [Int -> Int -> BinderGrid m -> m (BinderGrid m)] -- the transition function : position -> current_binders -> next_binders
>                             ) -- deterministic: one output state and one update function

> buildDPat0Table :: (Monad m, PrimMonad m) => Pat -> (DPat0Table m, [Int])
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


> builder' :: (PrimMonad m) => PdPat0Table m
>          -> [ Letter ]
>          -> [ NFAStates ] -- all so far
>          -> [ ( NFAStates, Letter, NFAStates, IM.IntMap [Int -> Int -> BinderGrid m -> m (BinderGrid m)] ) ]  -- delta
>          -> [ NFAStates ]  -- maybe new states
>          -> D.Dictionary (NFAStates, Int) -- mapping dictionary
>          -> Int -- max key
>          -> ( [ NFAStates ] -- all states
>             , [ (NFAStates, Letter, NFAStates, IM.IntMap [Int -> Int -> BinderGrid m -> m (BinderGrid m) ] ) ]  -- all delta : book keeping: IntMap, mapping input nfa state to op?
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


> lookupPdPat1 :: (Monad m, PrimMonad m) => PdPat0Table m -> Int -> Letter -> [ ( Int -- next state
>                                                   , ( Int -- current state : used as key to build the hash table
>                                                     , Int -> Int -> BinderGrid m -> m (BinderGrid m))) ]
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
> collectPatMatchFromBinder_ w ((x,((,) (-1) (-1))):xs) = (x,S.empty):(collectPatMatchFromBinder_ w xs)
> collectPatMatchFromBinder_ w ((x,rs):xs) = (x,rg_collect w rs):(collectPatMatchFromBinder_ w xs)
> {-
>                                            (x, f w rs):(collectPatMatchFromBinder_ w xs)
>     where f w [] = S.empty
>           f w (r:_) = rg_collect w r
> -}

> collectPatMatchFromBinderGrid :: Word -> BinderGrid (IO) -> [Int] -> IO [Env]
> collectPatMatchFromBinderGrid w bg states = 
>     mapM (\state -> collectOne w bg state) states
>    where collectOne :: Word -> BinderGrid (IO) -> Int -> IO Env
>          collectOne w bg state = do { col <- bgGetCol bg state 
>                                     ; return (collectPatMatchFromBinder_ w col) }

orginally the type was Int -> DPat0Table -> Word -> (Int,[(Int,Binder)]) -> (Int, [(Int,Binder)])
where the first Int is the DFA state, but this leads to a mysterious Stack overflow fiasco, (which I don't have time to investigate why
or able to come out a smallish example)

> {- 
> patMatchesIntStatePdPat1 :: Int -> DPat0Table -> Word -> [(Int,Int,Binder)] -> [(Int,Int,Binder)]
> patMatchesIntStatePdPat1 cnt dStateTable  w' [] = []
> patMatchesIntStatePdPat1 cnt dStateTable  w' currNfaStateBinders =
>     case {-# SCC "uncons" #-} S.uncons w' of 
>       Nothing -> currNfaStateBinders -- we are done with the matching
>       Just (l,w) -> 
>           let ((i,_,_):_) = currNfaStateBinders  -- i is the current DFA state
>               k           =  l `seq` i `seq` my_hash i l
>           in
>           case {- k `seq` -} IM.lookup k dStateTable of
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
> -}

fusing up the computation for binders

> computeBinders :: [(Int,Int,Binder)] -> IM.IntMap [Int -> Binder -> Binder] -> Int -> [Binder]
> computeBinders currNfaStateBinders fDict cnt = 
>     cm currNfaStateBinders
>     where 
>        cm :: [(Int,Int,Binder)] -> [Binder]
>        cm bs = foldl' k [] bs
>        k :: [Binder] -> (Int,Int,Binder) -> [Binder]
>        k !a (_,!m,!b) = case IM.lookup m fDict of { Nothing -> a; Just !gs -> ((++) a $! (map (\g -> g cnt b) gs)) }  


> {-

general type scheme concatMapl :: (a -> [b]) -> [a] -> [b]


> concatMapl :: ((Int,Int,Binder) -> [Binder]) -> [(Int,Int,Binder)] -> [Binder]
> concatMapl f x = foldl' k [] x
>   where 
>       k a b = a `seq` b `seq` (++) a (f b) -- to make it stricter
> -- same as k !a !b = (++) a (f b) 


> 
> foldl'rnf :: NFData a => (a -> b -> a) -> a -> [b] -> a
> foldl'rnf f z xs = lgo z xs
>    where                      
>       lgo z []     = z      
>       lgo z (x:xs) = lgo z' xs 
>          where 
>             z' = f z x `using` rseq {- was 'rnf' in the realworld haskell book -}
> 

> -}

> 
> concatMap' :: (a -> [b]) -> [a] -> [b]
> concatMap' f x = foldr' ( \ b a -> (++) a $! (f b) ) [] x
> 


> foldr' :: (a -> b -> b) -> b -> [a] -> b
> foldr' f b [] = b
> foldr' f b (a:as) = let b' = f a b 
>                     in b' `seq` 
>                        foldr' f b' as




> patMatchesIntStatePdPat1 :: Int -> DPat0Table (IO) -> Word -> (Int, [Int], BinderGrid (IO)) -> IO (Maybe  (Int, [Int], (BinderGrid (IO))))
> patMatchesIntStatePdPat1 cnt dStateTable w' r@(_,[],_) = return Nothing
> patMatchesIntStatePdPat1 cnt dStateTable w' r@(currDSt, currNSts, binderGrid) = 
>     case S.uncons w' of 
>       Nothing -> return (Just r)
>       Just (!l,w) -> 
>           let k = currDSt `seq` my_hash currDSt l
>           in case IM.lookup k dStateTable of 
>             { Nothing -> return Nothing -- "key missing" which means some letter exists in w but not in r.
>             ; Just (nextDSt, nextNSts, fDict) ->
>                 do { nextBinderGrid <- updateBinderGrid currNSts fDict cnt binderGrid
>                    ; let cnt' = cnt + 1
>                    ; nextNSts `seq` cnt' `seq` w `seq` nextDSt `seq` nextBinderGrid `seq` patMatchesIntStatePdPat1 cnt' dStateTable w (nextDSt, nextNSts, nextBinderGrid) }
>             }

> updateBinderGrid :: [Int] -> IM.IntMap [Int -> Int -> BinderGrid (IO) -> IO (BinderGrid (IO)) ] -> Int -> BinderGrid (IO) -> IO (BinderGrid (IO))
> updateBinderGrid currNSts fDict cnt bg = 
>     foldM (\bg_ nSt -> updateOneState nSt fDict cnt bg_)  bg currNSts

> updateOneState :: Int -> IM.IntMap [Int -> Int -> BinderGrid (IO) -> IO (BinderGrid (IO))] -> Int -> BinderGrid (IO) -> IO (BinderGrid (IO))
> updateOneState nSt fDict cnt bg' = 
>      case IM.lookup nSt fDict of { Nothing -> return bg'
>                                  ; Just !gs -> foldM (\bg'' g -> g cnt nSt bg'') bg' gs }


> patMatchIntStatePdPat1 :: Pat -> Word -> [Env]
> patMatchIntStatePdPat1 p w = 
>   unsafePerformIO $ do 
>      { let
>            (dStateTable,sfinal) = buildDPat0Table p
>            s = 0
>            b = toBinder p
>      ; bg <- bgInit (numOfStates p) (numOfVars p)
>      ; mb <- b `seq` s `seq` dStateTable `seq` (patMatchesIntStatePdPat1 0 dStateTable w (0,[s],bg))
>      ; case mb of 
>        { Nothing -> return []
>        ; Just (_,nSts, bg') ->
>           let nStsFinal = filter (\i -> i `elem` sfinal) nSts
>           in collectPatMatchFromBinderGrid w bg' nStsFinal }  
>      } 

> greedyPatMatch' :: Pat -> Word -> Maybe Env
> greedyPatMatch' p w =
>      first (patMatchIntStatePdPat1 p w)
>   where
>     first (env:_) = return env
>     first _ = Nothing


Compilation


> compilePat ::  PrimMonad m => Pat ->  (DPat0Table m, [Int], Binder, Int, Int)
> compilePat p = (dStateTable, sfinal, b, ns, nv)
>     where 
>           (dStateTable,sfinal) = buildDPat0Table p
>           b = toBinder p
>           ns = numOfStates p 
>           nv = numOfVars p




> patMatchIntStateCompiled :: (DPat0Table (IO), [Int], Binder, Int, Int) -> Word -> IO [Env]
> patMatchIntStateCompiled (dStateTable,sfinal,b,ns,nv) w = do
>   { let s = 0 
>   ; bg <- bgInit ns nv
>   ; let  e = (0,[s],bg)
>   ; mb <- e `seq` b `seq` s `seq` dStateTable `seq` (patMatchesIntStatePdPat1 0 dStateTable w e ) 
>   ; case mb of 
>     { Nothing -> return  []
>     ; Just (_,nSts, bg') ->
>        let nStsFinal  = filter (\i -> i `elem` sfinal) nSts
>        in collectPatMatchFromBinderGrid w bg' nStsFinal }
>   }

> third :: (a,b,c) -> c
> third (_,_,x) = x

> greedyPatMatchCompiled :: (DPat0Table (IO), [Int], Binder,Int,Int) -> Word -> IO (Maybe Env)
> greedyPatMatchCompiled compiled w =
>      do { r <- (patMatchIntStateCompiled compiled w)
>         ; return (first r) }
>   where
>     first (env:_) = return env
>     first _ = Nothing





> -- | The PDeriv backend spepcific 'Regex' type

> newtype Regex m = Regex (DPat0Table m, [Int], Binder, Int, Int) 


-- todo: use the CompOption and ExecOption

> compile :: PrimMonad m => CompOption -- ^ Flags (summed together)
>         -> ExecOption -- ^ Flags (summed together) 
>         -> S.ByteString -- ^ The regular expression to compile
>         -> Either String (Regex m) -- ^ Returns: the compiled regular expression
> compile compOpt execOpt bs = 
>     case parsePat (S.unpack bs) of
>     Left err -> Left ("parseRegex for Text.Regex.PDeriv.ByteString failed:"++show err)
>     Right pat -> Right $ patToRegex pat compOpt execOpt
>     where 
>       patToRegex p _ _ = Regex (compilePat $ simplify p)



> execute :: Regex (IO)    -- ^ Compiled regular expression
>        -> S.ByteString -- ^ ByteString to match against
>        -> IO (Either String (Maybe Env))
> execute (Regex r) bs = liftM Right (greedyPatMatchCompiled r bs)

> regexec :: Regex (IO)   -- ^ Compiled regular expression
>        -> S.ByteString -- ^ ByteString to match against
>        -> IO (Either String (Maybe (S.ByteString, S.ByteString, S.ByteString, [S.ByteString])))
> regexec (Regex r) bs = do 
>  mb <- greedyPatMatchCompiled r bs
>  case mb of
>    Nothing -> return (Right Nothing)
>    Just env ->
>      let pre = case lookup preBinder env of { Just w -> w ; Nothing -> S.empty }
>          post = case lookup subBinder env of { Just w -> w ; Nothing -> S.empty }
>          {- full_len = S.length bs
>          pre_len = S.length pre
>          post_len = S.length post
>          main_len = full_len - pre_len - post_len
>          main_and_post = S.drop pre_len bs
>          main = main_and_post `seq` main_len `seq` S.take main_len main_and_post -}
>          main = case lookup mainBinder env of { Just w -> w ; Nothing -> S.empty }
>          matched = map snd (filter (\(v,w) -> v > 0) env)
>      in return (Right (Just (pre,main,post,matched)))

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

> instance RegexOptions (Regex s) CompOption ExecOption where
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


-- Kenny's example

> long_pat = PPair (PVar 1 ((,) (-1) (-1)) (PE (Star (L 'A') Greedy))) (PVar 2 ((,) (-1) (-1)) (PE (Star (L 'A') Greedy)))
> long_string n = S.pack $ (take 0 (repeat 'A')) ++ (take n (repeat 'B'))

-- p4 = << x : (A|<A,B>), y : (<B,<A,A>>|A) >, z : (<A,C>|C) > 

> p4 = PPair (PPair p_x p_y) p_z
>    where p_x = PVar 1 ((,) (-1) (-1)) (PE (Choice (L 'A') (Seq (L 'A') (L 'B')) Greedy))      
>          p_y = PVar 2 ((,) (-1) (-1)) (PE (Choice (Seq (L 'B') (Seq (L 'A') (L 'A'))) (L 'A') Greedy))
>          p_z = PVar 3 ((,) (-1) (-1)) (PE (Choice (Seq (L 'A') (L 'C')) (L 'C') Greedy))

> input = S.pack "ABAAC"  -- long(posix) vs greedy match


> p5 = PStar (PVar 1 ((,) (-1) (-1)) (PE (Choice (L 'A') (Choice (L 'B') (L 'C') Greedy) Greedy))) Greedy

pattern = ( x :: (A|C), y :: (B|()) )*

> p6 = PStar (PPair (PVar 1 ((,) (-1) (-1)) (PE (Choice (L 'A') (L 'C') Greedy))) (PVar 2 ((,) (-1) (-1)) (PE (Choice (L 'B') Empty Greedy)))) Greedy

pattern = ( x :: ( y :: A, z :: B )* )

> p7 = PVar 1 ((,) (-1) (-1)) (PStar (PPair (PVar 2 ((,) (-1) (-1)) (PE (L 'A'))) (PVar 3 ((,) (-1) (-1)) (PE (L 'B')))) Greedy)

> input7 = S.pack "ABABAB"


pattern = ( x :: A*?, y :: A*)

> p8 = PPair (PVar 1 ((,) (-1) (-1)) (PE (Star (L 'A') NotGreedy))) (PVar 2 ((,) (-1) (-1)) (PE (Star (L 'A') Greedy)))

> input8 = S.pack "AAAAAA"

pattern = ( x :: A*?, y :: A*)

> p9 = PPair (PStar (PVar 1 ((,) (-1) (-1)) (PE (L 'A'))) NotGreedy) (PVar 2 ((,) (-1) (-1)) (PE (Star (L 'A') Greedy)))

pattern = ( x :: (A|B)*?, (y :: (B*,A*)))

> p10 = PPair (PVar 1 ((,) (-1) (-1)) (PE (Star (Choice (L 'A') (L 'B') Greedy) NotGreedy))) (PVar 2 ((,) (-1) (-1)) (PE (Seq (Star (L 'B') Greedy) (Star (L 'A') Greedy))))

> input10 = S.pack "ABA"


pattern = <(x :: (0|...|9)+?)*, (y :: (0|...|9)+?)*, (z :: (0|...|9)+?)*>

> digits_re = foldl' (\x y -> Choice x y Greedy) (L '0') (map L "123456789")

> p11 = PPair (PStar (PVar 1 ((,) (-1) (-1)) (PE (Seq digits_re (Star digits_re Greedy)))) Greedy) (PPair (PStar (PVar 2 ((,) (-1) (-1)) (PE (Seq digits_re (Star digits_re Greedy)))) Greedy) (PPair (PStar (PVar 3 ((,) (-1) (-1)) (PE (Seq digits_re (Star digits_re Greedy)))) Greedy) (PStar (PVar 4 ((,) (-1) (-1)) (PE (Seq digits_re (Star digits_re Greedy)))) Greedy)))

> input11 = S.pack "1234567890123456789-"


> -- Right up34 = compile defaultCompOpt defaultExecOpt (S.pack "(Ab|cD)*")

> s34 = S.pack "aBcD"