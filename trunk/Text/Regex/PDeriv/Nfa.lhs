----------------
-- NFA Stuff


> {-# LANGUAGE GADTs, MultiParamTypeClasses, FunctionalDependencies,
>     FlexibleInstances, TypeSynonymInstances, FlexibleContexts #-} 

> module Text.Regex.PDeriv.Nfa where 

> import List 


> class Nfa s a | s -> a where
>    pDeriv :: s -> a -> [s]
>    sigma :: s -> [a]
>    empty :: s -> Bool

A function that builds an NFA 

> buildNFA :: (Nfa s a, Eq s) => s -> NFA s a
> buildNFA init = NFA { all_states = all
>                     , delta_states = delta
>                     , init_states = [init]
>                     , final_states = final }
>   where
>      (all, delta) = builder [] [] [init]
>      final = [s | s <- all, empty s]
>      builder acc_states acc_delta [] = (acc_states, acc_delta)
>      builder acc_states acc_delta curr_states =
>        let all_sofar_states = acc_states ++ curr_states
>            new_delta = [ (s, l, s') | s <- curr_states, l <- sigma s, s' <- pDeriv s l]
>            new_states = nub [new_s | s <- curr_states, l <- sigma s, 
>                                     new_s <- pDeriv s l, not (elem new_s all_sofar_states)]
>        in builder all_sofar_states (acc_delta ++ new_delta) new_states


> data NFA s a = NFA { all_states :: [s]
>                    , delta_states :: [(s, a, s)]
>                    , init_states :: [s]
>                    , final_states :: [s] }
>                 deriving Show


optimized NFA using Int to represent states, IntMap to represent delta

> data SNFA s a = SNFA { mapping_states :: s -> Int
>                        , sall_states :: [Int]
>                        , sdelta_states :: [(Int,a,Int)]
>                        , sinit_states :: [Int]
>                        , sfinal_states :: [Int] }
>                 


> instance Show a => Show (SNFA s a) where
>   show s = "SNFA:\n" ++ show (sall_states s) ++ "\n"
>                      ++ show (sdelta_states s) ++ "\n"
>                      ++ show (sinit_states s) ++ "\n"
>                      ++ show (sfinal_states s)

> toSNFA :: (Eq s)  => NFA s a -> SNFA s a
> toSNFA (NFA { all_states = all
>             , delta_states = delta
>             , init_states = init
>             , final_states = final }) = 
>     let -- generate mapping from states to Int
>         mapping = all `seq` \x -> let (Just i) = findIndex (x ==) all in i 
>     in  SNFA { mapping_states = mapping
>              , sall_states = [0..(length all)-1]
>              , sdelta_states = map (\ (p,x,q) -> (mapping p,x,mapping q)) delta
>              , sinit_states = map mapping init
>              , sfinal_states = map mapping final }


> nofAllStates (NFA {all_states = all}) = length all
> nofDelta (NFA {delta_states = delta}) = length delta
> nofInitStates (NFA {init_states = init}) = length init
> nofFinalStates (NFA {final_states = final}) = length final 