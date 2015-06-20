



> {-# LANGUAGE GADTs, BangPatterns #-}

--------------------------------------------------------------------------------
-- Regular Expression Pattern Matching via Derivatives
--------------------------------------------------------------------------------

> module Main where

> import Control.Monad
> import Data.List
> import Data.Bits
> import Data.Char (ord)
> import GHC.IOBase
> import GHC.Int
> import qualified Data.IntMap as IM
> import qualified Data.ByteString.Char8 as S


------------------------------
-- regular expressions

> data RE where
>   Phi :: RE                      -- empty language
>   Empty :: RE                    -- empty word
>   L :: Char -> RE                -- single letter
>   Choice :: RE  -> RE  -> RE     -- r1 + r2
>   Seq :: RE  -> RE  -> RE        -- (r1,r2)
>   Star :: RE  -> RE              -- r*
>  deriving Eq

A word is a byte string.

> type Word = S.ByteString

Pretty printing of regular expressions

> instance Show RE where
>     show Phi = "{}"
>     show Empty = "<>"
>     show (L c) = show c
>     show (Choice r1 r2) = ("(" ++ show r1 ++ "|" ++ show r2 ++ ")")
>     show (Seq r1 r2) = ("<" ++ show r1 ++ "," ++ show r2 ++ ">")
>     show (Star r) = (show r ++ "*")


> resToRE :: [RE] -> RE
> resToRE (r:res) = foldl Choice r res
> resToRE [] = Phi


> sigmaRE :: RE -> [Char]
> sigmaRE (L l) = [l]
> sigmaRE (Seq r1 r2) = nub ((sigmaRE r1) ++ (sigmaRE r2))
> sigmaRE (Choice r1 r2) = nub ((sigmaRE r1) ++ (sigmaRE r2))
> sigmaRE (Star r) = sigmaRE r
> sigmaRE Phi = []
> sigmaRE Empty = []

> class IsEmpty a where
>     isEmpty :: a -> Bool

> instance IsEmpty RE where
>   isEmpty Phi = False
>   isEmpty Empty = True
>   isEmpty (Choice r1 r2) = (isEmpty r1) || (isEmpty r2)
>   isEmpty (Seq r1 r2) = (isEmpty r1) && (isEmpty r2)
>   isEmpty (Star r) = True
>   isEmpty (L _) = False


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


> type Range  = (Int,Int)      -- (sub)words represent by range

> data Pat where
>  PVar :: Int -> Maybe Range -> RE -> Pat
>  PPair :: Pat -> Pat -> Pat
>  PChoice :: Pat -> Pat -> Pat
>  PEmpty :: Pat -> Pat       -- used internally to indicate
>                             -- that mkEmpPat function has been applied
>   deriving Show

NOTE: We ignore the 'consumed word' when comparing patterns
      (ie we only compare the pattern structure).
      Essential for later comparisons among patterns.

> instance Eq Pat where
>   (==) (PVar x1 _ r1) (PVar x2 _ r2) = (x1 == x2) && (r1 == r2)
>   (==) (PPair p1 p2) (PPair p1' p2') = (p1 == p1') && (p2 == p2')
>   (==) (PChoice p1 p2) (PChoice p1' p2') = (p1 == p1') && (p2 == p2')
>   (==) _ _ = False


> sigmaPat :: Pat -> [Char]
> sigmaPat (PVar _ _ r) = sigmaRE r
> sigmaPat (PPair p1 p2) = nub (sigmaPat p1 ++ sigmaPat p2)
> sigmaPat (PChoice p1 p2) = nub (sigmaPat p1 ++ sigmaPat p2)
> sigmaPat (PEmpty p) = sigmaPat p

> strip :: Pat -> RE
> strip (PVar _ w r) = r
> strip (PPair p1 p2) = Seq (strip p1) (strip p2)
> strip (PChoice p1 p2) = Choice (strip p1) (strip p2)
> strip (PEmpty p) = strip p





> mkEmpPat :: Pat -> Pat
> mkEmpPat (PVar x w r)
>  | isEmpty r = PVar x w Empty
>  | otherwise = PVar x w Phi
> mkEmpPat (PPair p1 p2) = PPair (mkEmpPat p1) (mkEmpPat p2)
> mkEmpPat (PChoice p1 p2) = PChoice (mkEmpPat p1) (mkEmpPat p2)


> isEmptyPat :: Pat -> Bool
> isEmptyPat (PVar _ w r) = isEmpty r
> isEmptyPat (PPair p1 p2) =  (isEmptyPat p1) && (isEmptyPat p2)
> isEmptyPat (PChoice p1 p2) =  (isEmptyPat p1) || (isEmptyPat p2)
> isEmptyPat (PEmpty p) = isEmptyPat p


> -- Each char letter carries the character and the variable (int)
> -- to which the character will be bound to.
> data Letter = Ch Char Int | Epsilon deriving Eq

> instance Show Letter where
>    show Epsilon = "eps"
>    show (Ch c v) = varMapping v ++ " -> " ++ [c]

> -- | Vars represented as ints, map to symbolic names.
> varMapping 1 = "x"
> varMapping 2 = "y"
> varMapping 3 = "z"
> varMapping _ = error "pl extend"


> newtype State = State Int deriving Eq
> unState (State s) = s
> instance Show State where
>    show (State s) = show s

> type Pos = Int
> newtype Var = Var Int deriving (Eq,Show)

-- the binding of pattern variables to ranges

> type Env = [(Var, Maybe Range)]

> type Binding = Pos -> Env -> Env

> idBnd = error "should be never executed"


> buildEnv :: Pat -> Env
> buildEnv (PVar x w _) = [(Var x,w)]
> buildEnv (PPair p1 p2) = (buildEnv p1) ++ (buildEnv p2)
> buildEnv (PEmpty p) = buildEnv p
> buildEnv (PChoice _ _) = error "PChoice impossible here"



> re :: State -> Var -> RE -> (NFA, State)
> re (State cnt) var (L c) =
>   let s1 = State cnt
>       s2 = State (cnt+1)
>       envFn = \ curpos -> \ env ->
>                    map ( \  (y,w) ->
>                      if var == y
>                      then case w of
>                            Nothing -> (var, Just (curpos,curpos))
>                            Just (i,j) -> (var, Just (i,j+1))
>                            -- append to the back in case of left-to-right
>                       else (y,w) ) env
>       Var v = var
>       delta = (s1,Ch c v,envFn,s2)
>   in (NFA { initial = s1,
>             final = [s2],
>             deltas = [delta] },
>       State $ cnt+2)
>
> re cnt var (Choice r1 r2) =
>   let (nfa1, cnt2) = re cnt var r1
>       (nfa2, cnt3) = re cnt2 var r2
>       start = cnt3
>       ds = (deltas nfa1) ++
>            (deltas nfa2) ++
>            [(start,Epsilon,idBnd,initial nfa1),
>             (start,Epsilon,idBnd,initial nfa2)]
>       fs = final nfa1 ++ final nfa2
>   in (NFA {initial = start, final = fs, deltas = ds},
>       State ((unState start)+1) )
>
> re cnt var (Seq r1 r2) =
>   let (nfa1, cnt2) = re cnt var r1
>       (nfa2, cnt3) = re cnt2 var r2
>       start = initial nfa1
>       ds = (deltas nfa1) ++
>            (deltas nfa2) ++
>            map (\f -> (f, Epsilon, idBnd, initial nfa2)) (final nfa1)
>       fs = final nfa2
>   in (NFA {initial = start, final = fs, deltas = ds},
>       cnt3 )
>
> re cnt var (Star r) =
>   let (nfa, cnt2) = re cnt var r
>       start = cnt2
>       ds = deltas nfa ++
>            [(start, Epsilon, idBnd, initial nfa)] ++
>            map (\f -> (f, Epsilon, idBnd, start)) (final nfa)
>       fs = [start]
>    in (NFA {initial = start, final = fs, deltas = ds},
>       State ((unState start)+1) )

> pat :: State -> Pat -> (NFA, State)
> pat cnt (PVar x _ r) = re cnt (Var x) r
>
> pat cnt (PChoice p1 p2) =
>   let (nfa1, cnt2) = pat cnt p1
>       (nfa2, cnt3) = pat cnt2 p2
>       start = cnt3
>       ds = (deltas nfa1) ++
>            (deltas nfa2) ++
>            [(start,Epsilon,idBnd,initial nfa1),
>             (start,Epsilon,idBnd,initial nfa2)]
>       fs = final nfa1 ++ final nfa2
>   in (NFA {initial = start, final = fs, deltas = ds},
>       State ((unState start)+1) )
>
> pat cnt (PPair p1 p2) =
>   let (nfa1, cnt2) = pat cnt p1
>       (nfa2, cnt3) = pat cnt2 p2
>       start = initial nfa1
>       ds = (deltas nfa1) ++
>            (deltas nfa2) ++
>            map (\f -> (f, Epsilon, idBnd, initial nfa2)) (final nfa1)
>       fs = final nfa2
>   in (NFA {initial = start, final = fs, deltas = ds},
>       cnt3 )

> data NFA = NFA { initial :: State
>                , final :: [State]
>                , deltas :: [(State,Letter, Binding,State)] }


> instance Show NFA where
>   show nfa = "initial: " ++ show (initial nfa) ++ "\n" ++
>              "final: " ++ show (final nfa) ++ "\n" ++
>              "deltas: " ++
>                (concat $ (map ( \ (s1,l,_,s2) -> show (s1,l,s2) ++ "\n") (deltas nfa)))

> data NFAMeasure = NFAMeasure { noOfStates :: Int,
>                                noOfTransitions :: Int}
>                   deriving Show

> measureNFA p =
>   let nfa = buildNFA p
>   in NFAMeasure { noOfStates = length $
>                                  nub $ concat $ map(\(s1,_,_,s2) ->
>                                                        [s1,s2])
>                                                 (deltas nfa),
>                   noOfTransitions = length $ deltas nfa }


> nfaToDot nfa =
>  unlines $ ["digraph G {"]
>            ++ map (\(s1,l,_,s2) ->
>                       show s1 ++ " -> " ++ show s2
>                       ++ "[label=\"" ++ show l ++ "\"];")
>                   (deltas nfa)
>            ++ [" 0 -> " ++ show (initial nfa) ++ ";",
>                "0 [shape = point];"]
>            ++ map (\s -> show s ++ "[shape = circle];")
>                   nonFinalStates
>            ++ map (\s -> show s ++ "[shape = doublecircle];")
>                   (final nfa)
>            ++ ["}"]
>  where
>    nonFinalStates = filter (\s -> not $ elem s $ final nfa)
>                            (nub $ concat $
>                                     map (\(s1,_,_,s2) -> [s1,s2])
>                                         (deltas nfa))

> check x p = (p x) `seq` x

> imlookup nfa st ch = check
>      [ (nextstate, bnd) | (st',l',bnd,nextstate) <- deltas nfa,
>                           st == st',
>                           case l' of
>                              Epsilon -> False
>                              Ch ch' _ -> ch == ch' ]
>      (\xs -> length xs == 1) -- in case of Thompson NFA

> {-
> closure nfa states =
>  states ++
>  [ (s2,f)   |  (s, f) <- states,
>                (s1,l,_,s2) <- deltas nfa,
>                s1 == s, l == Epsilon ]
> -}

build epsilon-closure

can there be cycles ???


Version1: non-greedy, need to follow epsilon transitions depth-first

> {-
> closure nfa states =
>   fixCl states
>         ( \ sts ->
>              [ (s2,f) | (s, f) <- sts,
>                         (s1,l,_,s2) <- deltas nfa,
>                         s1 == s, l == Epsilon ])
>         states

> fixCl acc f states =
>   let next = f states
>   in if next == []
>      then acc
>      else fixCl (acc++next) f next
> -}

Version2: greedy, follow epsilon transitions depth-first

> closure1 nfa (s,f) =
>   [ (s2,f) | (s1,l,_,s2) <- deltas nfa,
>              s1 == s, l == Epsilon ]

> closure nfa states =
>     foldl ( \ acc -> \st ->
>              let sts = closure1 nfa st
>              in if sts == []
>                 then acc++[st]
>                 else acc++[st] ++ closure nfa sts)
>                      -- depth-first traversal
>            []
>            states



keep first pair (s1,f) which corresponds to the greedy match

> nub2 = nubBy ( \ (s1,_) (s2,_) -> s1 == s2)

> lPM :: NFA -> Pat -> Word -> Maybe Env
> lPM nfa p w =
>   let match curstates curpos w =
>        case (S.uncons w) of
>          Nothing ->
>            map ( \ (st, env) -> env)
>               (filter ( \ (st, _) -> elem st (final nfa)) curstates)
>          Just (l,w') ->
>            let next' = [ (st', f curpos env)  | (st, env) <- curstates,
>                                                 (st', f) <- imlookup nfa st l ]
>                next'' = closure nfa next'
>                next = nub2 next''
>                nextpos = curpos+1
>                cur = curstates
>            in --error ((show next') ++ "\n" ++ (show next'') ++ "\n" ++ (show next))
>               cur `seq` next' `seq` next'' `seq` match next nextpos w'
>       initEnv = buildEnv p
>   in case (match (closure nfa [(initial nfa, initEnv)]) 1 w) of
>       (env:_) -> Just env
>       [] -> Nothing


> patMatch p w =
>   let start = State 1
>       (nfa, _) = pat start p
>   in lPM nfa p w


> buildNFA p =
>   let start = State 1
>       (nfa, _) = pat start p
>   in nfa

> buildDot = nfaToDot . buildNFA

tests

> ltest4c n m = patMatch (big_pat n) (big_string m)

> em = Nothing


> big_pat n = pair n
>
>  where
>     pvar n r = PVar n em r
>     reg = Star (Choice (L 'A') (L 'B'))
>     pair 0 = PVar 0 em reg
>     pair n = PPair (pair (n-1)) (pvar n reg)

> big_pat2 n = pair n
>
>  where
>      pvar n r = PVar n em r
>      reg = Star (Choice (L 'A') (L 'B'))
>      pair 0 = PVar 0 em reg
>      pair n = PPair (pvar n reg) (pair (n-1))

> big_string n = S.pack  (take n string)
>     where string = "AB" ++ string

> pvar n = (PVar n em (Star (L 'A')))

> r = (Choice (Star (Seq (L 'A') (L 'B'))) (L 'B'))   -- ((A,B)*|B)
> p = PPair (pvar 1) (PVar 2 em r)                    -- <x:A*,y:((A,B)*|B)>


> p4 = PPair (PPair p_x p_y) p_z
>    where p_x = PVar 1  em (Choice (L 'A') (Seq (L 'A') (L 'B')))
>          p_y = PVar 2  em (Choice (Seq (L 'B') (Seq (L 'A') (L 'A'))) (L 'A'))
>          p_z = PVar 3  em (Choice (Seq (L 'A') (L 'C')) (L 'C'))

> p4a = PPair p_x (PPair p_y p_z)
>    where p_x = PVar 1  em (Choice (L 'A') (Seq (L 'A') (L 'B')))
>          p_y = PVar 2  em (Choice (Seq (L 'B') (Seq (L 'A') (L 'A'))) (L 'A'))
>          p_z = PVar 3  em (Choice (Seq (L 'A') (L 'C')) (L 'C'))

> input = S.pack "ABAAC"  -- long(posix) vs greedy match

> p4' = PPair p_x (PPair p_y p_z)
>   where p_x = PVar 1  em (Choice (L 'A') (Seq (L 'A') (L 'B')))
>         p_y = PVar 2  em (Choice (Seq (L 'B') (Seq (L 'A') (L 'A'))) (L 'A'))
>         p_z = PVar 3  em (Choice (Seq (L 'A') (L 'C')) (L 'C'))

> p4b' = PPair (PPair p_x p_y) p_z
>   where p_x = PVar 1  em (Choice (L 'A') (Seq (L 'A') (L 'B')))
>         p_y = PVar 2  em (Choice (Seq (L 'B') (Seq (L 'A') (L 'A'))) (L 'A'))
>         p_z = PVar 3  em (Choice (Seq (L 'A') (L 'C')) (L 'C'))


> p8 = PVar 1 em (Choice (L 'A') (L 'B'))

> p9 = PVar 1 em (L 'A')

> p10 = PVar 1 em (Star (L 'A'))

> p11 = PPair p9 (PVar 2 em (Star (L 'A')))

> p12 = PPair (PVar 1 em (L 'A')) (PVar 2 em (L 'A'))

> p13 = PVar 1 em (Star (Choice (L 'A') (L 'B')))

> p14 = PPair (PVar 1 em (Star (L 'A'))) (PVar 2 em (Star (L 'A')))

> p15 = PVar 1  em (Choice (L 'A') (Seq (L 'A') (L 'B')))

> aa = S.pack "AA"
