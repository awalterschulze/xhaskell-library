



> {-# LANGUAGE GADTs, BangPatterns #-} 

--------------------------------------------------------------------------------
-- Regular Expression Pattern Matching via Glushkov automata (Position based)
--------------------------------------------------------------------------------

> module Main where

> import Monad
> import List 
> import Data.Bits
> import Char (ord)
> import GHC.IO
> import Data.Int
> import qualified Data.IntMap as IM
> import qualified Data.ByteString.Char8 as S

> import System.IO.Unsafe

------------------------------
-- regular expressions

> data RE where
>   Phi :: RE                      -- empty language
>   Empty :: RE                    -- empty word
>   L :: Char -> Int -> RE                -- single letter with a position number 
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
>     show (L c n) = show c ++ show n
>     show (Choice r1 r2) = ("(" ++ show r1 ++ "|" ++ show r2 ++ ")")
>     show (Seq r1 r2) = ("<" ++ show r1 ++ "," ++ show r2 ++ ">")
>     show (Star r) = (show r ++ "*")


> class IsEmpty a where
>     isEmpty :: a -> Bool

> instance IsEmpty RE where
>   isEmpty Phi = False
>   isEmpty Empty = True
>   isEmpty (Choice r1 r2) = (isEmpty r1) || (isEmpty r2)
>   isEmpty (Seq r1 r2) = (isEmpty r1) && (isEmpty r2)
>   isEmpty (Star r) = True
>   isEmpty (L _ _) = False


annotate add position info to the regex

> newtype State s a = State { runState :: (s -> (a,s)) } 
 
> instance Monad (State s) where
>    -- return :: a -> State s a
>    return a        = State (\s -> (a,s))
>    -- (>>=) :: State s a -> (a -> State s b) -> State s b
>    (State x) >>= f = State (\s -> let (a,s') = x s 
>                                       stb = f a
>                                   in (runState stb) s')

> run :: s -> State s a -> (a,s)
> run s sta = (runState sta) s


> data Env = Env { cnt :: Int
>                } deriving Show

> initEnv :: Env 
> initEnv = Env 0 

> nextCounter :: State Env Int
> nextCounter = State (\env -> let c = (cnt env) + 1
>                                  env' = c `seq` env{cnt=c}
>                              in env' `seq` (c, env'))


annotate a regex with position index

> rAnnotate :: RE -> RE
> rAnnotate r = case run initEnv (rAnn r) of
>              { (r', _ ) -> r' }  

> rAnn :: RE -> State Env RE
> rAnn Phi = return Phi
> rAnn Empty = return Empty
> rAnn (Choice r1 r2) = 
>   do { r1' <- rAnn r1
>      ; r2' <- rAnn r2
>      ; return (Choice r1' r2') }
> rAnn (Seq r1 r2) = 
>   do { r1' <- rAnn r1
>      ; r2' <- rAnn r2
>      ; return (Seq r1' r2') }
> rAnn (Star r) = 
>   do { r' <- rAnn r                
>      ; return (Star r') }
> rAnn (L c _) = 
>   do { i <- nextCounter       
>      ; return (L c i) }


> rFirst :: RE -> [(Char, Int)] 
> rFirst Phi = []
> rFirst Empty = []
> rFirst (L c i) = [(c,i)]
> rFirst (Star r) = rFirst r
> rFirst (Choice r1 r2) = (rFirst r1) ++ (rFirst r2)
> rFirst (Seq r1 r2) = if isEmpty r1 then (rFirst r1) ++ (rFirst r2) else rFirst r1

> rLast :: RE -> [(Char, Int)] 
> rLast Phi = []
> rLast Empty = []
> rLast (L c i) = [(c,i)]
> rLast (Star r) = rLast r
> rLast (Choice r1 r2) = (rLast r1) ++ (rLast r2)
> rLast (Seq r1 r2) = if isEmpty r2 then (rLast r1) ++ (rLast r2) else rLast r2

> rFollow :: RE -> [(Int, Char, Int)]
> rFollow Phi = []
> rFollow Empty = []
> rFollow (L _ _) = []
> rFollow (Choice r1 r2) = (rFollow r1) ++ (rFollow r2)
> rFollow (Seq r1 r2) = (rFollow r1) ++ (rFollow r2) ++ [ (l,c,f) | (_,l) <- rLast r1, (c,f) <- rFirst r2 ]
> rFollow (Star r) = (rFollow r) ++ [ (l,c,f) | (_,l) <- rLast r, (c,f) <- rFirst r ]

> rPos :: RE -> [Int]
> rPos Phi = []
> rPos Empty = []
> rPos (L _ i) = [i]
> rPos (Choice r1 r2) = (rPos r1) ++ (rPos r2) 
> rPos (Seq r1 r2) = (rPos r1) ++ (rPos r2)
> rPos (Star r) = rPos r

> data NFA a l = NFA { states :: [a]
>                    , initStates   :: [a]
>                    , finalStates  :: [a]
>                    , delta  :: [(a,l,a)] 
>                    } deriving Show


> table :: Eq a => [(a,b)] -> [(a,[b])]
> table ps = intern [] ps
>   where intern t [] = t
>         intern t ((k,v):ps) = case lookup k t of 
>                               { Nothing -> intern ((k,[v]):t) ps
>                               ; Just vs -> intern (update k (vs++[v]) t) ps }
>         update k v t = let t' = filter (\(k',_) -> not (k == k')) t
>                        in (k,v):t'


> runNFA :: (Eq a, Eq l) => NFA a l -> [l] -> Bool
> runNFA nfa w = 
>    let xs = runIntern (initStates nfa) (table (map (\(f,s,t) -> ((f,s),t)) (delta nfa))) w
>    in any (\x -> x `elem` finalStates nfa) xs
>    where runIntern :: (Eq a, Eq l) => [a] -> [((a,l),[a])] -> [l] -> [a]
>          runIntern currs _ [] = currs
>          runIntern currs dels (l:ls) = 
>            let nexts = concatMap (\a -> case lookup (a,l) dels of
>                                      { Nothing -> []                        
>                                      ; Just b  -> b }) currs
>            in nexts `seq` runIntern nexts dels ls


> rGlushkov :: RE -> NFA Int Char
> rGlushkov r = let r' = rAnnotate r
>               in NFA{ states = 0:(rPos r')
>                     , initStates = [0]
>                     , finalStates = if isEmpty r then 0:(map snd (rLast r')) else (map snd (rLast r'))
>                     , delta = [ (0,c,f) | (c,f) <- rFirst r' ] ++ (rFollow r') }



> runGlushkov :: RE -> String -> Bool
> runGlushkov r w = 
>    let r' = rAnnotate r   
>        nfa = rGlushkov r'          
>    in runNFA nfa w 


label with default position 0

> l0 c = L c 0

r1 = ((a|b)*,c)

> r1 = Seq (Star (Choice (l0 'a') (l0 'b'))) (l0 'c')



> data Pat where
>  PVar :: Int -> RE -> Pat 
>  PPair :: Pat -> Pat -> Pat  
>  PChoice :: Pat -> Pat -> Pat 
>   deriving Show


> strip :: Pat -> RE 
> strip (PVar _ r) = r
> strip (PPair p1 p2) = Seq (strip p1) (strip p2)
> strip (PChoice p1 p2) = Choice (strip p1) (strip p2)


extending annotate operation for patterns

> pAnnotate :: Pat -> Pat
> pAnnotate p = case run initEnv (pAnn p) of { (p', _ ) -> p' }

> pAnn :: Pat -> State Env Pat
> pAnn (PVar v r) = do { r' <- rAnn r
>                        ; return (PVar v r') }
> pAnn (PPair p1 p2) = do { p1' <- pAnn p1
>                         ; p2' <- pAnn p2 
>                         ; return (PPair p1' p2') }
> pAnn (PChoice p1 p2) = do { p1' <- pAnn p1
>                           ; p2' <- pAnn p2
>                           ; return (PChoice p1' p2') }

extending first, last and follow operations for patterns

the result of pFirst and pLast are  list of tripple, (the letter, the position, and the pattern variable updated)

> pFirst :: Pat -> [(Char, Int, Int)]
> pFirst (PVar v r) = [ (c,i,v) | (c,i) <- rFirst r ]
> pFirst (PPair p1 p2) | isEmpty (strip p1) = pFirst p1 ++ pFirst p2
>                      | otherwise          = pFirst p1
> pFirst (PChoice p1 p2) = pFirst p1 ++ pFirst p2

> pLast :: Pat -> [(Char, Int, Int)]
> pLast (PVar v r) = [ (c,i,v) | (c,i) <- rLast r ]
> pLast (PPair p1 p2) | isEmpty (strip p2) = pLast p1 ++ pLast p2
>                     | otherwise          = pLast p2
> pLast (PChoice p1 p2) = pLast p1 ++ pLast p2

we also introduce the pattern variable updated into the result of the follow operation

> pFollow :: Pat -> [(Int, Char, Int, Int)]
> pFollow (PVar v r) = [ (p, c, q, v) | (p, c, q) <- rFollow r ]
> pFollow (PPair p1 p2) = (pFollow p1) ++ (pFollow p2) 
>                         ++ [ (l,c,f,v) |  (_,l,_) <- pLast p1, (c,f,v) <- pFirst p2 ]
> pFollow (PChoice p1 p2) = (pFollow p1) ++ (pFollow p2)


> pPos :: Pat -> [Int]
> pPos (PVar v r) = rPos r
> pPos (PPair p1 p2) = pPos p1 ++ pPos p2
> pPos (PChoice p1 p2) = pPos p1 ++ pPos p2


> snd2 :: (a,b,c) -> b
> snd2 (_,x,_) = x

we need a different nfa because now the delta should keep track of which pattern variable is updated

> data NFA2 a l = NFA2 { states2 :: [a]
>                    , initStates2   :: [a]
>                    , finalStates2  :: [a]
>                    , delta2  :: [(a,l,a,Int)] 
>                    } deriving Show

> -- return a list of variable bindings
> runNFA2 :: (Eq a, Eq l) => NFA2 a l -> [l] -> [[Int]]
> runNFA2 nfa w = 
>    let xvs = runIntern (zip (initStates2 nfa) (repeat [])) 
>               (table (map (\(f,s,t,v) -> ((f,s),(t,v))) (delta2 nfa))) w
>    in map snd (filter (\(x,v) -> x `elem` finalStates2 nfa) xvs)
>    where runIntern :: (Eq a, Eq l) => [(a,[Int])] -> [((a,l),[(a,Int)])] -> [l] -> [(a,[Int])]
>          runIntern currs _ [] = currs
>          runIntern currs dels (l:ls) = 
>            let nexts = concatMap (\(a,vs) -> case lookup (a,l) dels of
>                                      { Nothing -> []                        
>                                      ; Just bvs -> map (\(b,v) -> (b, (vs++[v]))) bvs }) currs
>            in nexts `seq` runIntern nexts dels ls
> 

> pGlushkov :: Pat -> NFA2 Int Char
> pGlushkov p = let p' = pAnnotate p
>               in NFA2{ states2 = 0:(pPos p')
>                     , initStates2 = [0]
>                     , finalStates2 = if isEmpty (strip p) then 0:(map snd2 (pLast p')) else (map snd2 (pLast p'))
>                     , delta2 = [ (0, c, f, v) | (c,f,v) <- pFirst p']  ++ (pFollow p') 
>                     }



> patMatchGlushkov :: Pat -> String -> [(Int,String)]
> patMatchGlushkov p w = 
>    let p' = pAnnotate p
>        nfa = pGlushkov p'         
>        matches = runNFA2 nfa w
>    in case matches of 
>       { [] -> [] -- no match
>       ; (m:_) -> IM.toList (collect m w IM.empty) }
>    where collect :: [Int] -> String -> IM.IntMap String -> IM.IntMap String
>          collect [] _ m = m
>          collect (i:is) (c:cs) m = 
>                  case IM.lookup i m of
>                      { Just r ->  collect is cs (IM.update (\_ -> Just (r++[c])) i m )
>                      ; Nothing -> collect is cs (IM.insert i [c] m) }



> p4 = PPair (PPair p_x p_y) p_z
>    where p_x = PVar 1 (Choice (l0 'A') (Seq (l0 'A') (l0 'B')))
>          p_y = PVar 2 (Choice (Seq (l0 'B') (Seq (l0 'A') (l0 'A'))) (l0 'A'))
>          p_z = PVar 3 (Choice (Seq (l0 'A') (l0 'C')) (l0 'C'))

> s4 = "ABAAC"



Ungreedy match can be easily adopted in Glushkov 

e.g. consider p = ( x :: a1 * ?, y :: a2 * ) where 1 and 2 are position tags.

first p = [ ( 'a', 1, x) ,  ('a', 2, y) ]

last p  = [ ('a', 1, x), ('a', 2, y) ]

follow p = (follow (x :: a1*?)) ++ (follow  (y :: a2*)) ++ 
        [ (p1,c2,p2,v2) | (c1,p1,v1) <- last (x :: a1*?), (c2,p2,v2) <- first (y :: a2*) ]
         = [ (p, c, p',x) |  (p, c, p') <- follow (a1*?) ] ++ 
           [ (p, c, p',y) |  (p, c, p') <- follow (a2*) ] ++ 
        [ (p1,c2,p2,v2) | (c1,p1,v1) <- last (x :: a1*?), (c2,p2,v2) <- first (y :: a2*) ]
         = [ (1,'a',1,x) ] ++ [ (2,'a',2,y) ] ++ [ (p1,c2,p2,v2) | (c1,p1,v1) <- [('a',1,x)], (c2,p2,v2) <- [('a',2,y)] ]   -- (1)
         = [ (1,'a',1,x) ] ++ [ (2,'a',2,y) ] ++ [ (1,'a',2',y) ] 
Note that for (1) we have all the transitions. Assume during the matching, the transitions are 'tried' in the order
of left to right. Hence (1,'a',1,x) is always tried before (1,'a',2',y), which leads to a greedy matching.

On the other hand, if we swap [ (1,'a',1,x) ]  with  [ (1,'a',2',y) ]  we will have non-greedy matching

hence for a non-greedy match, if a1 is non-greedy
follow (q1,q2) =  [ (p1,c2,p2,v2) | (c1,p1,v1) <- last q1, (c2,p2,v2) <- first q2 ] 
               ++ follow q1 ++ follow q2
       
