> module Text.Regex.PDeriv.Translate 
>     ( translate ) where
>         

A translation schema from the external syntax (ERE) to our interal syntax (xhaskell style pattern)


> import Control.Monad.State -- needed for the translation scheme
> import Text.Regex.PDeriv.ExtPattern
> import Text.Regex.PDeriv.Pattern
> import Text.Regex.PDeriv.RE
> import Char (chr)

There are two rules.
e ~> p
and
e => r

First we need to define a state monad so that we can assign number to groups and non-groups.

> data TState = TState { ngi :: NGI
>                      , gi :: GI
>                      , anchorStart :: Bool
>                      , anchorEnd :: Bool } -- the state for trasslation
>             deriving Show

> initTState = TState { ngi = -1, gi = 1, anchorStart = False, anchorEnd = False }

> type NGI = Int -- the non group index

> type GI = Int -- the group index

getters and putters

> getNGI :: State TState NGI
> getNGI = do { st <- get
>             ; return $ ngi st
>             }

> getIncNGI :: State TState NGI -- get then increase
> getIncNGI = do { st <- get
>                ; let i = ngi st
>                ; put st{ngi=(i-1)} 
>                ; return i
>                }

> getGI :: State TState GI
> getGI = do { st <- get
>            ; return $ gi st
>            }

> getIncGI :: State TState GI -- get then increase 
> getIncGI = do { st <- get
>               ; let i = gi st
>               ; put st{gi=(i+1)}
>               ; return i
>               }

> getAnchorStart :: State TState Bool
> getAnchorStart = do { st <- get
>                     ; return (anchorStart st)
>                     }

> setAnchorStart :: State TState ()
> setAnchorStart = do { st <- get
>                     ; put st{anchorStart=True}
>                     }

> getAnchorEnd :: State TState Bool
> getAnchorEnd  = do { st <- get
>                    ; return (anchorEnd st)
>                    }

> setAnchorEnd :: State TState ()
> setAnchorEnd = do { st <- get
>                   ; put st{anchorEnd=True}
>                   }



> -- | Translating external pattern to internal pattern
> translate :: EPat -> Pat
> translate epat = case runState (p_trans epat) initTState of
>                  (pat, state) ->
>                    let hasAnchorS = anchorStart state
>                        hasAnchorE = anchorEnd state
>                        i = ngi state
>                    in case (hasAnchorS, hasAnchorE) of
>                         (True, True) -> pat 
>                         (True, False) -> PPair pat (PVar (i-1) Nothing (Star anychar))
>                         (False, True) -> PPair (PVar (i-1) Nothing (Star anychar)) pat -- todo: we need ungreedy here.
>                         (False, False) -> PPair (PVar (i-1) Nothing (Star anychar)) (PPair pat (PVar (i-2) Nothing (Star anychar))) -- todo: we need ungreedy here.
>                    

the translation scheme

e ~> p

convention:
a,b are non group indices.
x,y,z are group indices

> p_trans :: EPat -> State TState Pat
> p_trans epat = 
>     case epat of
>       -- () ~> a :: ()
>     { EEmpty ->
>       do { i <- getIncNGI
>          ; return ( PVar i Nothing Empty )
>          }
>       {-
>         e => r
>         -----------------
>         ( e ) ~> x :: r
>       -}
>     ; EGroup e ->
>       do { i <- getIncGI
>          ; r <- r_trans e
>          ; return ( PVar i Nothing r )
>          }
>     ; EOr es -> 
>         {-
>           e1 ~> p1  e2 ~> p2
>           -------------------
>             e1|e2 ~> p1|p2
>          -}
>       do { ps <- mapM p_trans es
>          ; case ps of
>            { (p':ps') -> 
>               return (foldl (\xs x -> PChoice xs x) p' ps')
>            ; [] -> error "an empty choice enountered." -- todo : capture the error in the monad state
>            }
>          }
>     ; EConcat es ->
>         {- 
>            e1 ~> p1  e2 ~> p2
>            ---------------------
>              (e1,e2) ~> (p1,p2)
>          -} 
>         do { ps <- mapM p_trans es
>            ; case reverse ps of  -- to make sure it is right assoc
>              { (p':ps') -> 
>                    return (foldl (\xs x -> PPair x xs) p' ps')
>              ; [] -> error "an empty sequence enountered." -- todo : capture the error in the moand state
>              }
>            }
>     ; EOpt e ->
>       {- 
>          todo : not sure whether this makes sense
>            e => r
>          -------------------
>            e? ~> a :: (r|())
>        -}
>       do { r <- r_trans e
>          ; i <- getIncNGI 
>          ; let p = (PVar i Nothing (Choice r Empty))
>          ; return p
>          }
>     ; EPlus e ->
>       {- 
>          todo : not sure whether this makes sense
>            e => r
>          -------------------
>            e+ ~> a :: r+
>        -}
>       do { r <- r_trans e
>          ; i <- getIncNGI 
>          ; let p = (PVar i Nothing (Seq r (Star r)))
>          ; return p
>          }
>     ; EStar e -> 
>       {- 
>          todo : not sure whether this makes sense
>            e => r
>          -------------------
>            e*~> a :: r*
>        -}
>       do { r <- r_trans e
>          ; i <- getIncNGI 
>          ; let p = (PVar i Nothing (Star r))
>          ; return p
>          }
>     ; EBound e low (Just high) ->
>         {-
>             e => r  
>             r1 = take l (repeat r)
>             r2 = take (h-l) (repeat r?)
>             r' = (r1,r2)
>           -------------------------------------
>             e{l,h} ~> a :: r' 
>          -}
>       do { r <- r_trans e
>          ; i <- getIncNGI
>          ; let r1s = take low $ repeat r
>                r1 = case r1s of 
>                     { [] -> Empty
>                     ; (r':rs') -> foldl (\ rs r -> Seq rs r) r' rs'
>                     }
>                r2s = take (high - low) $ repeat (Choice r Empty)
>                r2 = case r2s of
>                     { [] -> Empty
>                     ; (r':rs') -> foldl (\ rs r -> Seq rs r) r' rs'
>                     }
>                r3 = case (r1,r2) of 
>                       (Empty, Empty) -> Empty
>                       (Empty, _    ) -> r2
>                       (_    , Empty) -> r1
>                       (_    , _    ) -> Seq r1 r2
>                p = PVar i Nothing r3
>          ; return p
>          }
>     ; EBound e low Nothing ->
>         {-
>             e => r  
>             r1 = take l (repeat r)
>             r' = (r1,r*)
>           -------------------------------------
>             e{l,} ~> a :: r' 
>          -}
>       do { r <- r_trans e
>          ; i <- getIncNGI
>          ; let r1s = take low $ repeat r
>                r1 = case r1s of 
>                     { [] -> Empty
>                     ; (r':rs') -> foldl (\ rs r -> Seq rs r) r' rs'
>                     }
>                r2 = Seq r1 (Star r)
>                p = PVar i Nothing r2
>          ; return p
>          }
>     ; ECarat -> 
>       -- currently we anchor the entire expression 
>       -- regardless of where ^ appears, we turn the subsequent
>       -- ECarat into literal,
>       do { f <- getAnchorStart
>          ; if f 
>            then do { i <- getIncNGI -- not the first carat
>                    ; let r = L '^'
>                          p = PVar i Nothing r
>                    ; return p
>                    }
>            else do { setAnchorStart -- the first carat
>                    ; i <- getIncNGI
>                    ; let r = Empty
>                          p = PVar i Nothing r
>                    ; return p
>                    }
>          }
>     ; EDollar -> 
>           -- similar to carat, except that we will not treat
>           -- the subsequent EDollar as literal.
>       do { f <- getAnchorEnd
>          ; if f
>            then return ()
>            else setAnchorEnd
>          ; i <- getIncNGI
>          ; let r = Empty
>                p = PVar i Nothing r
>          ; return p
>          }
>     ; EDot -> 
>         --  . ~> a :: \Sigma
>       do { i <- getIncNGI
>          ; let r = anychar
>                p = PVar i Nothing r
>          ; return p
>         }
>     ; EAny cs ->
>         -- [ abc ] ~> a :: 'a'|'b'|'c'
>       do { i <- getIncNGI
>          ; let r = char_list_to_re cs
>                p = PVar i Nothing r
>          ; return p
>          }
>     ; ENoneOf cs ->
>         -- [^ abc] ~> a :: \Sigma - 'a'|'b'|'c'
>       do { i <- getIncNGI
>          ; let r = char_list_to_re (filter (\c -> not (c `elem` cs )) sigma)
>                p = PVar i Nothing r
>          ; return p
>          }
>     ; EEscape c ->
>         --  \\c ~> a :: L c
>       do { i <- getIncNGI 
>          ; let p = PVar i Nothing (L c)
>          ; return p 
>          }
>     ; EChar c ->
>         -- c ~> a :: L c
>       do { i <- getIncNGI
>          ; let p = PVar i Nothing (L c)
>          ; return p
>          }
>     }


> char_list_to_re (c:cs) = foldl (\ r c' -> Choice r (L c')) (L c) cs
> char_list_to_re [] = error "char_list_to_re expects non-empty list"

> alphas = char_list_to_re (['a'..'z'] ++ ['A'..'Z'])

> digits = char_list_to_re ['0'..'9']

> sigma = map chr [0 .. 127]

> anychar = char_list_to_re sigma


e => r


> r_trans :: EPat -> State TState RE
> r_trans e = 
>     case e of 
>     { EEmpty -> 
>       {-
>         () => ()
>        -}
>       return Empty
>     ; EGroup e ->
>       {-
>          e => r
>         ----------
>         (e) => r
>        -}
>       r_trans e
>     ; EOr es ->
>       {-
>         e1 => r1 e2 => r2
>       -------------------
>         e1|e2 => r1|r2
>        -}
>       do { rs <- mapM r_trans es
>          ; case rs of
>            { [] -> return Phi
>            ; (r:rs) -> return (foldl (\ xs x -> Choice xs x) r rs)
>            }
>          }
>     ; EConcat es ->
>       {-
>         e1 => r1  e2 => r2
>        ----------------------
>         (e1,e2) => (r1,r2)
>        -}
>       do { rs <- mapM r_trans es
>          ; case rs of
>            { [] -> return Empty
>            ; (r:rs) -> return (foldl (\ xs x -> Seq xs x) r rs)
>            }
>          }
>     ; EOpt e -> 
>       {-
>           e => r
>         -----------
>           e? => r?
>        -}
>       do { r <- r_trans e
>          ; return (Choice r Empty)
>          }
>     ; EPlus e -> 
>       {-
>         e => r
>         ---------------
>           e+ => (r,r*)
>        -}
>       do { r <- r_trans e
>          ; return (Seq r (Star r))
>          }
>     ; EStar e -> 
>       {-
>         e => r
>         ----------------
>           e* => r*
>        -}
>       do { r <- r_trans e
>          ; return (Star r)
>          }
>     ; EBound e low (Just high) ->
>       {-
>         e => r
>         r1 = take l (repeat r)
>         r2 = take (h-l) (repeat r?)
>         r' = (r1,r2)         
>         -----------------
>           e{l:h} => r'
>        -}
>       do { r <- r_trans e
>          ; let r1s = take low $ repeat r
>                r1 = case r1s of
>                     { [] -> Empty
>                     ; (r':rs') -> foldl (\ rs r -> Seq rs r) r' rs'
>                     }
>                r2s = take (high - low) $ repeat (Choice r Empty)
>                r2 = case r2s of
>                     { [] -> Empty
>                     ; (r':rs') -> foldl (\ rs r -> Seq rs r) r' rs'
>                     }
>                r3 = case (r1,r2) of
>                       (Empty, Empty) -> Empty
>                       (Empty, _    ) -> r2
>                       (_    , Empty) -> r1
>                       (_    , _    ) -> Seq r1 r2
>          ; return r3
>          }
>     ; EBound e low Nothing -> 
>         {-
>             e => r  
>             r1 = take l (repeat r)
>             r' = (r1,r*)
>           -------------------------------------
>             e{l,} => r' 
>          -}
>       do { r <- r_trans e
>          ; let r1s = take low $ repeat r
>                r1 = case r1s of 
>                     { [] -> Empty
>                     ; (r':rs') -> foldl (\ rs r -> Seq rs r) r' rs'
>                     }
>                r2 = Seq r1 (Star r)
>          ; return r2
>          }
>     ; ECarat -> 
>         -- '^' => '^'
>         return (L '^')
>     ; EDollar -> 
>         -- '$' => '$'
>         return (L '$')
>     ; EDot -> 
>         -- . => \Sigma
>         return anychar
>     ; EAny cs ->
>       -- [ abc ] =>  'a'|'b'|'c'
>         return (char_list_to_re cs)
>     ; ENoneOf cs ->
>       -- [^ abc] => \Sigma - 'a'|'b'|'c'
>         return $ char_list_to_re (filter (\c -> not (c `elem` cs )) sigma)
>     ; EEscape c ->
>       -- \\c => c
>         return $ L c
>     ; EChar c ->
>       -- c => c
>         return $ L c
>     }
>           

