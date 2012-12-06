data Pat where
PVar :: Int -> RE -> Pat
PPair :: Pat -> Pat -> Pat
PChoice :: Pat -> Pat -> Pat
PStar :: Pat -> Pat
PatVar :: Int -> Pat -> Pat
deriving Eq
pdPat :: Pat -> Char -> [(Pat,Env->Env)]
pdPat (PVar x r) l =
let pds = partDeriv r l
in if null pds then []
else [(PVar x (resToRE pds),
\ env -> update (x,l) env)]
pdPat (PPair p1 p2) l =
if (isEmpty (strip p1))
then nub2 ( [(PPair p1’ p2,f) | (p1’,f) <- pdPat p1 l] ++
pdPat p2 l)
else [ (PPair p1’ p2,f) | (p1’,f) <- pdPat p1 l ]
pdPat (PChoice p1 p2) l =
nub2 ( (pdPat p1 l) ++ (pdPat p2 l))
pdPat (this@(PStar p)) l =
[ (PPair p’ this, f) | (p’,f) <- pdPat p l]
pdPat (PatVar x p) l =
[ (PatVar x p’, f . (update (x,l))) | (p’,f) <- pdPat p l]
update :: (Int,Char) -> Env -> Env
update (x,l) [] = [(x,[l])]
update (x,l) ((y,w):env)
| (y == x) = (x,w++[l]) : env
| otherwise = (y,w) : update (x,l) env
nub2 = nubBy ( (p1, ) (p2, ) -> p1 == p2)