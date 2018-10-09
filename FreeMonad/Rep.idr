module Rep 

import HoareState

data St : (s : Type) -> (a : Type) -> Pre s -> Post s a -> Type where
  MkSt  : ((prf : (s >< p)) -> (a, s) >< q (fst prf)) -> St s a p q  
  
get : St s s (\_ => Unit) (\s1, (x, s2) => Unit)
get = MkSt $ \(s ** _) => ((s, s) ** ())
