module State

import Control.Monad.Free

State : Type -> Type -> Type
State s r = s -> (r, s)

return : r -> State s r
return x = (\st => (x, st))

bind : State s a -> (a -> State s b) -> State s b
bind st f s = let (x, s') = st s in f x s'

put : s -> State s ()
put x = (\_ => ((), x))

get : State s s
get = (\s => (s, s))

putInt : State Int ()
putInt = get `bind` (const $ put 10)

runState : State s a -> s -> a
runState st = fst . st

evalState : State s a -> s -> s
evalState st = snd . st

data Tele s c = Get c
              | Put s c
              | Return
