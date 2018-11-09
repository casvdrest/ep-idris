module Shell

import Free
import Expr
import HoareState
import Control.Monad.State

incr : Functor f => {auto p : Incr :<: f} -> Int -> Free f ()
incr i = inject (MkIncr i (Pure ()))

recall : Functor f => {auto p : Recall :<: f} -> Free f Int
recall = inject (MkRecall Pure)

tick : Functor f => {auto p1 : Recall :<: f} -> {auto p2 : Incr :<: f} -> Free f Int
tick = do
  val <- recall
  incr 1
  pure val

run : Run f m => Free f a -> m a
run = foldTerm pure runAlgebra

program : Free (Incr :+: Recall) Int
program = tick

runProgramState : Int -> Free (Incr :+: Recall) a -> (a, Int)
runProgramState init prog = runState (run prog) init

runHoare : AssertAtomic s m => (p : Predicate s) -> (q : Predicate s) -> Free f a -> HoareState s m p q a
runHoare p q = foldTerm pure runAlgebra
