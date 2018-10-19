-- Taken from https://gist.github.com/timjb/6258302
module GCurry

import Data.HVect

%access export

public export
total C : Vect k Type -> Type -> Type 
C [] t = t
C (x :: xs) t = x -> C xs t

GCurry : (ts : Vect n Type) -> (HVect ts -> Type) -> Type
GCurry [] t = t []
GCurry (t :: ts) t' = (v : t) -> GCurry ts (t' . (v ::))

gCurry :  {ts : Vect n Type}
       -> {T : HVect ts -> Type}
       -> ((vs : HVect ts) -> T vs)
       -> GCurry ts T
gCurry {ts=[]}          f = f []
gCurry {ts=t::ts} {T=t'} f = \v => gCurry {ts=ts} {T = t' . (v ::)} (\vs => f (v :: vs))

gUncurry :  {ts : Vect n Type}
         -> {T : HVect ts -> Type}
         -> GCurry ts T
         -> (vs : HVect ts)
         -> T vs
gUncurry {ts=[]}          f []        = f
gUncurry {ts=t::ts} {T=t'} f (x :: xs) = gUncurry {ts=ts} {T = t' . (x ::)} (f x) xs
