module HoareState

Pre : {s : Type} -> Type
Pre {s} = s -> Bool

Post : {s : Type} -> Type
Post {s} = s -> Bool

data HoareState : (s : Type) -> (a : Type) -> Type where
  HState : (p : Pre {s = s}) -> (q : Post {s = s}) -> (s -> (Maybe a, s)) -> HoareState s a

implementation Functor (HoareState s) where
  map f (HState p q st) =
    HState p q (\s =>
      let (v, s') =
        st s in
      (f <$> v, s')
    )

implementation Applicative (HoareState s) where
  pure a = HState (const True) (const True) (\s => (Just a, s))
  (HState p q st) <*> (HState p' q' st') =
    HState (\s =>
      p s && p' s
    ) (\s =>
      q s && q' s
    ) (\s =>
      let (f, _) =
        st s in
      let (v, s') =
        st' s in
      (f <*> v, s')
    )

implementation Monad (HoareState m) where
  (HState p q st) >>= f =
    HState (\s =>
      let (v, s') =
        st s in
      case v of
        Nothing  => False
        (Just x) =>
          let (HState p' _ _) =
            f x in
          p s && (p' s || (not $ q s))
    ) (\s =>
      let (v, s') =
        st s in
      case v of
        Nothing => False
        (Just x) =>
        let (HState _ q' st') =
          f x in
        let (v', s'') =
          st' s' in
        case v' of
          Nothing => False
          Just x  => ?hole 
    ) (\s =>

    )
