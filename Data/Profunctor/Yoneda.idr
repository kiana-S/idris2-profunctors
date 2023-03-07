module Data.Profunctor.Yoneda

import Data.Profunctor

%default total


public export
record Yoneda p a b where
  constructor MkYoneda
  runYoneda : forall x, y. (x -> a) -> (b -> y) -> p x y
