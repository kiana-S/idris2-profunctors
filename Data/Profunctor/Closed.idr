module Data.Profunctor.Closed

import Data.Profunctor.Types
import Data.Profunctor.Functor
import Data.Profunctor.Strong

%default total


public export
interface Profunctor p => Closed p where
  closed : p a b -> p (x -> a) (x -> b)
