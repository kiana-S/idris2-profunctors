module Data.Profunctor.Sieve

import Data.Profunctor

%default total


public export
interface (Profunctor p, Functor f) => Sieve p f | p where
  sieve : p a b -> a -> f b


public export
interface (Profunctor p, Functor f) => Cosieve p f | p where
  cosieve : p a b -> f a -> b
