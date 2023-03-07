module Data.Profunctor.Sieve

import Control.Monad.Identity
import Data.Morphisms
import Data.Profunctor

%default total


public export
interface (Profunctor p, Functor f) => Sieve p f | p where
  sieve : p a b -> a -> f b


export
Sieve Morphism Identity where
  sieve (Mor f) = Id . f

export
[Function] Sieve (\a,b => a -> b) Identity using Profunctor.Function where
  sieve = (Id .)

export
Functor f => Sieve (Kleislimorphism f) f where
  sieve = applyKleisli

export
Functor f => Sieve (Star f) f where
  sieve = applyStar


public export
interface (Profunctor p, Functor f) => Cosieve p f | p where
  cosieve : p a b -> f a -> b

export
Cosieve Morphism Identity where
  cosieve (Mor f) = f . runIdentity

namespace Cosieve
  export
  [Function] Cosieve (\a,b => a -> b) Identity using Profunctor.Function where
    cosieve = (. runIdentity)

export
Functor f => Cosieve (Costar f) f where
  cosieve = applyCostar
