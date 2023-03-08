module Data.Profunctor.Sieve

import Control.Monad.Identity
import Data.Morphisms
import Data.Profunctor

%default total


------------------------------------------------------------------------------
-- Interfaces
------------------------------------------------------------------------------


||| A profunctor `p` is a sieve on `f` if it is a subprofunctor of `Star f`.
public export
interface (Profunctor p, Functor f) => Sieve p f | p where
  sieve : p a b -> a -> f b


||| A profunctor `p` is a cosieve on `f` if it is a subprofunctor of `Costar f`.
public export
interface (Profunctor p, Functor f) => Cosieve p f | p where
  cosieve : p a b -> f a -> b


------------------------------------------------------------------------------
-- Implementations
------------------------------------------------------------------------------


export
Sieve Morphism Identity where
  sieve (Mor f) = Id . f

||| A named implementation of `Sieve` for function types.
||| Use this to avoid having to use a type wrapper like `Morphism`.
export
[Function] Sieve (\a,b => a -> b) Identity using Profunctor.Function where
  sieve = (Id .)

export
Functor f => Sieve (Kleislimorphism f) f where
  sieve = applyKleisli

export
Functor f => Sieve (Star f) f where
  sieve = applyStar


export
Cosieve Morphism Identity where
  cosieve (Mor f) = f . runIdentity

namespace Cosieve
  ||| A named implementation of `Cosieve` for function types.
  ||| Use this to avoid having to use a type wrapper like `Morphism`.
  export
  [Function] Cosieve (\a,b => a -> b) Identity using Profunctor.Function where
    cosieve = (. runIdentity)

export
Functor f => Cosieve (Costar f) f where
  cosieve = applyCostar
