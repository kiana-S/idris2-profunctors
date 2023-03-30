module Data.Profunctor.Sieve

import Control.Applicative.Const
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


public export
Sieve Morphism Identity where
  sieve (Mor f) = Id . f

||| A named implementation of `Sieve` for function types.
||| Use this to avoid having to use a type wrapper like `Morphism`.
public export
[Function] Sieve (\a,b => a -> b) Prelude.id using Profunctor.Function FunctorId where
  sieve = id

public export
Functor f => Sieve (Kleislimorphism f) f where
  sieve = applyKleisli

public export
Functor f => Sieve (Star f) f where
  sieve = applyStar

public export
Sieve (Forget r) (Const r) where
  sieve (MkForget k) = MkConst . k


public export
Cosieve Morphism Identity where
  cosieve (Mor f) = f . runIdentity

namespace Cosieve
  ||| A named implementation of `Cosieve` for function types.
  ||| Use this to avoid having to use a type wrapper like `Morphism`.
  public export
  [Function] Cosieve (\a,b => a -> b) Prelude.id using Profunctor.Function FunctorId where
    cosieve = id

public export
Functor f => Cosieve (Costar f) f where
  cosieve = applyCostar

public export
Cosieve (Coforget r) (Const r) where
  cosieve (MkCoforget k) = k . runConst
