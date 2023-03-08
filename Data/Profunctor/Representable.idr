module Data.Profunctor.Representable

import Control.Monad.Identity
import Data.Morphisms
import Data.Profunctor
import Data.Profunctor.Costrong
import Data.Profunctor.Sieve

%default total


------------------------------------------------------------------------------
-- Interfaces
------------------------------------------------------------------------------


||| A profunctor `p` is representable if it is isomorphic to `Star f` for some `f`.
public export
interface (Sieve p f, Strong p) => Representable p f | p where
  tabulate : (a -> f b) -> p a b


||| A profunctor `p` is representable if it is isomorphic to `Costar f` for some `f`.
public export
interface Cosieve p f => Corepresentable p f | p where
  cotabulate : (f a -> b) -> p a b


export
tabulated : (Representable q f, Representable r g) => forall p. Profunctor p =>
              p (q a b) (r a' b') -> p (a -> f b) (a' -> g b')
tabulated = dimap tabulate sieve

export
cotabulated : (Corepresentable q f, Corepresentable r g) => forall p. Profunctor p =>
              p (q a b) (r a' b') -> p (f a -> b) (g a' -> b')
cotabulated = dimap cotabulate cosieve


------------------------------------------------------------------------------
-- Implementations
------------------------------------------------------------------------------


export
Representable Morphism Identity where
  tabulate f = Mor (runIdentity . f)

||| A named implementation of `Representable` for function types.
||| Use this to avoid having to use a type wrapper like `Morphism`.
export
[Function] Representable (\a,b => a -> b) Identity
    using Sieve.Function Strong.Function where
  tabulate = (runIdentity .)

export
Functor f => Representable (Kleislimorphism f) f where
  tabulate = Kleisli

export
Functor f => Representable (Star f) f where
  tabulate = MkStar

export
Corepresentable Morphism Identity where
  cotabulate f = Mor (f . Id)

namespace Corepresentable
  ||| A named implementation of `Corepresentable` for function types.
  ||| Use this to avoid having to use a type wrapper like `Morphism`.
  export
  [Function] Corepresentable (\a,b => a -> b) Identity using Cosieve.Function where
    cotabulate = (. Id)

export
Functor f => Corepresentable (Costar f) f where
  cotabulate = MkCostar
