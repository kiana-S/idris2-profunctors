module Data.Profunctor.Representable

import Control.Monad.Identity
import Data.Morphisms
import Data.Profunctor
import Data.Profunctor.Costrong
import Data.Profunctor.Sieve

%default total


public export
interface (Sieve p f, Strong p) => Representable p f | p where
  tabulate : (a -> f b) -> p a b


export
Representable Morphism Identity where
  tabulate f = Mor (runIdentity . f)

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
tabulated : (Representable q f, Representable r g) => forall p. Profunctor p =>
              p (q a b) (r a' b') -> p (a -> f b) (a' -> g b')
tabulated = dimap tabulate sieve


public export
interface (Cosieve p f, Costrong p) => Corepresentable p f | p where
  cotabulate : (f a -> b) -> p a b


export
cotabulated : (Corepresentable q f, Corepresentable r g) => forall p. Profunctor p =>
              p (q a b) (r a' b') -> p (f a -> b) (g a' -> b')
cotabulated = dimap cotabulate cosieve
