module Data.Profunctor.Cayley

import Data.Profunctor
import Data.Profunctor.Costrong
import Data.Profunctor.Traversing
import Data.Profunctor.Mapping
import Data.Profunctor.Sieve

%default total


-- NOTE: This may be better as a type synonym instead of a new type?

||| A profunctor lifted into a functor.
public export
record Cayley {0 k1,k2,k3 : Type} f (p : k1 -> k2 -> k3) a b where
  constructor MkCayley
  runCayley : f (p a b)


export
Functor f => Profunctor p => Profunctor (Cayley f p) where
  dimap f g (MkCayley p) = MkCayley (dimap f g <$> p)
  lmap f (MkCayley p) = MkCayley (lmap f <$> p)
  rmap g (MkCayley p) = MkCayley (rmap g <$> p)

export
Functor f => ProfunctorFunctor (Cayley f) where
  promap f (MkCayley p) = MkCayley (map f p)

export
Monad m => ProfunctorMonad (Cayley m) where
  propure = MkCayley . pure
  projoin (MkCayley p) = MkCayley $ p >>= runCayley

export
Functor f => GenStrong ten p => GenStrong ten (Cayley f p) where
  strongl (MkCayley p) = MkCayley (strongl {ten} <$> p)
  strongr (MkCayley p) = MkCayley (strongr {ten} <$> p)

export
Functor f => GenCostrong ten p => GenCostrong ten (Cayley f p) where
  costrongl (MkCayley p) = MkCayley (costrongl {ten} <$> p)
  costrongr (MkCayley p) = MkCayley (costrongr {ten} <$> p)

export
Functor f => Closed p => Closed (Cayley f p) where
  closed (MkCayley p) = MkCayley (closed <$> p)

export
Functor f => Traversing p => Traversing (Cayley f p) where
  traverse' (MkCayley p) = MkCayley (traverse' <$> p)
  wander f (MkCayley p) = MkCayley (wander f <$> p)

export
Functor f => Mapping p => Mapping (Cayley f p) where
  map' (MkCayley p) = MkCayley (map' <$> p)
  roam f (MkCayley p) = MkCayley (roam f <$> p)

export
Functor g => Sieve p f => Sieve (Cayley g p) (g . f) using Functor.Compose where
  sieve (MkCayley p) x = ($ x) . sieve <$> p


export
mapCayley : (forall x. f x -> g x) -> Cayley f p :-> Cayley g p
mapCayley f (MkCayley p) = MkCayley (f p)
