module Data.Profunctor.Yoneda

import Data.Profunctor
import Data.Profunctor.Traversing
import Data.Profunctor.Mapping
import Data.Profunctor.Sieve

%default total


public export
record Yoneda p a b where
  constructor MkYoneda
  runYoneda : forall x, y. (x -> a) -> (b -> y) -> p x y

export
Profunctor (Yoneda p) where
  lmap f (MkYoneda p) = MkYoneda $ \l,r => p (f . l) r
  rmap f (MkYoneda p) = MkYoneda $ \l,r => p l (r . f)
  dimap f g (MkYoneda p) = MkYoneda $ \l,r => p (f . l) (r . g)

export
ProfunctorFunctor Yoneda where
  promap f (MkYoneda p) = MkYoneda $ f .: p

export
ProfunctorMonad Yoneda where
  propure p = MkYoneda $ \l,r => dimap l r p
  projoin (MkYoneda p) = p id id

export
ProfunctorComonad Yoneda where
  proextract (MkYoneda p) = p id id
  produplicate p = MkYoneda $ \l,r => dimap l r p

export
yonedaEqv : Profunctor p => p a b <=> Yoneda p a b
yonedaEqv = MkEquivalence propure proextract

export
Functor (Yoneda p a) where
  map = rmap

export
GenStrong ten p => GenStrong ten (Yoneda p) where
  strongl = propure . strongl {ten,p} . proextract
  strongr = propure . strongr {ten,p} . proextract

export
Closed p => Closed (Yoneda p) where
  closed = propure . closed . proextract

export
Traversing p => Traversing (Yoneda p) where
  traverse' = propure . traverse' . proextract
  wander f = propure . wander f . proextract

export
Mapping p => Mapping (Yoneda p) where
  map' = propure . map' . proextract
  roam f = propure . roam f . proextract

export
Sieve p f => Sieve (Yoneda p) f where
  sieve = sieve . proextract

export
Cosieve p f => Cosieve (Yoneda p) f where
  cosieve = cosieve . proextract


public export
data Coyoneda : (p : Type -> Type -> Type) -> Type -> Type -> Type where
  MkCoyoneda : (a -> x) -> (y -> b) -> p x y -> Coyoneda p a b


export
Profunctor (Coyoneda p) where
  lmap f (MkCoyoneda l r p) = MkCoyoneda (l . f) r p
  rmap f (MkCoyoneda l r p) = MkCoyoneda l (f . r) p
  dimap f g (MkCoyoneda l r p) = MkCoyoneda (l . f) (g . r) p

export
ProfunctorFunctor Coyoneda where
  promap f (MkCoyoneda l r p) = MkCoyoneda l r (f p)

export
ProfunctorMonad Coyoneda where
  propure = MkCoyoneda id id
  projoin (MkCoyoneda l r p) = dimap l r p

export
ProfunctorComonad Coyoneda where
  proextract (MkCoyoneda l r p) = dimap l r p
  produplicate = MkCoyoneda id id

export
coyonedaEqv : Profunctor p => p a b <=> Coyoneda p a b
coyonedaEqv = MkEquivalence propure proextract

export
Functor (Coyoneda p a) where
  map = rmap

export
GenStrong ten p => GenStrong ten (Coyoneda p) where
  strongl = propure . strongl {ten,p} . proextract
  strongr = propure . strongr {ten,p} . proextract

export
Closed p => Closed (Coyoneda p) where
  closed = propure . closed . proextract

export
Traversing p => Traversing (Coyoneda p) where
  traverse' = propure . traverse' . proextract
  wander f = propure . wander f . proextract

export
Mapping p => Mapping (Coyoneda p) where
  map' = propure . map' . proextract
  roam f = propure . roam f . proextract

export
Sieve p f => Sieve (Coyoneda p) f where
  sieve = sieve . proextract

export
Cosieve p f => Cosieve (Coyoneda p) f where
  cosieve = cosieve . proextract
