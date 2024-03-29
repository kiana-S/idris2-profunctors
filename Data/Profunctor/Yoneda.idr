module Data.Profunctor.Yoneda

import Data.Profunctor
import Data.Profunctor.Costrong
import Data.Profunctor.Traversing
import Data.Profunctor.Mapping
import Data.Profunctor.Sieve

%default total


------------------------------------------------------------------------------
-- Yoneda
------------------------------------------------------------------------------


||| The cofree profunctor given a data constructor with two type parameters.
public export
record Yoneda p a b where
  constructor MkYoneda
  runYoneda : forall x, y. (x -> a) -> (b -> y) -> p x y

public export
Profunctor (Yoneda p) where
  lmap f (MkYoneda p) = MkYoneda $ \l,r => p (f . l) r
  rmap f (MkYoneda p) = MkYoneda $ \l,r => p l (r . f)
  dimap f g (MkYoneda p) = MkYoneda $ \l,r => p (f . l) (r . g)

public export
ProfunctorFunctor Yoneda where
  promap f (MkYoneda p) = MkYoneda $ f .: p

public export
ProfunctorMonad Yoneda where
  propure p = MkYoneda $ \l,r => dimap l r p
  projoin (MkYoneda p) = p id id

public export
ProfunctorComonad Yoneda where
  proextract (MkYoneda p) = p id id
  produplicate p = MkYoneda $ \l,r => dimap l r p

||| A witness that `Yoneda p` and `p` are equivalent when `p` is a profunctor.
public export
yonedaEqv : Profunctor p => p a b <=> Yoneda p a b
yonedaEqv = MkEquivalence propure proextract

public export
yonedaIso : (Profunctor q, Profunctor r) => forall p. Profunctor p =>
              p (q a b) (r a' b') -> p (Yoneda q a b) (Yoneda r a' b')
yonedaIso = dimap proextract propure

public export
Functor (Yoneda p a) where
  map = rmap

public export
GenStrong ten p => GenStrong ten (Yoneda p) where
  strongl = propure . strongl {ten,p} . proextract
  strongr = propure . strongr {ten,p} . proextract

public export
GenCostrong ten p => GenCostrong ten (Yoneda p) where
  costrongl = propure . costrongl {ten,p} . proextract
  costrongr = propure . costrongr {ten,p} . proextract

public export
Closed p => Closed (Yoneda p) where
  closed = propure . closed . proextract

public export
Traversing p => Traversing (Yoneda p) where
  traverse' = propure . traverse' . proextract
  wander f = propure . wander f . proextract

public export
Mapping p => Mapping (Yoneda p) where
  map' = propure . map' . proextract
  roam f = propure . roam f . proextract

public export
Sieve p f => Sieve (Yoneda p) f where
  sieve = sieve . proextract

public export
Cosieve p f => Cosieve (Yoneda p) f where
  cosieve = cosieve . proextract


------------------------------------------------------------------------------
-- Coyoneda
------------------------------------------------------------------------------


||| The free profunctor given a data constructor with two type parameters.
public export
data Coyoneda : (p : Type -> Type -> Type) -> Type -> Type -> Type where
  MkCoyoneda : (a -> x) -> (y -> b) -> p x y -> Coyoneda p a b


public export
Profunctor (Coyoneda p) where
  lmap f (MkCoyoneda l r p) = MkCoyoneda (l . f) r p
  rmap f (MkCoyoneda l r p) = MkCoyoneda l (f . r) p
  dimap f g (MkCoyoneda l r p) = MkCoyoneda (l . f) (g . r) p

public export
ProfunctorFunctor Coyoneda where
  promap f (MkCoyoneda l r p) = MkCoyoneda l r (f p)

public export
ProfunctorMonad Coyoneda where
  propure = MkCoyoneda id id
  projoin (MkCoyoneda l r p) = dimap l r p

public export
ProfunctorComonad Coyoneda where
  proextract (MkCoyoneda l r p) = dimap l r p
  produplicate = MkCoyoneda id id

||| A witness that `Coyoneda p` and `p` are equivalent when `p` is a profunctor.
public export
coyonedaEqv : Profunctor p => p a b <=> Coyoneda p a b
coyonedaEqv = MkEquivalence propure proextract

public export
coyonedaIso : (Profunctor q, Profunctor r) => forall p. Profunctor p =>
              p (q a b) (r a' b') -> p (Coyoneda q a b) (Coyoneda r a' b')
coyonedaIso = dimap proextract propure

public export
Functor (Coyoneda p a) where
  map = rmap

public export
GenStrong ten p => GenStrong ten (Coyoneda p) where
  strongl = propure . strongl {ten,p} . proextract
  strongr = propure . strongr {ten,p} . proextract

public export
GenCostrong ten p => GenCostrong ten (Coyoneda p) where
  costrongl = propure . costrongl {ten,p} . proextract
  costrongr = propure . costrongr {ten,p} . proextract

public export
Closed p => Closed (Coyoneda p) where
  closed = propure . closed . proextract

public export
Traversing p => Traversing (Coyoneda p) where
  traverse' = propure . traverse' . proextract
  wander f = propure . wander f . proextract

public export
Mapping p => Mapping (Coyoneda p) where
  map' = propure . map' . proextract
  roam f = propure . roam f . proextract

public export
Sieve p f => Sieve (Coyoneda p) f where
  sieve = sieve . proextract

public export
Cosieve p f => Cosieve (Coyoneda p) f where
  cosieve = cosieve . proextract
