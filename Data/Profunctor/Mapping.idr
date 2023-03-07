module Data.Profunctor.Mapping

import Control.Monad.Identity
import Data.Morphisms
import Data.Tensor
import Data.Profunctor
import Data.Profunctor.Traversing

%default total


public export
interface (Traversing p, Closed p) => Mapping p where
  map' : Functor f => p a b -> p (f a) (f b)
  map' = roam map

  roam : ((a -> b) -> s -> t) -> p a b -> p s t
  roam f = dimap (flip f) ($ id) . map' @{%search} @{functor}
    where
      functor : Functor (\a => (a -> b) -> t)
      functor = MkFunctor (\f => (. (. f)))


export
Mapping Morphism where
  map' (Mor f) = Mor (map f)
  roam f (Mor x) = Mor (f x)

export
[Function] Mapping (\a,b => a -> b)
    using Traversing.Function Closed.Function where
  map' = map
  roam = id


public export
record CofreeMapping p a b where
  constructor MkCFM
  runCFM : forall f. Functor f => p (f a) (f b)

export
Profunctor p => Profunctor (CofreeMapping p) where
  lmap f (MkCFM p) = MkCFM (lmap (map f) p)
  rmap f (MkCFM p) = MkCFM (rmap (map f) p)
  dimap f g (MkCFM p) = MkCFM (dimap (map f) (map g) p)

export
Profunctor p => Functor (CofreeMapping p a) where
  map = rmap

export
ProfunctorFunctor CofreeMapping where
  promap f (MkCFM p) = MkCFM (f p)

export
ProfunctorComonad CofreeMapping where
  proextract (MkCFM p) = dimap Id runIdentity p
  produplicate (MkCFM p) = MkCFM $ MkCFM $ p @{Compose}

export
Symmetric ten => Profunctor p => GenStrong ten (CofreeMapping p) where
  strongr (MkCFM p) = MkCFM (p @{Compose {g=ten c} @{%search} @{MkFunctor mapSnd}})
  strongl (MkCFM p) = MkCFM (p @{Compose {g=(`ten` c)} @{%search} @{MkFunctor mapFst}})

export
Profunctor p => Closed (CofreeMapping p) where
  closed (MkCFM p) = MkCFM (p @{Compose {g = \b => x -> b} @{%search} @{MkFunctor (.)}})

roamCofree : Profunctor p => ((a -> b) -> s -> t) -> CofreeMapping p a b -> CofreeMapping p s t
roamCofree f (MkCFM p) = MkCFM $ dimap (map (flip f)) (map ($ id)) $
      p @{Compose @{%search} @{functor}}
  where
    functor : Functor (\a => (a -> b) -> t)
    functor = MkFunctor (\f => (. (. f)))

export
Profunctor p => Traversing (CofreeMapping p) where
  traverse' (MkCFM p) = MkCFM (p @{Compose})
  wander f = roamCofree $ (runIdentity .) . f . (Id .)

export
Profunctor p => Mapping (CofreeMapping p) where
  map' (MkCFM p) = MkCFM (p @{Compose})
  roam = roamCofree



public export
data FreeMapping : (p : Type -> Type -> Type) -> Type -> Type -> Type where
  MkFM : Functor f => (f y -> b) -> p x y -> (a -> f x) -> FreeMapping p a b

export
Profunctor (FreeMapping p) where
  lmap f (MkFM l m r) = MkFM l m (r . f)
  rmap f (MkFM l m r) = MkFM (f . l) m r
  dimap f g (MkFM l m r) = MkFM (g . l) m (r . f)

export
ProfunctorFunctor FreeMapping where
  promap f (MkFM l m r) = MkFM l (f m) r

export
ProfunctorMonad FreeMapping where
  propure p = MkFM runIdentity p Id
  projoin (MkFM l' (MkFM l m r) r') = MkFM @{Compose} (l' . map l) m (map r . r')

export
Functor (FreeMapping p a) where
  map = rmap

export
GenStrong Pair (FreeMapping p) where
  strongr (MkFM l m r) = MkFM @{Compose} (map l) m (map r)
  strongl = dimap Builtin.swap Builtin.swap . strongr {p=FreeMapping p}

export
GenStrong Either (FreeMapping p) where
  strongr (MkFM l m r) = MkFM @{Compose} (map l) m (map r)
  strongl = dimap Tensor.swap Tensor.swap . strongr {p=FreeMapping p}

export
Closed (FreeMapping p) where
  closed (MkFM l m r) = dimap Mor applyMor $ MkFM @{Compose} (map l) m (map r)

roamFree : ((a -> b) -> s -> t) -> FreeMapping p a b -> FreeMapping p s t
roamFree f (MkFM l m r) = MkFM @{Compose @{functor}} (($ id) . map @{functor} l) m (map @{functor} r . flip f)
  where
    functor : Functor (\a => (a -> b) -> t)
    functor = MkFunctor (\f => (. (. f)))

export
Traversing (FreeMapping p) where
  traverse' (MkFM l m r) = MkFM @{Compose} (map l) m (map r)
  wander f = roamFree $ (runIdentity .) . f . (Id .)

export
Mapping (FreeMapping p) where
  map' (MkFM l m r) = MkFM @{Compose} (map l) m (map r)
  roam = roamFree