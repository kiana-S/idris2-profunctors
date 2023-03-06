module Data.Profunctor.Closed

import Data.Profunctor.Types
import Data.Profunctor.Functor
import Data.Profunctor.Strong

%default total


public export
interface Profunctor p => Closed p where
  closed : p a b -> p (x -> a) (x -> b)


export
curry' : Closed p => p (a, b) c -> p a (b -> c)
curry' = lmap (,) . closed

-- Helper functions for working with function types
hither : (s -> (a, b)) -> (s -> a, s -> b)
hither h = (fst . h, snd . h)

yon : (s -> a, s -> b) -> s -> (a,b)
yon h s = (fst h s, snd h s)



-- Closure

public export
record Closure p a b where
  constructor MkClosure
  getClosure : forall x. p (x -> a) (x -> b)


export
Profunctor p => Profunctor (Closure p) where
  dimap f g (MkClosure p) = MkClosure $ dimap (f .) (g .) p
  lmap f (MkClosure p) = MkClosure $ lmap (f .) p
  rmap f (MkClosure p) = MkClosure $ rmap (f .) p

export
ProfunctorFunctor Closure where
  promap f (MkClosure p) = MkClosure (f p)

export
ProfunctorComonad Closure where
  proextract (MkClosure p) = dimap const ($ ()) p
  produplicate (MkClosure p) = MkClosure $ MkClosure $ dimap uncurry curry p

export
Strong p => GenStrong Pair (Closure p) where
  strongl (MkClosure p) = MkClosure $ dimap hither yon $ first p
  strongr (MkClosure p) = MkClosure $ dimap hither yon $ second p

export
Profunctor p => Closed (Closure p) where
  closed p = getClosure $ produplicate p

export
Profunctor p => Functor (Closure p a) where
  map = rmap


export
close : Closed p => p :-> q -> p :-> Closure q
close f p = MkClosure $ f $ closed p

export
unclose : Profunctor q => p :-> Closure q -> p :-> q
unclose f p = dimap const ($ ()) $ getClosure $ f p


-- Environment

public export
data Environment : (p : Type -> Type -> Type) -> Type -> Type -> Type where
  MkEnv : ((z -> y) -> b) -> p x y -> (a -> z -> x) -> Environment p a b


Profunctor (Environment p) where
  dimap f g (MkEnv l m r) = MkEnv (g . l) m (r . f)
  lmap f (MkEnv l m r) = MkEnv l m (r . f)
  rmap g (MkEnv l m r) = MkEnv (g . l) m r

ProfunctorFunctor Environment where
  promap f (MkEnv l m r) = MkEnv l (f m) r

ProfunctorMonad Environment where
  propure p = MkEnv ($ ()) p const
  projoin (MkEnv {x=x',y=y',z=z'} l' (MkEnv {x,y,z} l m r) r') = MkEnv (ll . curry) m rr
    where
      ll : (z' -> z -> y) -> b
      ll zr = l' (l . zr)
      rr : a -> (z', z) -> x
      rr a (b, c) = r (r' a b) c

ProfunctorAdjunction Environment Closure where
  prounit p = MkClosure (MkEnv id p id)
  procounit (MkEnv l (MkClosure x) r) = dimap r l x

Closed (Environment p) where
  closed {x=x'} (MkEnv {x,y,z} l m r) = MkEnv l' m r'
    where
      l' : ((z, x') -> y) -> x' -> b
      l' f x = l (\z => f (z,x))
      r' : (x' -> a) -> (z, x') -> x
      r' f (z,x) = r (f x) z

Profunctor p => Functor (Environment p a) where
  map = rmap


environment : Closed q => p :-> q -> Environment p :-> q
environment f (MkEnv l m r) = dimap r l $ closed (f m)

unenvironment : Environment p :-> q -> p :-> q
unenvironment f p = f (MkEnv ($ ()) p const)
