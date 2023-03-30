module Data.Profunctor.Closed

import Data.Morphisms
import Data.Profunctor.Types
import Data.Profunctor.Functor
import Data.Profunctor.Strong

%default total


------------------------------------------------------------------------------
-- Closed interface
------------------------------------------------------------------------------


||| Closed profunctors preserve the closed structure of a category.
|||
||| Laws:
||| * `lmap (. f) . closed = rmap (. f) . closed`
||| * `closed . closed = dimap uncurry curry . closed`
||| * `dimap const ($ ()) . closed = id`
public export
interface Profunctor p => Closed p where
  ||| The action of a closed profunctor.
  closed : p a b -> p (x -> a) (x -> b)


------------------------------------------------------------------------------
-- Implementations
------------------------------------------------------------------------------


public export
Closed Morphism where
  closed (Mor f) = Mor (f .)

||| A named implementation of `Closed` for function types.
||| Use this to avoid having to use a type wrapper like `Morphism`.
public export
[Function] Closed (\a,b => a -> b) using Profunctor.Function where
  closed = (.)

public export
Functor f => Closed (Costar f) where
  closed (MkCostar p) = MkCostar $ \f,x => p (map ($ x) f)


public export
curry' : Closed p => p (a, b) c -> p a (b -> c)
curry' = lmap (,) . closed


------------------------------------------------------------------------------
-- Closure
------------------------------------------------------------------------------


-- Helper functions for working with function types
hither : (s -> (a, b)) -> (s -> a, s -> b)
hither h = (fst . h, snd . h)

yon : (s -> a, s -> b) -> s -> (a,b)
yon h s = (fst h s, snd h s)


||| The comonad generated by the reflective subcategory of profunctors that
||| implement `Closed`.
public export
record Closure p a b where
  constructor MkClosure
  runClosure : forall x. p (x -> a) (x -> b)


public export
Profunctor p => Profunctor (Closure p) where
  dimap f g (MkClosure p) = MkClosure $ dimap (f .) (g .) p
  lmap f (MkClosure p) = MkClosure $ lmap (f .) p
  rmap f (MkClosure p) = MkClosure $ rmap (f .) p

public export
ProfunctorFunctor Closure where
  promap f (MkClosure p) = MkClosure (f p)

public export
ProfunctorComonad Closure where
  proextract (MkClosure p) = dimap const ($ ()) p
  produplicate (MkClosure p) = MkClosure $ MkClosure $ dimap uncurry curry p

public export
Strong p => GenStrong Pair (Closure p) where
  strongl (MkClosure p) = MkClosure $ dimap hither yon $ first p
  strongr (MkClosure p) = MkClosure $ dimap hither yon $ second p

public export
Profunctor p => Closed (Closure p) where
  closed p = runClosure $ produplicate p

public export
Profunctor p => Functor (Closure p a) where
  map = rmap


public export
close : Closed p => p :-> q -> p :-> Closure q
close f p = MkClosure $ f $ closed p

public export
unclose : Profunctor q => p :-> Closure q -> p :-> q
unclose f p = dimap const ($ ()) $ runClosure $ f p


------------------------------------------------------------------------------
-- Environment
------------------------------------------------------------------------------


||| The monad generated by the reflective subcategory of profunctors that
||| implement `Closed`.
public export
data Environment : (p : Type -> Type -> Type) -> Type -> Type -> Type where
  MkEnv : ((z -> y) -> b) -> p x y -> (a -> z -> x) -> Environment p a b


public export
Profunctor (Environment p) where
  dimap f g (MkEnv l m r) = MkEnv (g . l) m (r . f)
  lmap f (MkEnv l m r) = MkEnv l m (r . f)
  rmap g (MkEnv l m r) = MkEnv (g . l) m r

public export
ProfunctorFunctor Environment where
  promap f (MkEnv l m r) = MkEnv l (f m) r

public export
ProfunctorMonad Environment where
  propure p = MkEnv ($ ()) p const
  projoin (MkEnv {x=x',y=y',z=z'} l' (MkEnv {x,y,z} l m r) r') = MkEnv (ll . curry) m rr
    where
      ll : (z' -> z -> y) -> b
      ll zr = l' (l . zr)
      rr : a -> (z', z) -> x
      rr a (b, c) = r (r' a b) c

public export
ProfunctorAdjunction Environment Closure where
  prounit p = MkClosure (MkEnv id p id)
  procounit (MkEnv l (MkClosure x) r) = dimap r l x

public export
Closed (Environment p) where
  closed {x=x'} (MkEnv {x,y,z} l m r) = MkEnv l' m r'
    where
      l' : ((z, x') -> y) -> x' -> b
      l' f x = l (\z => f (z,x))
      r' : (x' -> a) -> (z, x') -> x
      r' f (z,x) = r (f x) z

public export
Profunctor p => Functor (Environment p a) where
  map = rmap


public export
environment : Closed q => p :-> q -> Environment p :-> q
environment f (MkEnv l m r) = dimap r l $ closed (f m)

public export
unenvironment : Environment p :-> q -> p :-> q
unenvironment f p = f (MkEnv ($ ()) p const)
