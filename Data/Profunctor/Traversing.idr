module Data.Profunctor.Traversing

import Control.Applicative.Const
import Control.Monad.Identity
import Data.Morphisms
import Data.Tensor
import Data.Profunctor

%default total


------------------------------------------------------------------------------
-- Default implementation machinery
------------------------------------------------------------------------------


[FoldablePair] Foldable (Pair c) where
  foldr op init (_, x) = x `op` init
  foldl op init (_, x) = init `op` x
  null _ = False

[TraversablePair] Traversable (Pair c) using FoldablePair where
  traverse f (l, r) = (l,) <$> f r

[FoldableIdentity] Foldable Identity where
  foldr f i (Id x) = f x i
  foldl f i (Id x) = f i x
  null _ = False

[TraversableIdentity] Traversable Identity using FoldableIdentity where
  traverse f (Id x) = map Id (f x)


record Bazaar a b t where
  constructor MkBazaar
  runBazaar : forall f. Applicative f => (a -> f b) -> f t

Functor (Bazaar a b) where
  map f (MkBazaar g) = MkBazaar (map f . g)

Applicative (Bazaar a b) where
  pure a = MkBazaar $ \_ => pure a
  mf <*> ma = MkBazaar $ \k => runBazaar mf k <*> runBazaar ma k

sell : a -> Bazaar a b b
sell a = MkBazaar ($ a)

record Baz t b a where
  constructor MkBaz
  runBaz : forall f. Applicative f => (a -> f b) -> f t

Functor (Baz t b) where
  map f (MkBaz g) = MkBaz (g . (. f))


sold : Baz t a a -> t
sold m = runIdentity (runBaz m Id)

Foldable (Baz t b) where
  foldr f i bz = runBaz bz @{appEndo} f i
    where
      -- Equivalent to `Const (Endomorphism acc)`
      appEndo : Applicative (\_ => acc -> acc)
      appEndo = MkApplicative @{MkFunctor (const id)} (const id) (.)

Traversable (Baz t b) where
  traverse f bz = map (\m => MkBaz (runBazaar m)) $ runBaz bz @{Compose} $ \x => sell <$> f x

export
wanderDef : Profunctor p => (forall f. Traversable f => p a b -> p (f a) (f b))
                         -> (forall f. Applicative f => (a -> f b) -> s -> f t) -> p a b -> p s t
wanderDef tr f = dimap (\s => MkBaz $ \afb => f afb s) sold . tr


------------------------------------------------------------------------------
-- Traversing interface
------------------------------------------------------------------------------


||| The interface of profunctors that implement `wander`.
||| NOTE: Definitions in terms of `wander` are much more efficient!
|||
||| Laws:
||| * `traverse' = wander traverse`
||| * `traverse' . lmap f = lmap (map f) . traverse'`
||| * `traverse' . rmap f = rmap (map f) . traverse'`
||| * `traverse' . traverse' = traverse' @{Compose}`
||| * `dimap Id runIdentity . traverse' = id`
public export
interface (Strong p, Choice p) => Traversing p where
  traverse' : Traversable f => p a b -> p (f a) (f b)
  traverse' = wander traverse

  wander : (forall f. Applicative f => (a -> f b) -> s -> f t) -> p a b -> p s t
  wander = wanderDef traverse'


------------------------------------------------------------------------------
-- Implementations
------------------------------------------------------------------------------


export
Traversing Morphism where
  traverse' (Mor f) = Mor (map f)
  wander f (Mor p) = Mor (runIdentity . (f $ Id . p))

||| A named implementation of `Traversing` for function types.
||| Use this to avoid having to use a type wrapper like `Morphism`.
export
[Function] Traversing (\a,b => a -> b) using Strong.Function where
  traverse' = map
  wander f g = runIdentity . (f $ Id . g)

export
Applicative f => Traversing (Kleislimorphism f) where
  traverse' (Kleisli p) = Kleisli (traverse p)
  wander f (Kleisli p) = Kleisli (f p)

export
Applicative f => Traversing (Star f) where
  traverse' (MkStar p) = MkStar (traverse p)
  wander f (MkStar p) = MkStar (f p)

export
Monoid r => Traversing (Forget r) where
  traverse' (MkForget k) = MkForget (foldMap k)
  wander f (MkForget k) = MkForget (runConst . f (MkConst . k))


------------------------------------------------------------------------------
-- CofreeTraversing
------------------------------------------------------------------------------


||| The comonad generated by the reflective subcategory of profunctors that
||| implement `Traversing`.
public export
record CofreeTraversing p a b where
  constructor MkCFT
  runCFT : forall f. Traversable f => p (f a) (f b)

export
Profunctor p => Profunctor (CofreeTraversing p) where
  lmap f (MkCFT p) = MkCFT (lmap (map f) p)
  rmap g (MkCFT p) = MkCFT (rmap (map g) p)
  dimap f g (MkCFT p) = MkCFT (dimap (map f) (map g) p)

export
Profunctor p => GenStrong Pair (CofreeTraversing p) where
  strongr (MkCFT p) = MkCFT (p @{Compose @{%search} @{TraversablePair}})
  strongl = dimap swap' swap' . strongr {p=CofreeTraversing p}

export
Profunctor p => GenStrong Either (CofreeTraversing p) where
  strongr (MkCFT p) = MkCFT (p @{Compose {f=Either c}})
  strongl = dimap swap' swap' . strongr {p=CofreeTraversing p}

export
Profunctor p => Traversing (CofreeTraversing p) where
  traverse' (MkCFT p) = MkCFT (p @{Compose})

export
ProfunctorFunctor CofreeTraversing where
  promap f (MkCFT p) = MkCFT (f p)

export
ProfunctorComonad CofreeTraversing where
  proextract (MkCFT p) = dimap Id runIdentity $ p @{TraversableIdentity}
  produplicate (MkCFT p) = MkCFT $ MkCFT $ p @{Compose}

export
Profunctor p => Functor (CofreeTraversing p a) where
  map = rmap


export
cofreeTraversing : Traversing p => p :-> q -> p :-> CofreeTraversing q
cofreeTraversing f p = MkCFT $ f $ traverse' p

export
uncofreeTraversing : Profunctor q => p :-> CofreeTraversing q -> p :-> q
uncofreeTraversing f p = proextract $ f p


------------------------------------------------------------------------------
-- FreeTraversing
------------------------------------------------------------------------------


||| The monad generated by the reflective subcategory of profunctors that
||| implement `Traversing`.
public export
data FreeTraversing : (p : Type -> Type -> Type) -> Type -> Type -> Type where
  MkFT : Traversable f => (f y -> b) -> p x y -> (a -> f x) -> FreeTraversing p a b

export
Profunctor (FreeTraversing p) where
  lmap f (MkFT l m r) = MkFT l m (r . f)
  rmap f (MkFT l m r) = MkFT (f . l) m r
  dimap f g (MkFT l m r) = MkFT (g . l) m (r . f)

export
GenStrong Pair (FreeTraversing p) where
  strongr (MkFT l m r) = MkFT @{Compose @{TraversablePair}} (map l) m (map r)
  strongl = dimap swap' swap' . strongr {p=FreeTraversing p}

export
GenStrong Either (FreeTraversing p) where
  strongr (MkFT l m r) = MkFT @{Compose {t=Either c}} (map l) m (map r)
  strongl = dimap swap' swap' . strongr {p=FreeTraversing p}

export
Traversing (FreeTraversing p) where
  traverse' (MkFT l m r) = MkFT @{Compose} (map l) m (map r)

export
ProfunctorFunctor FreeTraversing where
  promap f (MkFT l m r) = MkFT l (f m) r

export
ProfunctorMonad FreeTraversing where
  propure p = MkFT @{TraversableIdentity} runIdentity p Id
  projoin (MkFT l' (MkFT l m r) r') = MkFT @{Compose} (l' . map l) m (map r . r')


export
freeTraversing : Traversing q => p :-> q -> FreeTraversing p :-> q
freeTraversing fn (MkFT {f} l m r) = dimap r l (traverse' {f} (fn m))

export
unfreeTraversing : FreeTraversing p :-> q -> p :-> q
unfreeTraversing f p = f (MkFT @{TraversableIdentity} runIdentity p Id)
