module Data.Profunctor.Types

import Data.Contravariant
import Data.Morphisms

%default total


public export
interface Profunctor p where

  dimap : (a -> b) -> (c -> d) -> p b c -> p a d
  dimap f g = lmap f . rmap g

  lmap : (a -> b) -> p b c -> p a c
  lmap f = dimap f id

  rmap : (b -> c) -> p a b -> p a c
  rmap = dimap id


infix 0 :->
public export
0 (:->) : (p, q : k -> k' -> Type) -> Type
p :-> q = {0 a, b : _} -> p a b -> q a b


-- Instances for existing types

export
Profunctor Morphism where
  dimap f g (Mor h) = Mor (g . h . f)
  lmap f (Mor g) = Mor (g . f)
  rmap = map

namespace Profunctor
  export
  [Function] Profunctor (\a,b => a -> b) where
    dimap f g h = g . h . f
    lmap = flip (.)
    rmap = (.)

export
Functor f => Profunctor (Kleislimorphism f) where
  dimap f g (Kleisli h) = Kleisli (map g . h . f)
  lmap f (Kleisli g) = Kleisli (g . f)
  rmap = map


-- Examples of profunctors

public export
record Star {0 k : Type} (f : k -> Type) a (b : k) where
  constructor MkStar
  applyStar : a -> f b

export
Functor f => Functor (Star f a) where
  map f (MkStar g) = MkStar (map f . g)

export
Applicative f => Applicative (Star f a) where
  pure = MkStar . const . pure
  MkStar f <*> MkStar g = MkStar (\x => f x <*> g x)

export
Monad f => Monad (Star f a) where
  MkStar f >>= g = MkStar $ \x => do
    a <- f x
    applyStar (g a) x

export
Contravariant f => Contravariant (Star f a) where
  contramap f (MkStar g) = MkStar (contramap f . g)


export
Functor f => Profunctor (Star f) where
  dimap f g (MkStar h) = MkStar (map g . h . f)
  lmap f (MkStar g) = MkStar (g . f)
  rmap f (MkStar g) = MkStar (map f . g)


public export
record Costar {0 k : Type} (f : k -> Type) (a : k) b where
  constructor MkCostar
  applyCostar : f a -> b

export
Functor (Costar f a) where
  map f (MkCostar g) = MkCostar (f . g)

export
Applicative (Costar f a) where
  pure = MkCostar . const
  MkCostar f <*> MkCostar g = MkCostar (\x => f x (g x))

export
Monad (Costar f a) where
  MkCostar f >>= g = MkCostar (\x => applyCostar (g (f x)) x)

export
Functor f => Profunctor (Costar f) where
  dimap f g (MkCostar h) = MkCostar (g . h . map f)
  lmap f (MkCostar g) = MkCostar (g . map f)
  rmap f (MkCostar g) = MkCostar (f . g)


public export
record Tagged {0 k : Type} (a : k) b where
  constructor Tag
  getTagged : b

public export
retag : Tagged a c -> Tagged b c
retag (Tag x) = Tag x

export
Functor (Tagged a) where
  map f (Tag x) = Tag (f x)

export
Applicative (Tagged a) where
  pure = Tag
  Tag f <*> Tag x = Tag (f x)

export
Monad (Tagged a) where
  join = getTagged
  Tag x >>= f = f x

export
Foldable (Tagged a) where
  foldr f x (Tag y) = f y x
  foldl f x (Tag y) = f x y
  null = const False
  foldlM f x (Tag y) = f x y
  toList (Tag x) = [x]
  foldMap f (Tag x) = f x

export
Traversable (Tagged a) where
  traverse f (Tag x) = map Tag (f x)

export
Profunctor Tagged where
  dimap _ f (Tag x) = Tag (f x)
  lmap = const retag
  rmap f (Tag x) = Tag (f x)
