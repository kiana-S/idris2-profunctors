module Data.Profunctor.Traversing

import Control.Monad.Identity
import Data.Morphisms
import Data.Profunctor.Types
import Data.Profunctor.Functor
import Data.Profunctor.Strong
import Data.Profunctor.Closed

%default total

record Bazaar a b t where
  constructor MkBazaar
  getBazaar : forall f. Applicative f => (a -> f b) -> f t

Functor (Bazaar a b) where
  map f (MkBazaar g) = MkBazaar (map f . g)

Applicative (Bazaar a b) where
  pure a = MkBazaar $ \_ => pure a
  mf <*> ma = MkBazaar $ \k => getBazaar mf k <*> getBazaar ma k

sell : a -> Bazaar a b b
sell a = MkBazaar ($ a)

record Baz t b a where
  constructor MkBaz
  getBaz : forall f. Applicative f => (a -> f b) -> f t

Functor (Baz t b) where
  map f (MkBaz g) = MkBaz (g . (. f))


sold : Baz t a a -> t
sold m = runIdentity (getBaz m Id)

Foldable (Baz t b) where
  foldr f i bz = getBaz bz @{appEndo} f i
    where
      -- Equivalent to `Const (Endomorphism acc)`
      appEndo : Applicative (\_ => acc -> acc)
      appEndo = MkApplicative @{MkFunctor (const id)} (const id) (.)

Traversable (Baz t b) where
  traverse f bz = map (\m => MkBaz (getBazaar m)) $ getBaz bz @{Compose} $ \x => sell <$> f x


public export
interface (Strong p, Choice p) => Traversing p where
  traverse' : Traversable f => p a b -> p (f a) (f b)
  traverse' = wander traverse

  wander : (forall f. Applicative f => (a -> f b) -> s -> f t) -> p a b -> p s t
  wander f = dimap (\s => MkBaz $ \afb => f afb s) sold . traverse'
