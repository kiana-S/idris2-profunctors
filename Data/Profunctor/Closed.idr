module Data.Profunctor.Closed

import Data.Profunctor.Types
import Data.Profunctor.Functor
import Data.Profunctor.Strong

%default total


public export
interface Profunctor p => Closed p where
  closed : p a b -> p (x -> a) (x -> b)


-- Closure

public export
record Closure p a b where
  constructor MkClosure
  getClosure : forall x. p (x -> a) (x -> b)


-- Environment

public export
data Environment : (p : Type -> Type -> Type) -> Type -> Type -> Type where
  MkEnv : ((z -> y) -> b) -> p x y -> (a -> z -> x) -> Environment p a b

