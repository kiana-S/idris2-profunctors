module Data.Profunctor.Functor

import Data.Profunctor.Types

%default total


public export
interface ProfunctorFunctor (0 t : (Type -> Type -> Type) -> k -> k' -> Type) where
  promap : Profunctor p => p :-> q -> t p :-> t q

public export
interface ProfunctorFunctor t =>
    ProfunctorMonad (0 t : (Type -> Type -> Type) -> Type -> Type -> Type) where
  propure : Profunctor p => p :-> t p
  projoin : Profunctor p => t (t p) :-> t p

public export
interface ProfunctorFunctor t =>
    ProfunctorComonad (0 t : (Type -> Type -> Type) -> Type -> Type -> Type) where
  proextract : Profunctor p => t p :-> p
  produplicate : Profunctor p => t p :-> t (t p)

public export
interface (ProfunctorFunctor f, ProfunctorFunctor u) =>
    ProfunctorAdjunction (0 f : (Type -> Type -> Type) -> Type -> Type -> Type)
                         (0 u : (Type -> Type -> Type) -> Type -> Type -> Type) | f, u where
  prounit   : Profunctor p => p :-> u (f p)
  procounit : Profunctor p => f (u p) :-> p
