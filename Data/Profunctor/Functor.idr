||| This module defines endofunctors in the category of profunctors `[Idrᵒᵖ * Idr, Idr]`,
||| along with adjunctions of those functors.
||| Examples of these functors include `Yoneda`, `Pastro`, `Closure`, etc.
module Data.Profunctor.Functor

import Data.Profunctor.Types

%default total


||| An endofunctor in the category of profunctors.
|||
||| Laws:
||| * `promap id = id`
||| * `promap g . promap f = promap (g . f)`
public export
interface ProfunctorFunctor (0 t : (Type -> Type -> Type) -> k -> k' -> Type) where
  ||| Lift a transformation between profunctors into the functor `t`.
  promap : Profunctor p => p :-> q -> t p :-> t q


||| A monad in the category of profunctors.
||| 
||| Laws:
||| * `projoin . proreturn ≡ id`
||| * `projoin . promap proreturn ≡ id`
||| * `projoin . projoin ≡ projoin . promap projoin`
public export
interface ProfunctorFunctor t =>
    ProfunctorMonad (0 t : (Type -> Type -> Type) -> Type -> Type -> Type) where
  propure : Profunctor p => p :-> t p
  projoin : Profunctor p => t (t p) :-> t p

||| A comonad in the category of profunctors.
|||
||| Laws:
||| * `proextract . produplicate ≡ id`
||| * `promap proextract . produplicate ≡ id`
||| * `produplicate . produplicate ≡ promap produplicate . produplicate`
public export
interface ProfunctorFunctor t =>
    ProfunctorComonad (0 t : (Type -> Type -> Type) -> Type -> Type -> Type) where
  proextract : Profunctor p => t p :-> p
  produplicate : Profunctor p => t p :-> t (t p)

||| An adjunction between endofunctors in the category of profunctors.
|||
||| Laws:
||| * `counit . promap unit ≡ id`
||| * `promap counit . unit ≡ id`
public export
interface (ProfunctorFunctor l, ProfunctorFunctor r) =>
    ProfunctorAdjunction (0 l, r : (Type -> Type -> Type) -> Type -> Type -> Type) | l, r where
  prounit   : Profunctor p => p :-> r (l p)
  procounit : Profunctor p => l (r p) :-> p
