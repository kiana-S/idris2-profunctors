||| This module defines profunctor costrength with respect to a particular
||| monoidal structure.
|||
||| Since the homset profunctor (`Morphism`) is not costrong, very few
||| profunctors implement this interface.
|||
||| Unlike Haskell's profunctors library, `Costrong` and `Cochoice` are here
||| special cases of the interface `GenCostrong`, which defines costrength with
||| respect to an arbitrary tensor product. When writing implementations for
||| a profunctor, `GenCostrong Pair` and `GenCostrong Either` should be used instead
||| of `Costrong` and `Cochoice` respectively.
module Data.Profunctor.Costrong

import Data.Morphisms
import Data.Tensor
import Data.Profunctor.Functor
import Data.Profunctor.Types

%default total


------------------------------------------------------------------------------
-- Costrength interface
------------------------------------------------------------------------------


||| Profunctor costrength with respect to a tensor product.
|||
||| These constraints are not required by the interface, but the tensor product
||| `ten` is generally expected to implement `(Tensor ten i, Symmetric ten)`.
|||
||| Laws:
||| * `costrongl = costrongr . dimap swap' swap'`
||| * `costrongl . dimap unitr.rightToLeft unitr.leftToRight = id`
||| * `costrongl . lmap (mapSnd f) = costrongl . rmap (mapSnd f)`
||| * `costrongr . costrongr = costrongr . dimap assocl assocr`
|||
||| @ ten The tensor product of the monoidal structure
public export
interface Profunctor p => GenCostrong (0 ten : Type -> Type -> Type) p where
  ||| The left action of a costrong profunctor.
  costrongl : p (a `ten` c) (b `ten` c) -> p a b
  ||| The right action of a costrong profunctor.
  costrongr : p (c `ten` a) (c `ten` b) -> p a b


||| Profunctor costrength with respect to the product (`Pair`).
public export
Costrong : (p : Type -> Type -> Type) -> Type
Costrong = GenCostrong Pair

||| A special case of `costrongl` with constraint `Costrong`.
||| This is useful if the typechecker has trouble inferring the tensor product.
public export
unfirst : Costrong p => p (a, c) (b, c) -> p a b
unfirst = costrongl {ten=Pair}

||| A special case of `costrongr` with constraint `Costrong`.
||| This is useful if the typechecker has trouble inferring the tensor product.
public export
unsecond : Costrong p => p (c, a) (c, b) -> p a b
unsecond = costrongr {ten=Pair}

||| Profunctor costrength with respect to the coproduct (`Either`).
public export
Cochoice : (p : Type -> Type -> Type) -> Type
Cochoice = GenCostrong Either

||| A special case of `costrongl` with constraint `Cochoice`.
||| This is useful if the typechecker has trouble inferring the tensor product.
public export
unleft : Cochoice p => p (Either a c) (Either b c) -> p a b
unleft = costrongl {ten=Either}

||| A special case of `costrongr` with constraint `Cochoice`.
||| This is useful if the typechecker has trouble inferring the tensor product.
public export
unright : Cochoice p => p (Either c a) (Either c b) -> p a b
unright = costrongr {ten=Either}


------------------------------------------------------------------------------
-- Implementations for existing types
------------------------------------------------------------------------------


export
GenCostrong Pair Tagged where
  costrongl (Tag (x,_)) = Tag x
  costrongr (Tag (_,x)) = Tag x

export
GenCostrong Either (Forget r) where
  costrongl (MkForget k) = MkForget (k . Left)
  costrongr (MkForget k) = MkForget (k . Right)

export
GenCostrong Pair (Coforget r) where
  costrongl (MkCoforget k) = MkCoforget (fst . k)
  costrongr (MkCoforget k) = MkCoforget (snd . k)


------------------------------------------------------------------------------
-- Cotambara
------------------------------------------------------------------------------


||| The comonad generated by the reflective subcategory of profunctors that
||| implement `GenCostrong ten`.
public export
data GenCotambara : (ten, p : Type -> Type -> Type) -> Type -> Type -> Type where
  MkCotambara : GenCostrong ten q => q :-> p -> q a b -> GenCotambara ten p a b

export
Profunctor (GenCotambara ten p) where
  lmap f (MkCotambara n p) = MkCotambara n (lmap f p)
  rmap f (MkCotambara n p) = MkCotambara n (rmap f p)
  dimap f g (MkCotambara n p) = MkCotambara n (dimap f g p)

export
ProfunctorFunctor (GenCotambara ten) where
  promap f (MkCotambara n p) = MkCotambara (f . n) p

export
GenCostrong ten (GenCotambara ten p) where
  costrongl (MkCotambara @{costr} n p) = MkCotambara n (costrongl @{costr} p)
  costrongr (MkCotambara @{costr} n p) = MkCotambara n (costrongr @{costr} p)

export
ProfunctorComonad (GenCotambara ten) where
  proextract (MkCotambara n p) = n p
  produplicate (MkCotambara n p) = MkCotambara id (MkCotambara n p)

export
Functor (GenCotambara ten p a) where
  map = rmap


||| The comonad generated by the reflective subcategory of profunctors that
||| implement `Costrong`.
|||
||| This is a special case of `GenCotambara`.
public export
Cotambara : (p : Type -> Type -> Type) -> Type -> Type -> Type
Cotambara = GenCotambara Pair

||| The comonad generated by the reflective subcategory of profunctors that
||| implement `Cochoice`.
|||
||| This is a special case of `GenCotambara`.
public export
CotambaraSum : (p : Type -> Type -> Type) -> Type -> Type -> Type
CotambaraSum = GenCotambara Either


export
cotambara : GenCostrong ten p => p :-> q -> p :-> GenCotambara ten q
cotambara f = MkCotambara f

export
uncotambara : Tensor ten i => Profunctor q => p :-> GenCotambara ten q -> p :-> q
uncotambara f p = proextract (f p)


------------------------------------------------------------------------------
-- Copastro
------------------------------------------------------------------------------


||| The monad generated by the reflective subcategory of profunctors that
||| implement `GenCostrong ten`.
public export
record GenCopastro (ten, p : Type -> Type -> Type) a b where
  constructor MkCopastro
  runCopastro : forall q. GenCostrong ten q => p :-> q -> q a b

export
Profunctor (GenCopastro ten p) where
  dimap f g (MkCopastro h) = MkCopastro $ \n => dimap f g (h n)
  lmap f (MkCopastro h) = MkCopastro $ \n => lmap f (h n)
  rmap f (MkCopastro h) = MkCopastro $ \n => rmap f (h n)

export
ProfunctorFunctor (GenCopastro ten) where
  promap f (MkCopastro h) = MkCopastro $ \n => h (n . f)

export
ProfunctorMonad (GenCopastro ten) where
  propure p = MkCopastro ($ p)
  projoin p = MkCopastro $ \x => runCopastro p (\y => runCopastro y x)

export
GenCostrong ten (GenCopastro ten p) where
  costrongl (MkCopastro h) = MkCopastro $ \n => costrongl {ten} (h n)
  costrongr (MkCopastro h) = MkCopastro $ \n => costrongr {ten} (h n)

export
ProfunctorAdjunction (GenCopastro ten) (GenCotambara ten) where
  prounit p = MkCotambara id (propure {t=GenCopastro ten} p)
  procounit (MkCopastro h) = proextract (h id)


||| The monad generated by the reflective subcategory of profunctors that
||| implement `Costrong`.
|||
||| This is a special case of `GenCopastro`.
public export
Copastro : (p : Type -> Type -> Type) -> Type -> Type -> Type
Copastro = GenCopastro Pair

||| The monad generated by the reflective subcategory of profunctors that
||| implement `Cochoice`.
|||
||| This is a special case of `GenCopastro`.
public export
CopastroSum : (p : Type -> Type -> Type) -> Type -> Type -> Type
CopastroSum = GenCopastro Either


export
copastro : GenCostrong ten q => p :-> q -> GenCopastro ten p :-> q
copastro f (MkCopastro h) = h f

export
uncopastro : Tensor ten i => GenCopastro ten p :-> q -> p :-> q
uncopastro f x = f (MkCopastro ($ x))
