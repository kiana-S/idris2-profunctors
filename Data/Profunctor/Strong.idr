||| This module defines profunctor strength with respect to a particular
||| monoidal structure.
|||
||| Unlike Haskell's profunctors library, `Strong` and `Choice` are here
||| special cases of the interface `GenStrong`, which defines strength with
||| respect to an arbitrary tensor product. When writing implementations for
||| a profunctor, `GenStrong Pair` and `GenStrong Either` should be used instead
||| of `Strong` and `Choice` respectively.
module Data.Profunctor.Strong

import Data.Morphisms
import Data.Tensor
import Data.Profunctor.Functor
import Data.Profunctor.Types

%default total


------------------------------------------------------------------------------
-- Strength interface
------------------------------------------------------------------------------

||| Profunctor strength with respect to a tensor product.
||| A strong profunctor preserves the monoidal structure of a category.
|||
||| These constraints are not required by the interface, but the tensor product
||| `ten` is generally expected to implement `(Tensor ten i, Symmetric ten)`.
|||
||| Laws:
||| * `strongl = dimap swap' swap' . strongr`
||| * `dimap unitr.rightToLeft unitr.leftToRight . strongl = id`
||| * `lmap (mapSnd f) . strongl = rmap (mapSnd f) . strongl`
||| * `strongr . strongr = dimap assocr assocl . strongr`
|||
||| @ ten The tensor product of the monoidal structure
public export
interface Profunctor p => GenStrong (0 ten : Type -> Type -> Type) p where
  ||| The left action of a strong profunctor.
  strongl : p a b -> p (a `ten` c) (b `ten` c)
  ||| The right action of a strong profunctor.
  strongr : p a b -> p (c `ten` a) (c `ten` b)


||| Profunctor strength with respect to the product (`Pair`).
public export
Strong : (p : Type -> Type -> Type) -> Type
Strong = GenStrong Pair

||| A special case of `strongl` with constraint `Strong`.
||| This is useful if the typechecker has trouble inferring the tensor product.
%inline
public export
first : Strong p => p a b -> p (a, c) (b, c)
first = strongl {ten=Pair}

||| A special case of `strongr` with constraint `Strong`.
||| This is useful if the typechecker has trouble inferring the tensor product.
%inline
public export
second : Strong p => p a b -> p (c, a) (c, b)
second = strongr {ten=Pair}

||| Profunctor strength with respect to the coproduct (`Either`).
public export
Choice : (p : Type -> Type -> Type) -> Type
Choice = GenStrong Either

||| A special case of `strongl` with constraint `Choice`.
||| This is useful if the typechecker has trouble inferring the tensor product to use.
%inline
public export
left : Choice p => p a b -> p (Either a c) (Either b c)
left = strongl {ten=Either}

||| A special case of `strongr` with constraint `Choice`.
||| This is useful if the typechecker has trouble inferring the tensor product to use.
%inline
public export
right : Choice p => p a b -> p (Either c a) (Either c b)
right = strongr {ten=Either}


public export
uncurry' : Strong p => p a (b -> c) -> p (a, b) c
uncurry' = rmap (uncurry id) . first

public export
strong : Strong p => (a -> b -> c) -> p a b -> p a c
strong f = dimap dup (uncurry $ flip f) . first


------------------------------------------------------------------------------
-- Implementations
------------------------------------------------------------------------------


public export
Bifunctor ten => GenStrong ten Morphism where
  strongl (Mor f) = Mor (mapFst f)
  strongr (Mor f) = Mor (mapSnd f)

||| A named implementation of `GenStrong` for function types.
||| Use this to avoid having to use a type wrapper like `Morphism`.
public export
[Function] Bifunctor ten => GenStrong ten (\a,b => a -> b)
    using Profunctor.Function where
  strongl = mapFst
  strongr = mapSnd

public export
Functor f => GenStrong Pair (Kleislimorphism f) where
  strongl (Kleisli f) = Kleisli $ \(a,c) => (,c) <$> f a
  strongr (Kleisli f) = Kleisli $ \(c,a) => (c,) <$> f a

public export
Applicative f => GenStrong Either (Kleislimorphism f) where
  strongl (Kleisli f) = Kleisli $ either (map Left . f) (pure . Right)
  strongr (Kleisli f) = Kleisli $ either (pure . Left) (map Right . f)

public export
Functor f => GenStrong Pair (Star f) where
  strongl (MkStar f) = MkStar $ \(a,c) => (,c) <$> f a
  strongr (MkStar f) = MkStar $ \(c,a) => (c,) <$> f a

public export
Applicative f => GenStrong Either (Star f) where
  strongl (MkStar f) = MkStar $ either (map Left . f) (pure . Right)
  strongr (MkStar f) = MkStar $ either (pure . Left) (map Right . f)

public export
GenStrong Either Tagged where
  strongl (Tag x) = Tag (Left x)
  strongr (Tag x) = Tag (Right x)

public export
GenStrong Pair (Forget r) where
  strongl (MkForget k) = MkForget (k . fst)
  strongr (MkForget k) = MkForget (k . snd)

public export
Monoid r => GenStrong Either (Forget r) where
  strongl (MkForget k) = MkForget (either k (const neutral))
  strongr (MkForget k) = MkForget (either (const neutral) k)

public export
GenStrong Either (Coforget r) where
  strongl (MkCoforget k) = MkCoforget (Left . k)
  strongr (MkCoforget k) = MkCoforget (Right . k)


------------------------------------------------------------------------------
-- Tambara
------------------------------------------------------------------------------


||| The comonad generated by the reflective subcategory of profunctors that
||| implement `GenStrong ten`.
public export
record GenTambara (ten, p : Type -> Type -> Type) a b where
  constructor MkTambara
  runTambara : forall c. p (a `ten` c) (b `ten` c)

public export
Bifunctor ten => Profunctor p => Profunctor (GenTambara ten p) where
  dimap f g (MkTambara p) = MkTambara $ dimap (mapFst f) (mapFst g) p

public export
ProfunctorFunctor (GenTambara ten) where
  promap f (MkTambara p) = MkTambara (f p)

public export
Tensor ten i => ProfunctorComonad (GenTambara ten) where
  proextract (MkTambara p) = dimap unitr.rightToLeft unitr.leftToRight p
  produplicate (MkTambara p) = MkTambara $ MkTambara $ dimap assocr assocl p

public export
Associative ten => Symmetric ten => Profunctor p => GenStrong ten (GenTambara ten p) where
  strongl (MkTambara p) = MkTambara $ dimap assocr assocl p
  strongr (MkTambara p) = MkTambara $ dimap (assocr . mapFst swap')
                                            (mapFst swap' . assocl) p

public export
Bifunctor ten => Profunctor p => Functor (GenTambara ten p a) where
  map = rmap


||| The comonad generated by the reflective subcategory of profunctors that
||| implement `Strong`.
|||
||| This is a special case of `GenTambara`.
public export
Tambara : (p : Type -> Type -> Type) -> Type -> Type -> Type
Tambara = GenTambara Pair

||| The comonad generated by the reflective subcategory of profunctors that
||| implement `Choice`.
|||
||| This is a special case of `GenTambara`.
public export
TambaraSum : (p : Type -> Type -> Type) -> Type -> Type -> Type
TambaraSum = GenTambara Either


public export
tambara : GenStrong ten p => p :-> q -> p :-> GenTambara ten q
tambara @{gs} f x = MkTambara $ f $ strongl @{gs} x

public export
untambara : Tensor ten i => Profunctor q => p :-> GenTambara ten q -> p :-> q
untambara f x = dimap unitr.rightToLeft unitr.leftToRight $ runTambara $ f x


------------------------------------------------------------------------------
-- Pastro
------------------------------------------------------------------------------


||| The monad generated by the reflective subcategory of profunctors that
||| implement `GenStrong ten`.
public export
data GenPastro : (ten, p : Type -> Type -> Type) -> Type -> Type -> Type where
  MkPastro : (y `ten` z -> b) -> p x y -> (a -> x `ten` z) -> GenPastro ten p a b


public export
Profunctor (GenPastro ten p) where
  dimap f g (MkPastro l m r) = MkPastro (g . l) m (r . f)
  lmap f (MkPastro l m r) = MkPastro l m (r . f)
  rmap g (MkPastro l m r) = MkPastro (g . l) m r

public export
ProfunctorFunctor (GenPastro ten) where
  promap f (MkPastro l m r) = MkPastro l (f m) r

public export
(Tensor ten i, Symmetric ten) => ProfunctorMonad (GenPastro ten) where
  propure x = MkPastro unitr.leftToRight x unitr.rightToLeft
  projoin (MkPastro {x=x',y=y',z=z'} l' (MkPastro {x,y,z} l m r) r') = MkPastro ll m rr
    where
      ll : y `ten` (z' `ten` z) -> b
      ll = l' . mapFst l . assocl . mapSnd swap'

      rr : a -> x `ten` (z' `ten` z)
      rr = mapSnd swap' . assocr . mapFst r . r'

public export
ProfunctorAdjunction (GenPastro ten) (GenTambara ten) where
  prounit x = MkTambara (MkPastro id x id)
  procounit (MkPastro l (MkTambara x) r) = dimap r l x

public export
(Associative ten, Symmetric ten) => GenStrong ten (GenPastro ten p) where
  strongl (MkPastro {x,y,z} l m r) = MkPastro l' m r'
    where
      l' : y `ten` (z `ten` c) -> b `ten` c
      l' = mapFst l . assocl
      r' : a `ten` c -> x `ten` (z `ten` c)
      r' = assocr . mapFst r
  strongr (MkPastro {x,y,z} l m r) = MkPastro l' m r'
    where
      l' : y `ten` (c `ten` z) -> c `ten` b
      l' = swap' . mapFst l . assocl . mapSnd swap'
      r' : c `ten` a -> x `ten` (c `ten` z)
      r' = mapSnd swap' . assocr . mapFst r . swap'


||| The monad generated by the reflective subcategory of profunctors that
||| implement `Strong`.
|||
||| This is a special case of `GenPastro`.
public export
Pastro : (p : Type -> Type -> Type) -> Type -> Type -> Type
Pastro = GenPastro Pair

||| The monad generated by the reflective subcategory of profunctors that
||| implement `Choice`.
|||
||| This is a special case of `GenPastro`.
public export
PastroSum : (p : Type -> Type -> Type) -> Type -> Type -> Type
PastroSum = GenPastro Either


public export
pastro : GenStrong ten q => p :-> q -> GenPastro ten p :-> q
pastro @{gs} f (MkPastro l m r) = dimap r l (strongl @{gs} (f m))

public export
unpastro : Tensor ten i => GenPastro ten p :-> q -> p :-> q
unpastro f x = f (MkPastro unitr.leftToRight x unitr.rightToLeft)

