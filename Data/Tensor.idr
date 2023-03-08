||| This module defines tensor products, which are later used to define
||| the concept of profunctor strength. The two primary tensor products
||| in `Idr` are the product (`Pair`) and the coproduct (`Either`).
module Data.Tensor

%default total


------------------------------------------------------------------------------
-- Tensor products
------------------------------------------------------------------------------


||| A bifunctor that admits an *associator*, i.e. a bifunctor that is
||| associative up to isomorphism.
|||
||| Laws:
||| * `mapFst assoc.rightToLeft . assoc.leftToRight . assoc.leftToRight = assoc.leftToRight . mapSnd assoc.leftToRight`
public export
interface Bifunctor ten => Associative ten where
  assoc : a `ten` (b `ten` c) <=> (a `ten` b) `ten` c

||| A bifunctor that admits a swap map, i.e. a bifunctor that is
||| symmetric up to isomorphism.
|||
||| The bifunctor `ten` is generally also associative.
public export
interface Bifunctor ten => Symmetric ten where
  swap : a `ten` b -> b `ten` a
  swap = symmetric.leftToRight

  symmetric : a `ten` b <=> b `ten` a
  symmetric = MkEquivalence swap swap


||| A tensor product is an associative bifunctor that has an identity element
||| up to isomorphism. Tensor products constitute the monoidal structure of a
||| monoidal category.
|||
||| Laws:
||| * `mapSnd unitl.leftToRight = mapFst unitr.leftToRight . assoc.leftToRight`
public export
interface Associative ten => Tensor ten i | ten where
  unitl : i `ten` a <=> a
  unitr : a `ten` i <=> a


------------------------------------------------------------------------------
-- Cartesian monoidal structure
------------------------------------------------------------------------------


export
Associative Pair where
  assoc = MkEquivalence (\(x,(y,z)) => ((x,y),z)) (\((x,y),z) => (x,(y,z)))

export
Symmetric Pair where
  swap = Builtin.swap

export
Tensor Pair () where
  unitl = MkEquivalence snd ((),)
  unitr = MkEquivalence fst (,())


------------------------------------------------------------------------------
-- Cocartesian monoidal structure
------------------------------------------------------------------------------


export
Associative Either where
  assoc = MkEquivalence f b
    where
      f : forall a,b,c. Either a (Either b c) -> Either (Either a b) c
      f (Left x) = Left (Left x)
      f (Right (Left x)) = Left (Right x)
      f (Right (Right x)) = Right x

      b : forall a,b,c. Either (Either a b) c -> Either a (Either b c)
      b (Left (Left x)) = Left x
      b (Left (Right x)) = Right (Left x)
      b (Right x) = Right (Right x)

export
Symmetric Either where
  swap = either Right Left

export
Tensor Either Void where
  unitl = MkEquivalence (either absurd id) Right
  unitr = MkEquivalence (either id absurd) Left
