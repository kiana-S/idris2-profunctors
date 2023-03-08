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
||| * `mapFst assocl . assocl . assocl = assocl . mapSnd assocl`
public export
interface Bifunctor ten => Associative ten where
  assocl : a `ten` (b `ten` c) -> (a `ten` b) `ten` c
  assocl = assoc.leftToRight

  assocr : (a `ten` b) `ten` c -> a `ten` (b `ten` c)
  assocr = assoc.rightToLeft

  assoc : a `ten` (b `ten` c) <=> (a `ten` b) `ten` c
  assoc = MkEquivalence assocl assocr


||| A bifunctor that admits a swap map, i.e. a bifunctor that is
||| symmetric up to isomorphism.
|||
||| The bifunctor `ten` is generally also associative.
public export
interface Bifunctor ten => Symmetric ten where
  swap' : a `ten` b -> b `ten` a
  swap' = symmetric.leftToRight

  symmetric : a `ten` b <=> b `ten` a
  symmetric = MkEquivalence swap' swap'


||| A tensor product is an associative bifunctor that has an identity element
||| up to isomorphism. Tensor products constitute the monoidal structure of a
||| monoidal category.
|||
||| Laws:
||| * `mapSnd unitl.leftToRight = mapFst unitr.leftToRight . assocl`
public export
interface Associative ten => Tensor ten i | ten where
  unitl : i `ten` a <=> a
  unitr : a `ten` i <=> a


------------------------------------------------------------------------------
-- Cartesian monoidal structure
------------------------------------------------------------------------------


export
Associative Pair where
  assocl (x,(y,z)) = ((x,y),z)
  assocr ((x,y),z) = (x,(y,z))

export
Symmetric Pair where
  swap' = swap

export
Tensor Pair () where
  unitl = MkEquivalence snd ((),)
  unitr = MkEquivalence fst (,())


------------------------------------------------------------------------------
-- Cocartesian monoidal structure
------------------------------------------------------------------------------


export
Associative Either where
  assocl (Left x) = Left (Left x)
  assocl (Right (Left x)) = Left (Right x)
  assocl (Right (Right x)) = Right x

  assocr (Left (Left x)) = Left x
  assocr (Left (Right x)) = Right (Left x)
  assocr (Right x) = Right (Right x)

export
Symmetric Either where
  swap' = either Right Left

export
Tensor Either Void where
  unitl = MkEquivalence (either absurd id) Right
  unitr = MkEquivalence (either id absurd) Left
