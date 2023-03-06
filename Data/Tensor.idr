module Data.Tensor

%default total


public export
interface Bifunctor ten => Associative ten where
  assoc : a `ten` (b `ten` c) <=> (a `ten` b) `ten` c

public export
interface Bifunctor ten => Symmetric ten where
  swap : a `ten` b -> b `ten` a
  swap = symmetric.leftToRight

  symmetric : a `ten` b <=> b `ten` a
  symmetric = MkEquivalence swap swap



public export
interface Associative ten => Tensor ten i | ten where
  unitl : i `ten` a <=> a
  unitr : a `ten` i <=> a


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
