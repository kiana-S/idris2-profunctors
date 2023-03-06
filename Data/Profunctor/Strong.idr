module Data.Profunctor.Strong

import Data.Tensor
import Data.Profunctor.Functor
import Data.Profunctor.Types

%default total

public export
interface Profunctor p => GenStrong (0 ten : Type -> Type -> Type) p where
  strongl : p a b -> p (a `ten` c) (b `ten` c)
  strongr : p a b -> p (c `ten` a) (c `ten` b)


public export
Strong : (p : Type -> Type -> Type) -> Type
Strong = GenStrong Pair

public export
first : Strong p => p a b -> p (a, c) (b, c)
first = strongl {ten=Pair}

public export
second : Strong p => p a b -> p (c, a) (c, b)
second = strongr {ten=Pair}

public export
Choice : (p : Type -> Type -> Type) -> Type
Choice = GenStrong Either

public export
left : Choice p => p a b -> p (Either a c) (Either b c)
left = strongl {ten=Either}

public export
right : Choice p => p a b -> p (Either c a) (Either c b)
right = strongr {ten=Either}



export
uncurry' : Strong p => p a (b -> c) -> p (a, b) c
uncurry' = rmap (uncurry id) . first


-- Tambara

public export
record GenTambara (ten, p : Type -> Type -> Type) a b where
  constructor MkTambara
  getTambara : {0 c : Type} -> p (a `ten` c) (b `ten` c)

export
Bifunctor ten => Profunctor p => Profunctor (GenTambara ten p) where
  dimap f g (MkTambara p) = MkTambara $ dimap (mapFst f) (mapFst g) p

export
ProfunctorFunctor (GenTambara ten) where
  promap f (MkTambara p) = MkTambara (f p)

export
Tensor ten i => ProfunctorComonad (GenTambara ten) where
  proextract (MkTambara p) = dimap unitr.bwd unitr.fwd p
  produplicate (MkTambara p) = MkTambara $ MkTambara $ dimap assoc.bwd assoc.fwd p

export
Associative ten => Symmetric ten => Profunctor p => GenStrong ten (GenTambara ten p) where
  strongl (MkTambara p) = MkTambara $ dimap assoc.bwd assoc.fwd p
  strongr = dimap swap swap . strongl {ten,p=GenTambara ten p}

export
Bifunctor ten => Profunctor p => Functor (GenTambara ten p a) where
  map = rmap


export
gentambara : GenStrong ten p => p :-> q -> p :-> GenTambara ten q
gentambara @{gs} f x = MkTambara $ f $ strongl @{gs} x

export
ungentambara : Tensor ten i => Profunctor q => p :-> GenTambara ten q -> p :-> q
ungentambara f x = dimap unitr.bwd unitr.fwd $ getTambara $ f x

public export
Tambara : (p : Type -> Type -> Type) -> Type
Tambara = GenTambara Pair

-- Pastro

public export
data GenPastro : (ten, p : Type -> Type -> Type) -> Type -> Type -> Type where
  MkPastro : (y `ten` z -> b) -> p x y -> (a -> x `ten` z) -> GenPastro ten p a b


export
Profunctor (GenPastro ten p) where
  dimap f g (MkPastro l m r) = MkPastro (g . l) m (r . f)
  lmap f (MkPastro l m r) = MkPastro l m (r . f)
  rmap g (MkPastro l m r) = MkPastro (g . l) m r

export
ProfunctorFunctor (GenPastro ten) where
  promap f (MkPastro l m r) = MkPastro l (f m) r

export
(Tensor ten i, Symmetric ten) => ProfunctorMonad (GenPastro ten) where
  propure x = MkPastro unitr.fwd x unitr.bwd
  projoin (MkPastro {x=x',y=y',z=z'} l' (MkPastro {x,y,z} l m r) r') = MkPastro ll m rr
    where
      ll : y `ten` (z' `ten` z) -> b
      ll = l' . mapFst l . assoc.fwd . mapSnd swap

      rr : a -> x `ten` (z' `ten` z)
      rr = mapSnd swap . assoc.bwd . mapFst r . r'

export
ProfunctorAdjunction (GenPastro ten) (GenTambara ten) where
  prounit x = MkTambara (MkPastro id x id)
  procounit (MkPastro l (MkTambara x) r) = dimap r l x

export
(Associative ten, Symmetric ten) => GenStrong ten (GenPastro ten p) where
  strongl (MkPastro {x,y,z} l m r) = MkPastro l' m r'
    where
      l' : y `ten` (z `ten` c) -> b `ten` c
      l' = mapFst l . assoc.fwd
      r' : a `ten` c -> x `ten` (z `ten` c)
      r' = assoc.bwd . mapFst r
  strongr (MkPastro {x,y,z} l m r) = MkPastro l' m r'
    where
      l' : y `ten` (c `ten` z) -> c `ten` b
      l' = swap . mapFst l . assoc.fwd . mapSnd swap
      r' : c `ten` a -> x `ten` (c `ten` z)
      r' = mapSnd swap . assoc.bwd . mapFst r . swap


export
genpastro : GenStrong ten q => p :-> q -> GenPastro ten p :-> q
genpastro @{gs} f (MkPastro l m r) = dimap r l (strongl @{gs} (f m))

export
ungenpastro : Tensor ten i => GenPastro ten p :-> q -> p :-> q
ungenpastro f x = f (MkPastro unitr.fwd x unitr.bwd)

