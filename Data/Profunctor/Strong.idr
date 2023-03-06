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
