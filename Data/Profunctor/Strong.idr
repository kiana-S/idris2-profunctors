module Data.Profunctor.Strong

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
record GenTambara (ten, p : Type -> Type -> Type) where
  constructor MkTambara
  getTambara : {0 c : Type} -> p (a `ten` c) (b `ten` c)

public export
Tambara : (p : Type -> Type -> Type) -> Type
Tambara = GenTambara Pair
