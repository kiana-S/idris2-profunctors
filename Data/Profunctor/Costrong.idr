module Data.Profunctor.Costrong

import Data.Morphisms
import Data.Tensor
import Data.Profunctor.Functor
import Data.Profunctor.Types

%default total

public export
interface Profunctor p => GenCostrong (0 ten : Type -> Type -> Type) p where
  costrongl : p (a `ten` c) (b `ten` c) -> p a b
  costrongr : p (c `ten` a) (c `ten` b) -> p a b


public export
Costrong : (p : Type -> Type -> Type) -> Type
Costrong = GenCostrong Pair

public export
unfirst : Costrong p => p (a, c) (b, c) -> p a b
unfirst = costrongl {ten=Pair}

public export
unsecond : Costrong p => p (c, a) (c, b) -> p a b
unsecond = costrongr {ten=Pair}

public export
Cochoice : (p : Type -> Type -> Type) -> Type
Cochoice = GenCostrong Either

public export
unleft : Cochoice p => p (Either a c) (Either b c) -> p a b
unleft = costrongl {ten=Either}

public export
unright : Cochoice p => p (Either c a) (Either c b) -> p a b
unright = costrongr {ten=Either}

-- Implementations

export
GenCostrong Pair Tagged where
  costrongl (Tag (x,_)) = Tag x
  costrongr (Tag (_,x)) = Tag x


-- Tambara

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


export
gencotambara : GenCostrong ten p => p :-> q -> p :-> GenCotambara ten q
gencotambara f = MkCotambara f

export
ungencotambara : Tensor ten i => Profunctor q => p :-> GenCotambara ten q -> p :-> q
ungencotambara f p = proextract (f p)


public export
Cotambara : (p : Type -> Type -> Type) -> Type -> Type -> Type
Cotambara = GenCotambara Pair

export
cotambara : Costrong p => p :-> q -> p :-> Cotambara q
cotambara = gencotambara

export
uncotambara : Profunctor q => p :-> Cotambara q -> p :-> q
uncotambara = ungencotambara


public export
CotambaraSum : (p : Type -> Type -> Type) -> Type -> Type -> Type
CotambaraSum = GenCotambara Either

export
cotambaraSum : Cochoice p => p :-> q -> p :-> CotambaraSum q
cotambaraSum = gencotambara

export
uncotambaraSum : Profunctor q => p :-> CotambaraSum q -> p :-> q
uncotambaraSum = ungencotambara


-- Copastro

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


public export
Copastro : (p : Type -> Type -> Type) -> Type -> Type -> Type
Copastro = GenCopastro Pair

public export
CopastroSum : (p : Type -> Type -> Type) -> Type -> Type -> Type
CopastroSum = GenCopastro Either


export
copastro : GenCostrong ten q => p :-> q -> GenCopastro ten p :-> q
copastro f (MkCopastro h) = h f

export
uncopastro : Tensor ten i => GenCopastro ten p :-> q -> p :-> q
uncopastro f x = f (MkCopastro ($ x))
