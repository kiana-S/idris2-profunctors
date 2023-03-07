module Data.Profunctor.Mapping

import Data.Profunctor
import Data.Profunctor.Traversing

%default total


public export
interface (Traversing p, Closed p) => Mapping p where
  map' : Functor f => p a b -> p (f a) (f b)
  map' = roam map

  roam : ((a -> b) -> s -> t) -> p a b -> p s t
  roam f = dimap (flip f) ($ id) . map' @{%search} @{functor}
    where
      functor : Functor (\a => (a -> b) -> t)
      functor = MkFunctor (\f => (. (. f)))
