
module Main

interface MyFunctor (f : Type -> Type) where
  fmap : (func : a -> b) -> f a -> f b

MyFunctor Maybe where
  fmap f Nothing = Nothing
  fmap f (Just x) = Just $ f x

MyFunctor List where
  fmap f [] = []
  fmap f (x :: xs) = f x :: fmap f xs

interface MyFunctor f => MyFunctorLaws (f : Type -> Type) where
  fmapIdLaw : (x : f a) -> fmap Basics.id x = x
  functorComposition
    : {a : Type} ->
      {b : Type} ->
      (x : f a) ->
      (g1 : a -> b) ->
      (g2 : b -> c) ->
      fmap (g2 . g1) x = (fmap g2 . fmap g1) x

MyFunctorLaws Maybe where
  fmapIdLaw Nothing = Refl
  fmapIdLaw (Just y) = Refl

  functorComposition Nothing g1 g2 = Refl
  functorComposition (Just x) g1 g2 = Refl

MyFunctorLaws List where
  fmapIdLaw Nil = Refl
  fmapIdLaw (x :: xs) = rewrite fmapIdLaw xs in Refl

  functorComposition [] g1 g2 = Refl
  functorComposition (x :: xs) g1 g2 =
    let lalala = functorComposition xs g1 g2 in
    rewrite lalala in
    Refl
