
module Main

import Data.Vect

data MyElem : a -> Vect k a -> Type where
  MyHere : MyElem x (x :: xs)
  MyThere : (later : MyElem x xs) -> MyElem x (y :: xs)

Uninhabited (MyElem value []) where
  uninhabited MyHere impossible
  uninhabited (MyThere _) impossible

myIsElem : DecEq a => (value : a) -> (xs : Vect n a) -> Dec (MyElem value xs)
myIsElem value [] = No absurd
myIsElem value (x :: xs) =
  case decEq value x of
    (Yes Refl) => Yes MyHere
    (No contra) =>
      case myIsElem value xs of
        (Yes prf) => Yes (MyThere prf)
        (No contra2) => No $ \prf2 =>
          case prf2 of
            MyHere => contra Refl
            (MyThere later) => contra2 later

data MyElemList : a -> List a -> Type where
  MyHereList : MyElemList x (x :: xs)
  MyThereList : (later : MyElemList x xs) -> MyElemList x (y :: xs)

data MyLast : a -> Vect n a -> Type where
  IsLast : MyLast a [a]
  NotYetLast : MyLast a xs -> MyLast a (y :: xs)

Uninhabited (MyLast value []) where
  uninhabited IsLast impossible
  uninhabited (NotYetLast _) impossible

total isLast : DecEq a => (x : a) -> (xs : Vect n a) -> Dec (MyLast x xs)
isLast x [] = No absurd
isLast x [y] =
  case decEq x y of
    (Yes xIsY) => Yes $ rewrite xIsY in IsLast
    (No xIsNotY) => No $ \IsLast => xIsNotY Refl
isLast x (y :: (gaga :: papas)) =
  case isLast x (gaga :: papas) of
    (Yes xIsLast) => Yes $ NotYetLast xIsLast
    (No xIsNotLast) => No $ \(NotYetLast next) => xIsNotLast next

example4 : MyLast 3 [1,2,3]
example4 = NotYetLast (NotYetLast IsLast)
