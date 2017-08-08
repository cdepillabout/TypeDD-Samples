
module Main

import Data.Vect

headVect : Vect (S n) a -> a
headVect (x :: _) = x

data LessThanHead : (item : a) -> (vect : Vect n a) -> Type where
  LessThanNil : LessThanHead item []
  LessThanHeadC
    : Ord a =>
      {item : a} ->
      {vect : Vect (S n) a} ->
      (item < headVect vect = True) ->
      LessThanHead item vect

data OrderedVect : (Vect n a) -> Type where
  OrderedVectNil : OrderedVect []
  OrderedVectCons
    : (item: a) ->
      OrderedVect vect ->
      LessThanHead item vect ->
      OrderedVect (item :: vect)

createLessThanHead : LessThanHead 1 []
createLessThanHead = LessThanNil

createLessThanHead2 : LessThanHead 4 [5]
createLessThanHead2 = LessThanHeadC Refl

createLessThanHead3 : LessThanHead 4 [5,6]
createLessThanHead3 = LessThanHeadC Refl

createOrderedVect : OrderedVect []
createOrderedVect = OrderedVectNil

createOrderedVect2 : OrderedVect [1,2]
createOrderedVect2 =
  OrderedVectCons
    1
    (OrderedVectCons 2 OrderedVectNil LessThanNil)
    (LessThanHeadC Refl)

isLessThan2 : Ord a => (item1 : a) -> (item2 : a) -> (item1 : a ** (item2 : a ** Dec (compare item1 item2 = LT)))
isLessThan2 item1 item2 = (item1 ** item2 **
  case compare item1 item2 of
    what => ?who
  )

isLessThan : Ord a => (item1 : a) -> (item2 : a) -> Dec (item1 < item2 = True)
isLessThan item1 item2 =
  case item1 < item2 of
    True => ?haha
    False => ?aaaa

isLessThanHead : (item : a) -> (vect : Vect n a) -> Dec (LessThanHead item vect)
isLessThanHead item [] = Yes LessThanNil
isLessThanHead item (x :: xs) = ?isLessThanHead_rhs_2

isOrderedVect : {n : Nat} -> (vect : Vect n a) -> Dec (OrderedVect vect)
isOrderedVect [] = Yes OrderedVectNil
isOrderedVect {n = S m} (x :: xs) =
  case isOrderedVect xs of
    (Yes OrderedVectNil) => Yes $ OrderedVectCons x OrderedVectNil LessThanNil
    (Yes (OrderedVectCons item orderedVect prf)) => ?isOrderedVect_rhs_4
    (No contra) => ?isOrderedVect_rhs_3
