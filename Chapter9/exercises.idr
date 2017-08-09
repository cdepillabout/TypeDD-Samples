
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
    (No contra) => ?ha0wa0feaf

data MyElem : (x : a) -> (vect : Vect n a) -> Type where
  MyHere : MyElem x (x :: vs)
  MyThere : MyElem x vs -> MyElem x (v :: vs)


maryInVector : MyElem "Mary" ["Peter", "Who", "Mary", "Jane"]
maryInVector = MyThere (MyThere MyHere)

total removeElem : (value : a) -> (vect : Vect (S n) a) -> (Elem value vect) -> Vect n a
removeElem value (value :: xs) Here = xs
removeElem {n = S n} value (y :: xs) (There later) =
  case removeElem value xs later of
    res => y :: res

isElem' : DecEq a => (x : a) -> (vect : Vect n a) -> Dec (Elem x vect)
isElem' x [] = No absurd
isElem' x (y :: ys) =
  case decEq x y of
    (Yes prf) => rewrite prf in Yes Here
    (No contra1) =>
      case isElem' x ys of
        (Yes prf) => Yes (There prf)
        (No contra2) => No $ \prf =>
          case prf of
            Here => contra1 Refl
            (There later) => contra2 later

notElemHeadOrTail
 : DecEq a =>
   {resVect : Vect resLen a} ->
   (contra : (value = x) -> Void) ->
   (prf1 : Elem value resVect -> Void) ->
   Elem value (x :: resVect) ->
   Void
notElemHeadOrTail contra prf1 Here = contra Refl
notElemHeadOrTail contra prf1 (There later) = prf1 later

total removeAll : DecEq a => (value : a) -> (vect : Vect n a) -> (newLen : Nat ** newVect : Vect newLen a ** (Elem value newVect -> Void))
removeAll {n = Z} value [] = (0 ** [] ** absurd)
removeAll {n = (S len)} value (x :: xs) =
  case removeAll value xs of
    (resLen ** resVect ** prf1) =>
      case decEq value x of
        (Yes prf2) => (resLen ** resVect ** prf1)
        (No contra) =>
          ((S resLen) ** (x :: resVect) ** (notElemHeadOrTail contra prf1))

data InOrderExcluding : {a : Type} -> (ex : a) -> (origVect : Vect n a) -> (newVect : Vect m a) -> Type where
  InOrderExcludingNil : InOrderExcluding ex [] []
  InOrderSkipVal
    : InOrderExcluding ex origVect newVect ->
      InOrderExcluding ex (ex :: origVect) newVect
  InOrder
    : (x = ex -> Void) ->
      InOrderExcluding ex origVect newVect ->
      InOrderExcluding ex (x :: origVect) (x :: newVect)

inorderExample1 : InOrderExcluding a [] []
inorderExample1 = InOrderExcludingNil

inorderExample2 : InOrderExcluding 3 [3] []
inorderExample2 = InOrderSkipVal InOrderExcludingNil

inorderExample3 : InOrderExcluding 3 [1,3,10] [1,10]
inorderExample3 = InOrder ?ahahha 

-- newCantContainEx : InOrderExcluding ex orig (ex :: new) -> Void
-- newCantContainEx (InOrderSkipVal next) = ?newCantContainEx_rhs_1
-- newCantContainEx (InOrder next) = ?newCantContainEx_rhs_2

-- origEmptyNewNonEmptyImpossible : InOrderExcluding ex [] (x :: xs) -> Void
-- origEmptyNewNonEmptyImpossible InOrderExcludingNil impossible
-- origEmptyNewNonEmptyImpossible (InOrderSkipVal _) impossible
-- origEmptyNewNonEmptyImpossible (InOrder _) impossible

-- changeSomething : (ex = x) -> InOrderExcluding x xs [] -> InOrderExcluding ex xs []
-- changeSomething prf e = rewrite prf in e


-- nonEmptyOrigEmptyNewNotInOrder : (contra : (ex = x) -> Void) -> InOrderExcluding ex [x] [] -> Void
-- nonEmptyOrigEmptyNewNotInOrder contra (InOrderSkipVal _) = contra Refl

-- cantBeEmptyWithNonEqVal
--   : (contra : (ex = x) -> Void) ->
--     (InOrderExcluding ex origVect []) ->
--     InOrderExcluding ex (x :: (ex :: origVect)) [] ->
--     Void
-- cantBeEmptyWithNonEqVal contra InOrderExcludingNil (InOrderSkipVal _) = contra Refl
-- cantBeEmptyWithNonEqVal contra (InOrderSkipVal _) (InOrderSkipVal _) = contra Refl


-- hahaha0fa
--   : (contra : InOrderExcluding ex xs (ex :: ys) -> Void) ->
--     InOrderExcluding ex xs ys ->
--     InOrderExcluding ex xs (ex :: ys) ->
--     Void
-- hahaha0fa contra (InOrderSkipVal y) (InOrderSkipVal x) = ?hahaha0fa_rhs_3
-- hahaha0fa contra (InOrder y) (InOrderSkipVal x) = ?hahaha0fa_rhs_4
-- hahaha0fa contra (InOrderSkipVal y) (InOrder x) = ?hahaha0fa_rhs_1
-- hahaha0fa contra (InOrder y) (InOrder x) = ?hahaha0fa_rhs_5

-- total isInOrderExcluding : DecEq a => (ex : a) -> (origVect : Vect n a) -> (newVect : Vect m a) -> Dec (InOrderExcluding ex origVect newVect)
-- isInOrderExcluding ex [] [] = Yes InOrderExcludingNil
-- isInOrderExcluding ex [] (x :: xs) = No origEmptyNewNonEmptyImpossible
-- isInOrderExcluding ex (x :: xs) [] =
--   case decEq ex x of
--     (Yes prf1) =>
--       rewrite prf1 in
--       case isInOrderExcluding ex xs [] of
--         (Yes prf2) => Yes $ (InOrderSkipVal (rewrite sym prf1 in prf2))
--         (No contra) => No $ \prf2 =>
--           case prf2 of
--             (InOrderSkipVal something) => contra (changeSomething prf1 something)
--     (No contra) =>
--       case isInOrderExcluding ex xs [] of
--         (Yes InOrderExcludingNil) => No $ nonEmptyOrigEmptyNewNotInOrder contra
--         (Yes (InOrderSkipVal next)) => No $ cantBeEmptyWithNonEqVal contra next
--         (No _) => No $ \prf2 =>
--           case prf2 of
--           (InOrderSkipVal x) => contra Refl
-- isInOrderExcluding ex (x :: xs) (y :: ys) =
--   case decEq ex x of
--     (Yes Refl) =>
--       case isInOrderExcluding ex xs (y :: ys) of
--         (Yes prf2) => Yes $ ?ha0efyaf -- rewrite sym prf1 in InOrderSkipVal prf2
--         (No contra) => No $ \prf2 =>
--           case prf2 of
--             (InOrderSkipVal next) => contra next
--             (InOrder next) => ?bababababa -- contra (hahaha0fa contra next)
--     (No contra) => ?afehfasfe_2fefaefasef
