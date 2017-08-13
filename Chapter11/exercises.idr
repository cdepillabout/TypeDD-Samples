
module Main

import Data.Primitives.Views

data InfList : Type -> Type where
  (::) : a -> (Inf (InfList a)) -> InfList a

%name InfList xs, ys, zs

countFrom : Nat -> InfList Nat
countFrom k = k :: Delay (countFrom (S k))

countFrom' : Nat -> InfList Nat
countFrom' k = k :: countFrom' (S k)

total
getPrefix : (count : Nat) -> InfList ty -> List ty
getPrefix Z _ = []
getPrefix (S k) (x :: xs) = x :: getPrefix k xs

labelWith : Stream labelType -> List a -> List (labelType, a)
labelWith _ [] = []
labelWith (value :: values) (x :: xs) = (value, x) :: labelWith values xs

label : List a -> List (Integer, a)
label = labelWith (iterate succ 1)

randoms : Int -> Stream Int
randoms seed =
  let seed' = 1664525 * seed + 1013904223 in
  (seed' `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms 12345)
  where
    bound : Int -> Int
    bound x with (divides x 100)
      bound ((100 * div) + rem) | (DivBy prf) = rem + 1

every_other : Stream a -> Stream a
every_other (value :: (x :: xs)) = x :: every_other xs

Functor InfList where
  map func (x :: xs) = func x :: map func xs

data Face = Heads | Tails

total
coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips Z _ = []
coinFlips (S k) (value :: xs) with (divides value 2)
  coinFlips (S k) (((2 * div) + 0) :: xs) | (DivBy prf) = Heads :: coinFlips k xs
  coinFlips (S k) (((2 * div) + n) :: xs) | (DivBy prf) = Tails :: coinFlips k xs

total
squareRootApprox : (number : Double) -> (approx : Double) -> Stream Double
squareRootApprox number approx =
  approx :: squareRootApprox number ((approx + (number / approx)) / 2)

total
squareRootBound
  : (max : Nat) ->
    (number : Double) ->
    (bound : Double) ->
    (approxs : Stream Double) ->
    Double
squareRootBound Z number bound (value :: xs) = value
squareRootBound (S k) number bound (value :: xs) =
  if abs ((value * value) - number) < bound
    then value
    else squareRootBound k number bound xs

total
squareRoot : (number : Double) -> Double
squareRoot number =
  squareRootBound 100 number 0.00000000001 (squareRootApprox number number)
