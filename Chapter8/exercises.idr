
module Main

data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
  Same : (num : Nat) -> EqNat num num

total doOnEqNat : (f: Nat -> Nat) -> EqNat num1 num2 -> EqNat (f num1) (f num2)
doOnEqNat f (Same num1) = Same (f num1)

total makeEqNat
  : Applicative f =>
    ({a : Nat} -> {b : Nat} -> f (EqNat a b)) ->
    (num1 : Nat) ->
    (num2 : Nat) ->
    f (EqNat num1 num2)
makeEqNat _ Z Z = pure $ Same 0
makeEqNat badVal Z (S k) = badVal
makeEqNat badVal (S k) Z = badVal
makeEqNat badVal (S k) (S j) = doOnEqNat succ <$> makeEqNat badVal k j

use : Nat -> Nat -> String
use nat1 nat2 =
  case makeEqNat Nothing nat1 nat2 of
       Nothing => "Not equal"
       (Just (Same sss)) => "Same nat: " ++ show sss

data EqBoi : {a : Type} -> (ty1 : a) -> (ty2 : a) -> Type where
  SameBoi : (ty : a) -> EqBoi ty ty

total doOnEqBoi
  : {a : Type} ->
    {ty1: a} ->
    {ty2: a} ->
    (f: a -> a) ->
    EqBoi ty1 ty2 ->
    EqBoi (f ty1) (f ty2)
doOnEqBoi f (SameBoi ty1) = SameBoi $ f ty1

total makeEqBoi
  : {a : Type} ->
    (num1 : Integer) ->
    (num2 : Integer) ->
    Maybe (EqBoi num1 num2)
makeEqBoi num1 num2 = Nothing

data Vect : Nat -> a -> Type where
  Nil : Vect 0 a
  (::) : a -> Vect n a -> Vect (S n) a

exactLen : Monad f => ({a : Nat} -> {b : Nat} -> f (EqNat a b)) -> (len : Nat) -> Vect m a -> f (Vect len a)
exactLen {m} nothing len x = do
  (Same _) <- makeEqNat nothing m len
  pure x

data EqNat2 : (num1 : Nat) -> (num2 : Nat) -> Type where
  Same2 : EqNat2 num num

plusOkay : {k : Nat} -> {j : Nat} -> (what : EqNat2 k j) -> EqNat2 (S k) (S j)
plusOkay {k = j} {j = j} Same2 = Same2

makeEqNat2
  : (num1 : Nat) ->
    (num2 : Nat) ->
    Maybe (EqNat2 num1 num2)
makeEqNat2 Z Z = pure Same2
makeEqNat2 Z (S k) = Nothing
makeEqNat2 (S k) Z = Nothing
makeEqNat2 (S k) (S j) =
  map plusOkay $ makeEqNat2 k j

use2 : Nat -> Nat -> String
use2 nat1 nat2 =
  case makeEqNat2 nat1 nat2 of
    Nothing => "Not equal"
    (Just Same) => "Same nat: " ++ show nat1

what : Void -> EqNat2 a b
what x = absurd x

app : Vect n a -> Vect m a -> Vect (n + m) a
app [] y = y
app (x :: z) y = x :: app z y

appEmptyLeft : {xs : Vect n a} -> app [] xs = xs
appEmptyLeft {xs} = Refl

appEmptyRight : {xs : Vect n a} -> xs = app xs []
appEmptyRight {xs = []} = Refl
appEmptyRight {xs = (x :: y)} = ?idunno
  -- case appEmptyRight {xs=y} of
  --   Refl => ?asefasef

plusIsSucc : {k : Nat} -> EqNat2 (plus k 1) (S k)
plusIsSucc {k = Z} = Same2
plusIsSucc {k = (S k)} = plusOkay plusIsSucc

lalaVect : Vect a x -> EqNat2 a b -> Vect b x
lalaVect x Same2 = x

reverse : Vect n a -> Vect n a
reverse {n = Z} [] = []
reverse {n = (S k)} (x :: xs) =
  let lala = app (reverse xs) [x]
  in lalaVect lala plusIsSucc

mycong : {f : a -> b} -> x = y -> f x = f y
mycong Refl = Refl

plusZeroIsSame : {k : Nat} -> k + 0 = k
plusZeroIsSame {k = Z} = Refl
plusZeroIsSame {k = (S k)} = cong plusZeroIsSame

plusIsSucc2 : plus k 1 = S k
plusIsSucc2 {k = Z} = Refl
plusIsSucc2 {k = (S k)} = mycong plusIsSucc2

someTransform :  {f : Type -> Type} -> n = m -> f n -> f m
someTransform Refl fn = fn

vectLenTrans : n = m -> Vect n a -> Vect m a
vectLenTrans Refl x = x

reverse2 : Vect n a -> Vect n a
reverse2 {n = Z} [] = []
reverse2 {n = (S k)} (x :: xs) =
  let reversedList = app (reverse xs) [x]
  in vectLenTrans plusIsSucc2 reversedList

same_cons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
same_cons {xs = ys} {ys = ys} Refl = Refl

same_lists
  : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
same_lists {xs = ys} {ys = ys} Refl Refl = Refl

data ThreeEq : {a : Type} -> {b : Type} -> {c : Type} -> (x : a) -> (y : b) -> (z : d) -> Type where
  Same3 : ThreeEq x x x

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS z z z Same3 = Same3

lalaReverse : {a : Type} -> {n : Nat} -> {x : a} -> {y : Vect n a} -> reverse2 (x :: y) = (app (reverse2 y) [x])
lalaReverse {x = x} {y = []} = Refl
lalaReverse {n = S n} {x = x} {y = (y :: ys)} = ?gagaga
  -- case lalaReverse {x = y} {y = ys} of
  --   Refl => ?aesfaefg

lalaReverseTryTwo
  : {x : a} -> {y : a} -> {rest : Vect n a} ->
    reverse2 (y :: rest) = app (reverse2 rest) [y] ->
    reverse2 (x :: y :: rest) = app (reverse2 rest) [y,x]
lalaReverseTryTwo {x} {y} {rest} prf = ?lalaReverseTryTwo_rhs

reverseTest : reverse2 (reverse2 v) = v
reverseTest {v = []} = Refl
reverseTest {v = (x :: y)} = ?reverseTest_rhs_2

plus0K : (k : Nat) -> 0 + k = k
plus0K k = Refl

plusK0 : (k : Nat) -> k + 0 = k
plusK0 Z = Refl
plusK0 (S k) =
  rewrite plusK0 k
  in Refl

plusTakeOutS : (left : Nat) -> (right : Nat) -> S (left + right) = left + S right
plusTakeOutS Z right = Refl
plusTakeOutS (S k) right =
  let ind = plusTakeOutS k right
  in rewrite ind
  in Refl

plusWhat : (left : Nat) -> (right : Nat) -> left + (S right) = (S left) + right
plusWhat Z right = Refl
plusWhat (S left) right =
  let ind = plusWhat left right
  in rewrite ind
  in Refl

plusCommutative' : (left : Nat) -> (right : Nat) -> left + right = right + left
plusCommutative' Z right = rewrite plusK0 right in Refl
plusCommutative' (S left) right =
  let ind = plusCommutative' left right in
  rewrite ind in
    plusTakeOutS right left
