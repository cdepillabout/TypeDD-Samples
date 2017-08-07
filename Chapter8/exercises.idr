
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

mycong : {f : x -> x} -> a = b -> f a = f b
mycong Refl = Refl

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

reverseTest : reverse2 (reverse2 v) = v
reverseTest {v} = ?reverseTest_rhs
