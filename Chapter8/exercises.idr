
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
