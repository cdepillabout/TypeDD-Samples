
module Main

data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
  Same : (num : Nat) -> EqNat num num

total doOnEqNat : (f: Nat -> Nat) -> EqNat num1 num2 -> EqNat (f num1) (f num2)
doOnEqNat f (Same num1) = Same (f num1)

total makeEqNat
  : Applicative f =>
    ({a : _} -> {b : _} -> f (EqNat a b)) ->
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
