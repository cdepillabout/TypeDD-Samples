
module Main

data GuessCmd : Type -> Nat -> Nat -> Type where
  Try : Integer -> GuessCmd Ordering (S n) n
  Pure : ty -> GuessCmd ty state state
  (>>=) : GuessCmd a x y -> (a -> GuessCmd b y z) -> GuessCmd b x z

threeGuesses : GuessCmd () 3 0
threeGuesses = do
  Try 10
  Try 20
  Try 15
  Pure ()
