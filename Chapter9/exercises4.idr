
module Main

import Data.Vect

data WordState : (guesses_remaining : Nat) -> (letters : Nat) -> Type where
  MkWordState
    : (word : String) ->
      (missing : Vect letters Char) ->
      WordState guesses_remaining letters

data Finished : Type where
  Lost : (game : WordState 0 (S letters)) -> Finished
  Won : (game : WordState (S guesses_remaining) 0) -> Finished

-- isFinished : {guesses_remaining : Nat} -> {letters : Nat} -> WordState guesses_remaining letters -> Dec Finished
-- isFinished {guesses_remaining = Z} {letters = Z} wordState = Yes $ Won ?ahasefaef
-- isFinished {guesses_remaining = Z} {letters = (S k)} wordState = Yes $ Lost wordState
-- isFinished {guesses_remaining = (S k)} {letters = Z} wordState = Yes $ Won wordState
-- isFinished {guesses_remaining = (S k)} {letters = (S j)} wordState = No $ \prf =>
--   case prf of
--     (Lost game) => ?hfesa_1
--     (Won game) => ?hfesa_2

game : WordState (S guesses) (S letters) -> IO Finished
game state = ?hfsa
