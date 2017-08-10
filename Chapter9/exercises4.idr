
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

wordStateFromFinished
  : Finished ->
    (guesses_remaining ** letters ** WordState guesses_remaining letters)
wordStateFromFinished (Lost {letters} game) =
  (0 ** S letters ** game)
wordStateFromFinished (Won {guesses_remaining} game) =
  (S guesses_remaining ** 0 ** game)

isFinished
  : {guesses_remaining : Nat} ->
    {letters : Nat} ->
    (state : WordState guesses_remaining letters) ->
    Dec
      ( fin : Finished **
      (wordStateFromFinished fin = (guesses_remaining ** letters ** state))
      )
isFinished {guesses_remaining = Z} {letters = Z} _ = No $ \prf =>
  case prf of
    (Lost _ ** Refl) impossible
    (Won _ ** Refl) impossible
isFinished {guesses_remaining = Z} {letters = (S k)} state =
  Yes (Lost state ** Refl)
isFinished {guesses_remaining = (S k)} {letters = Z} state =
  Yes (Won state ** Refl)
isFinished {guesses_remaining = (S k)} {letters = (S j)} _ = No $ \prf =>
  case prf of
    (Lost _ ** Refl) impossible
    (Won _ ** Refl) impossible

data ValidInput : List Char -> Type where
  Letter : (c : Char) -> ValidInput [c]

isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No $ \prf =>
  case prf of
    (Letter _) impossible
isValidInput (x :: []) = Yes $ Letter x
isValidInput (x :: y :: xs) = No $ \prf =>
  case prf of
    (Letter _) impossible

isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = isValidInput $ unpack s

readGuess : IO (x ** ValidInput x)
readGuess = do
  putStr "Guess: "
  x <- getLine
  case isValidString (toLower x) of
    (Yes validInput) => pure (_ ** validInput)
    (No contra) => do
      putStrLn "invalid guess"
      readGuess

removeElem : (x : a) -> (vect : Vect (S n) a) -> {auto prf : Elem x vect} -> Vect n a
removeElem x (x :: xs) {prf = Here} = xs
removeElem {n = Z} _ (_ :: _) {prf = (There _)} impossible
removeElem {n = (S k)} x (y :: xs) {prf = (There _)} = y :: removeElem x xs

processGuess
  : (letter : Char) ->
    WordState (S guesses) (S letters) ->
    Either
      (WordState guesses (S letters))
      (WordState (S guesses) letters)
processGuess {letters} letter (MkWordState word missing) =
  case isElem letter missing of
    (Yes _) =>
      let newMissing = removeElem letter missing
      in Right $ MkWordState word newMissing
    (No _) => Left $ MkWordState word missing

game : WordState (S guesses) (S letters) -> IO Finished
game {guesses} {letters} state = do
  (_ ** Letter letter) <- readGuess
  case processGuess letter state of
    (Left l) => do
      putStrLn "Wrong"
      case guesses of
        Z => pure (Lost l)
        (S _) => game l
    (Right r) => do
      putStrLn "Right"
      case letters of
        Z => pure (Won r)
        (S _) => game r


main : IO ()
main = do
  result <- game {guesses = 2} $ MkWordState "test" ['t', 'e', 's']
  case result of
    (Lost game) => putStrLn "You lose!"
    (Won game) => putStrLn "You win!"
