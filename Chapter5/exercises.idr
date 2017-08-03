
module Main

import Data.Vect
import System

readNumber : String -> Maybe Nat
readNumber line =
  if all isDigit $ unpack line
    then Just $ cast line
    else Nothing

readNumberIO : IO (Maybe Nat)
readNumberIO = map readNumber getLine

data GuessType = High | Low | Correct

processGuess : (target : Nat) -> (guess' : Nat) -> GuessType
processGuess target guess' =
  case compare guess' target of
    LT => Low
    EQ => Correct
    GT => High

guess : (target : Nat) -> (guesses : Nat) -> IO ()
guess target guesses = do
  putStr $ "guess number (guess number " ++ show guesses ++ "): "
  Just num <- readNumberIO
    | Nothing => do
        putStrLn "Not a number."
        guess target guesses
  case processGuess target num of
    High => do
      putStrLn "Guess too high."
      guess target (succ guesses)
    Low => do
      putStrLn "Guess too low."
      guess target (succ guesses)
    Correct => putStrLn "Correct!"

guessRandom : IO ()
guessRandom = do
  t <- time
  let randomNum = mod t 100
  guess (cast randomNum) 1

readVect : IO (len ** Vect len String)
readVect = do
  line <- getLine
  case line of
    "" => pure (_ ** [])
    _ => do
      (_ ** vect) <- readVect
      pure (_ ** line :: vect)

zipInputs : IO ()
zipInputs = do
  putStrLn "Enter first vector (blank line to end):"
  (len1 ** vect1) <- readVect
  putStrLn "Enter second vector (blank line to end):"
  (len2 ** vect2) <- readVect
  case exactLength len1 vect2 of
    Nothing => putStrLn "Vectors are different lengths."
    (Just newVect) => printLn (zip vect1 newVect)

readToBlank : IO (List String)
readToBlank = do
  line <- getLine
  case line of
    "" => pure []
    _ => do
      rest <- readToBlank
      pure $ line :: rest

linesToString : List String -> String
linesToString xs = concat $ intersperse "\n" xs

readAndSave : IO ()
readAndSave = do
  putStrLn "Enter lines:"
  lines <- readToBlank
  putStr "Enter filename: "
  filename <- getLine
  Right () <- writeFile filename (linesToString lines)
    | Left err => do
        putStrLn ("Got error when trying to write to file: " ++ show err)
  pure ()

readFromFile : (file : File) -> IO (n ** Vect n String)
readFromFile file = do
  Right line <- fGetLine file
    | Left err => do
        putStrLn ("Got error when trying to get line from file: " ++ show err)
        pure (_ ** [])
  putStrLn ("Got line from file: " ++ line)
  case line of
    "" => do
      putStrLn ("Got empty line from file")
      pure (_ ** [])
    _ => do
      (_ ** vect) <- readFromFile file
      pure $ (_ ** line :: vect)

readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename = do
  Right file <- openFile filename Read
    | Left err => do
        putStrLn ("Got error when trying to read file: " ++ show err)
        pure (_ ** [])
  res <- readFromFile file
  closeFile file
  pure res



