
module Main

import Data.Vect

data DataStore : Type where
     MkData : (size : Nat) ->
              (items : Vect size String) ->
              DataStore

%name DataStore dataStore, dataStore1

initDataStore : DataStore
initDataStore = MkData 0 []

size : DataStore -> Nat
size (MkData size' _) = size'

items : (store : DataStore) -> Vect (size store) String
items (MkData _ items') = items'

addToStore : DataStore -> String -> DataStore
addToStore (MkData _ items') y = MkData _ (items' ++ [y])

data Command : Type where
     Add : String -> Command
     Get : Nat -> Command
     Quit : Command

getDigit : String -> Maybe Nat
getDigit x =
  case all isDigit $ unpack x of
    False => Nothing
    True =>
      case (the Integer $ cast x) >= 0 of
        False => Nothing
        True => Just $ cast x

parseCommand : String -> Maybe Command
parseCommand str =
  case span (/= ' ') str of
    ("add", rest) => Just $ Add (ltrim rest)
    ("get", rest) =>
      case getDigit (ltrim rest) of
        Nothing => Nothing
        Just digit => Just $ Get digit
    ("quit", _) => Just Quit
    _ => Nothing

getItem : (dataStore : DataStore) -> (idx : Nat) -> Maybe String
getItem (MkData size items) idx = do
  fin <- natToFin idx size
  pure $ index fin items

doAction : DataStore -> String -> Maybe (String, DataStore)
doAction dataStore command =
  case parseCommand command of
        Nothing =>
          Just ("invalid command\n", dataStore)
        (Just (Add str)) =>
          Just ("added to store: " ++ str ++ "\n", addToStore dataStore str)
        (Just (Get idx)) =>
          case getItem dataStore idx of
            Just item => Just ("item: " ++ item ++ "\n", dataStore)
            Nothing => Just ("index out of range\n", dataStore)
        (Just Quit) =>
          Nothing

main : IO ()
main = replWith initDataStore "Command: " doAction
