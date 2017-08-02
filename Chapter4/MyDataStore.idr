
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
     Search : String -> Command
     Size : Command

     Quit : Command

%name Command cmd, cmd1, cmd2

total getDigit : String -> Maybe Nat
getDigit x =
  case all isDigit $ unpack x of
    False => Nothing
    True =>
      case (the Integer $ cast x) >= 0 of
        False => Nothing
        True => Just $ cast x

total parseCommand : String -> Maybe Command
parseCommand str =
  case span (/= ' ') str of
    ("add", rest) => Just $ Add (ltrim rest)
    ("get", rest) =>
      case getDigit (ltrim rest) of
        Nothing => Nothing
        Just digit => Just $ Get digit
    ("search", rest) => Just $ Search (ltrim rest)
    ("size", _) => Just Size
    ("quit", _) => Just Quit
    _ => Nothing

total getItem : (dataStore : DataStore) -> (idx : Nat) -> Maybe String
getItem (MkData size items) idx = do
  fin <- natToFin idx size
  pure $ index fin items

createMatches : String -> String -> String
createMatches x "" = x
createMatches x acc = x ++ ", " ++ acc

total handleCommand
  : (dataStore : DataStore) -> Maybe Command -> Maybe (String, DataStore)
handleCommand dataStore Nothing = 
  Just ("invalid command\n", dataStore)
handleCommand dataStore (Just (Add str)) =
  Just ("added to store: " ++ str ++ "\n", addToStore dataStore str)
handleCommand dataStore (Just (Get idx)) =
  case getItem dataStore idx of
    Just item => Just ("item: " ++ item ++ "\n", dataStore)
    Nothing => Just ("index out of range\n", dataStore)
handleCommand dataStore (Just (Search searchString)) =
    let (_ ** matches) = filter (isInfixOf searchString) $ items dataStore
        matchesStr = foldr createMatches "" matches
    in Just ("matches: " ++ matchesStr ++ "\n", dataStore)
handleCommand dataStore (Just Size) =
  let dataSize = cast $ the Int $ cast (size dataStore)
  in Just ("size: " ++ dataSize ++ "\n", dataStore)
handleCommand dataStore (Just Quit) = Nothing

total doAction : DataStore -> String -> Maybe (String, DataStore)
doAction dataStore command =
  handleCommand dataStore $ parseCommand command

main : IO ()
main = replWith initDataStore "Command: " doAction

-- vectLen : {n : Nat} -> {a : Type} -> Vect n a -> Fin n
-- vectLen {n=n} xs = case natToFin n (S n) of
--         Nothing => ?what
--         (Just x) => ?who

vectLen : {n : Nat} -> {a : Type} -> Vect n a -> Nat
vectLen {n} xs = n

-- lala : Nat -> (n : Nat) -> String
-- lala _ _ = "hello"
