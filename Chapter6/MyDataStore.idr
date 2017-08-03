module Main

import Data.Vect

infixr 4 .+.

data Schema
  = SString
  | SInt
  | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
       constructor MkData
       schema : Schema
       size : Nat
       items : Vect size (SchemaType schema)


addToStore
  : (dataStore : DataStore) -> SchemaType (schema dataStore)  -> DataStore
addToStore (MkData schema' size' store') newitem =
  MkData schema' _ (addToData store')
  where
    addToData
      : Vect size' (SchemaType schema') ->
        Vect (size' + 1) (SchemaType schema')
    addToData xs = xs ++ [newitem]
    -- addToData [] = [newitem]
    -- addToData (x :: xs) = x :: addToData xs

getEntry : (pos : Integer) -> (store : DataStore) ->
           Maybe (String, DataStore)
getEntry pos dataStore@(MkData schema' size' store') =
  case integerToFin pos size' of
    Nothing => Just ("Out of range\n", dataStore)
    Just id' => Just (?display (index id' store'), dataStore)
{-
data Command = Add String
             | Get Integer
             | Quit

parseCommand : String -> String -> Maybe Command
parseCommand "add" str = Just (Add str)
parseCommand "get" val = case all isDigit (unpack val) of
                              False => Nothing
                              True => Just (Get (cast val))
parseCommand "quit" "" = Just Quit
parseCommand _ _ = Nothing

parse : (input : String) -> Maybe Command
parse input = case span (/= ' ') input of
                   (cmd, args) => parseCommand cmd (ltrim args)

getEntry : (pos : Integer) -> (store : DataStore) ->
           Maybe (String, DataStore)
getEntry pos store
    = let store_items = items store in
          case integerToFin pos (size store) of
               Nothing => Just ("Out of range\n", store)
               Just id => Just (index id store_items ++ "\n", store)

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input
    = case parse input of
           Nothing => Just ("Invalid command\n", store)
           Just (Add item) =>
              Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
           Just (Get pos) => getEntry pos store
           Just Quit => Nothing

main : IO ()
main = replWith (MkData _ []) "Command: " processInput

-}
