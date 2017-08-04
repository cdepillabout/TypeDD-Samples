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

data Command : Schema -> Type where
  SetSchema : (newSchema : Schema) -> Command schema
  Add : SchemaType schema -> Command schema
  Get : Integer -> Command schema
  Quit : Command schema

record DataStore where
       constructor MkData
       schema : Schema
       size : Nat
       items : Vect size (SchemaType schema)

addToStore
  : (dataStore : DataStore) -> SchemaType (schema dataStore) -> DataStore
addToStore (MkData schema' size' store') newitem =
  MkData schema' _ (addToData store')
  where
    addToData
      : Vect size' (SchemaType schema') -> Vect (size' + 1) (SchemaType schema')
    addToData xs = xs ++ [newitem]

display : SchemaType schema' -> String
display {schema' = SString} x = "\"" ++ x ++ "\""
display {schema' = SInt} x = cast x
display {schema' = (_ .+. _)} (a, b) = display a ++ " " ++ display b

getEntry : (pos : Integer) -> (store : DataStore) ->
           Maybe (String, DataStore)
getEntry pos dataStore@(MkData schema' size' store') =
  case integerToFin pos size' of
    Nothing => Just ("Out of range\n", dataStore)
    Just id' => Just (display (index id' store') ++ "\n", dataStore)

getQuoted : List Char -> Maybe (String, String)
getQuoted ('"' :: xs) =
  case span (/= '"') xs of
  (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
  _ => Nothing
getQuoted _ = Nothing

parseAddPrefix : (schema' : Schema) -> String -> Maybe (SchemaType schema', String)
parseAddPrefix SString input = getQuoted $ unpack input
parseAddPrefix SInt input =
  case span isDigit input of
    ("", rest) => Nothing
    (num, rest) => Just (cast num, ltrim rest)
parseAddPrefix (leftSchema .+. rightSchema) input = do
  (leftRes, leftoverInput) <- parseAddPrefix leftSchema input
  (rightRes, endingInput) <- parseAddPrefix rightSchema leftoverInput
  pure ((leftRes, rightRes), endingInput)

parseAdd : (schema' : Schema) -> String -> Maybe (SchemaType schema')
parseAdd schema'' string = do
  (res, rest) <- parseAddPrefix schema'' string
  case rest of
    "" => pure res
    _ => Nothing

parseGet : String -> Maybe Integer
parseGet val = do
  case all isDigit (unpack val) of
    False => Nothing
    True => Just $ cast val

parseSchema : List String -> Maybe Schema
parseSchema ["String"] = Just SString
parseSchema ["Int"] = Just SInt
parseSchema ("String" :: xs) = map (SString .+.) $ parseSchema xs
parseSchema ("Int" :: xs) = map (SInt .+.) $ parseSchema xs
parseSchema _ = Nothing

parseCommand : (schema : Schema) -> String -> String -> Maybe (Command schema)
parseCommand schema' "schema" str = map SetSchema . parseSchema $ words str
parseCommand schema' "add" str = map Add $ parseAdd schema' str
parseCommand schema' "get" val = map Get $ parseGet val
parseCommand schema' "quit" _ = Just Quit
parseCommand schema' _ _ = Nothing

parse : (schema : Schema) -> String -> Maybe (Command schema)
parse schema' input =
  case span (/= ' ') input of
    (cmd, args) => parseCommand schema' cmd (ltrim args)

processInput
  : (dataStore : DataStore) -> String -> Maybe (String, DataStore)
processInput dataStore@(MkData schema' size' items') input =
  case parse schema' input of
    Nothing => Just ("Invalid command\n", dataStore)
    Just (SetSchema newSchema) =>
      Just ("updated schema and reset datastore\n", MkData newSchema _ [])
    Just (Add item) =>
      let newStore = addToStore (MkData schema' size' items') item
      in Just ("ID " ++ show (size dataStore) ++ "\n", newStore)
    Just (Get pos) => getEntry pos dataStore
    Just Quit => Nothing

main : IO ()
main = replWith (MkData SString _ []) "Command: " processInput
