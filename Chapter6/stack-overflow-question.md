
I'm currently going through the [Type-Driven Development with Idris](https://www.manning.com/books/type-driven-development-with-idris) book.

I have two questions relating to the design of the example data store in Chapter 6.  The data store is a command line application that allows the user to set what kind of data is stored in it, and then add new data.

Here are the relevant parts of the code (simplified slightly).  You can see the [full code]() on Github:

    module Main
    
    import Data.Vect
    
    infixr 4 .+.
    
    -- This datatype is to define what sorts of data can be contained in the data store.
    data Schema
      = SString
      | SInt
      | (.+.) Schema Schema
    
    -- This is a type-level function that translates a Schema to an actual type.
    SchemaType : Schema -> Type
    SchemaType SString = String
    SchemaType SInt = Int
    SchemaType (x .+. y) = (SchemaType x, SchemaType y)
    
    -- This is the data store.  It can potentially be storing any sort of schema.
    record DataStore where
           constructor MkData
           schema : Schema
           size : Nat
           items : Vect size (SchemaType schema)
    
    -- This adds new data to the datastore, making sure that the new data is
    -- the same type that the DataStore holds.
    addToStore
      : (dataStore : DataStore) -> SchemaType (schema dataStore) -> DataStore
    addToStore (MkData schema' size' store') newitem =
      MkData schema' _ (addToData store')
      where
        addToData
          : Vect size' (SchemaType schema') -> Vect (size' + 1) (SchemaType schema')
        addToData xs = xs ++ [newitem]
    
    -- These are commands the user can use on the command line.  They are able
    -- to change the schema, and add new data.
    data Command : Schema -> Type where
      SetSchema : (newSchema : Schema) -> Command schema
      Add : SchemaType schema -> Command schema
    
    -- Given a Schema, this parses input from the user into a Command.
    parse : (schema : Schema) -> String -> Maybe (Command schema)
    
    -- This is the main workhorse of the application.  It parses user
    -- input, turns it into a command, then evaluates the command and 
    -- returns an updated DataStore.
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
    
    -- This kicks off processInput with an empty datastore and a simple Schema
    -- of SString.
    main : IO ()
    main = replWith (MkData SString _ []) "Command: " processInput


This makes sense and is easy to use, but one thing bugged me about the design.  *Why does the `DataStore` contain a `Schema` instead of being indexed by one*?

Because the `DataStore` is not indexed by a `Schema`, we could have written an incorrect `addToStore` function like this:

    addToStore
      : (dataStore : DataStore) -> SchemaType (schema dataStore) -> DataStore
    addToStore _ newitem =
      MkData SInt _ []

Here is what I would imagine more type safe code would look like.  You can see the [full code]() on Github:

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
    
    record DataStore (schema : Schema) where
           constructor MkData
           size : Nat
           items : Vect size (SchemaType schema)
    
    addToStore
      : (dataStore : DataStore schema) ->
        SchemaType schema ->
        DataStore schema
    addToStore {schema} (MkData size' store') newitem =
      MkData _ (addToData store')
      where
        addToData
          : Vect size' (SchemaType schema) -> Vect (size' + 1) (SchemaType schema)
        addToData xs = xs ++ [newitem]

    data Command : Schema -> Type where
      SetSchema : (newSchema : Schema) -> Command schema
      Add : SchemaType schema -> Command schema
    
    parse : (schema : Schema) -> String -> Maybe (Command schema)
    
    processInput
      : (schema : Schema ** DataStore schema) ->
        String ->
        Maybe (String, (newschema ** DataStore newschema))
    processInput (schema ** (MkData size' items')) input =
      case parse schema input of
        Nothing => Just ("Invalid command\n", (_ ** MkData size' items'))
        Just (SetSchema newSchema) =>
          Just ("updated schema and reset datastore\n", (newSchema ** MkData _ []))
        Just (Add item) =>
          let newStore = addToStore (MkData size' items') item
              msg = "ID " ++ show (size newStore) ++ "\n"
          in Just (msg, (schema ** newStore))
    
    main : IO ()
    main = replWith (SString ** MkData _ []) "Command: " processInput
    
-----------------------------------------------

Here are my two questions:

1.  Why didn't the book use the more type-safe version of the `DataStore` type (the one indexed by the `Schema`)?  Is there something that is gained by using the less type-safe version (the one that just contains a `Schema`)?

2.  What is the theoretical difference of a type being indexed by another type vs containing another type?  Does this difference change depending on what language you are working on?
    
    For instance, I imagine there might not be a big difference in Idris, but there is quite a big difference in Haskell. (Right...?)
    
    I just started playing around with Idris (and I am not particularly well-versed with the use of singletons or GADTs in Haskell), so I'm having a hard time wrapping my head around this.  If you could point me to any papers talking about this, I'd be very interested.
