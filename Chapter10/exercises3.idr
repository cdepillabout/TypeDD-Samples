
module Main

import Data.Vect

private
data Proxy : {x : Type} -> (a : x) -> Type where
MkProxy : Proxy a

private
data Proxy2 a = MkProxy2

private
data Color = Red

private
help : Proxy Red

private
lala : (color : Color) -> Proxy color
lala Red = help

infixr 5 .+.

public export
data Schema = SString | SInt | (.+.) Schema Schema

public export
SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

public export
record DataStore (schema : Schema) where
  constructor MkData
  size : Nat
  items : Vect size (SchemaType schema)

export
empty : DataStore schema
empty = MkData _ []

export
addToStore : (value : SchemaType schema) -> (store : DataStore schema) -> DataStore schema
addToStore value (MkData _ items) = MkData _ (value :: items)

public export
data StoreView : DataStore schema -> Type where
  SNil : StoreView empty
  SAdd : (rec : StoreView store) -> StoreView (addToStore value store)

private
storeViewHelper : (items : Vect size (SchemaType schema)) -> StoreView (MkData size items)
storeViewHelper [] = SNil
storeViewHelper (x :: xs) = SAdd $ storeViewHelper xs

export
storeView : (store : DataStore schema) -> StoreView store
storeView (MkData _ items) = storeViewHelper items

export
storeView' : (store : DataStore schema) -> StoreView (MkData (size store) (items store))
storeView' (MkData _ items) = storeViewHelper items

lalaeq : (store : DataStore schema) -> (storeView store = storeView' store)
lalaeq (MkData size items) = Refl

testStore : DataStore (SString .+. SString .+. SInt)
testStore =
  addToStore ("Mercury", "Mariner 10", 1974) $
  addToStore ("Venus", "Venera", 1961) $
  addToStore ("Uranus", "Voyager 2", 1986) $
  addToStore ("Pluto", "New Horizons", 2015) $
  empty

total
listItems : DataStore schema -> List (SchemaType schema)
listItems x with (storeView x)
  listItems empty | SNil = []
  listItems (addToStore value store) | (SAdd rec) = value :: listItems store | rec

total
filterKeys : (test : SchemaType val_schema -> Bool) -> DataStore (SString .+. val_schema) -> List String
filterKeys test x with (storeView x)
  filterKeys test empty | SNil = []
  filterKeys test (addToStore (lala,  rest) store) | (SAdd rec) =
    (if test rest then (lala ::) else id) $ filterKeys test store | rec

getValues : (store : DataStore (SString .+. schema_val)) -> List (SchemaType schema_val)
getValues store with (storeView store)
  getValues store | SNil = []
  getValues (addToStore (key, val) s) | (SAdd rec) = val :: getValues s | rec



