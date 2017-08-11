
module Main

data ListLast : List a -> Type where
  Empty : ListLast []
  NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

total
describeHelper : Show a => {input : List a} -> (form : ListLast input) -> String
describeHelper Empty = "Empty list..."
describeHelper (NonEmpty xs x) = "Last element: " ++ show x

total
listLast : (input : List a) -> ListLast input
listLast [] = Empty
listLast (x :: xs) =
  case listLast xs of
    Empty => NonEmpty [] x
    NonEmpty newList las => NonEmpty (x :: newList) las

describeEnd : Show a => List a -> String
describeEnd xs = describeHelper $ listLast xs

describeListEnd : Show a => List a -> String
describeListEnd input with (listLast input)
  describeListEnd _ | Empty = "Empty List..."
  describeListEnd _ | (NonEmpty ys x) = "Last is " ++ show x

describeListEnd' : Show a => List a -> String
describeListEnd' input =
  case listLast input of
    Empty => "Empty list..."
    (NonEmpty ys x) => "Last is " ++ show x

myReverse : List a -> List a
myReverse xs with (listLast xs)
  myReverse _ | Empty = []
  myReverse _ | (NonEmpty ys x) = x :: myReverse ys

data SplitList : List a -> Type where
  SplitNone : SplitList []
  SplitOne : SplitList [x]
  SplitPair : (lefts : List a) -> (rights : List a) -> SplitList (lefts ++ rights)

total splitList : (input : List a) -> SplitList input
splitList input = go input input
  where
    go : List a -> (input : List a) -> SplitList input
    go _ [] = SplitNone
    go _ [_] = SplitOne
    go (_ :: _ :: counter) (item :: items) =
      case splitList items of
        SplitNone => SplitOne
        SplitOne {x} => SplitPair [item] [x]
        (SplitPair lefts rights) => SplitPair (item :: lefts) rights
    go _ rights = SplitPair [] rights

total splitList' : (input : List a) -> SplitList input
splitList' [] = SplitNone
splitList' [x] = SplitOne
splitList' (y :: ys) =
  case splitList' ys of
    SplitNone => SplitOne
    SplitOne {x} => SplitPair [y] [x]
    (SplitPair lefts rights) => ?hfesfa_4

total
merge : Ord a => List a -> List a -> List a
merge [] lefts = lefts
merge rights [] = rights
merge (x :: xs) (y :: ys) =
  if x < y
    then x :: Main.merge xs (y :: ys)
    else y :: Main.merge (x :: xs) ys

mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList xs)
  mergeSort [] | SplitNone = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (_ ++ _) | (SplitPair lefts rights) =
    Main.merge (mergeSort lefts) (mergeSort rights)

