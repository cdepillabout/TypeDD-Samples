
module Main

import Data.List.Views

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



data TakeN : List a -> Type where
  Fewer : TakeN xs
  Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)

total takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z xs = Exact []
takeN (S k) [] = Fewer
takeN (S k) (x :: xs) with (takeN k xs)
  takeN (S k) (x :: xs) | Fewer = Fewer
  takeN (S k) (x :: (n_xs ++ rest)) | (Exact n_xs) = Exact (x :: n_xs)

groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n ([] ++ rest) | (Exact []) = groupByN n rest
  groupByN n ((item :: items) ++ rest) | (Exact (item :: items)) = (item :: items) :: groupByN n rest

halves : List a -> (List a, List a)
halves xs =
  let len = length xs in
  case len of
    Z => ([], [])
    (S k) =>
      let half = div (S k) 2 in
      case takeN half xs of
        Fewer {xs} => ([], xs)
        (Exact n_xs {rest}) => (n_xs, rest)

halves' : List a -> (List a, List a)
halves' xs with (takeN (length xs `div` 2) xs)
  halves' xs | Fewer = ([], xs)
  halves' (n_xs ++ rest) | (Exact n_xs) = (n_xs, rest)

-- halves'' : List a -> (List a, List a)
-- halves'' xs with (length xs)
--   halves'' _ | Z = ([], [])
--   halves'' xs | (S k) with (takeN (S k `div 2) xs)
--     halves'' xs | (S k) | with_pat = ?k_rhs



data MySnocList : List a -> Type where
  SLEmpty : MySnocList []
  Snoc : (rec : MySnocList xs) -> MySnocList (xs ++ [x])

total
snocListHelper
  : {a : Type} ->
    (snoc : MySnocList input) ->
    (rest : List a) ->
    MySnocList (input ++ rest)
snocListHelper {input = input} snoc [] =
  -- the type I need to return is MySnocList (input ++ [])
  let _ = the (MySnocList input) snoc in
  -- appendNilRightNeutral : (l : List a) -> l ++ [] = l
  let _ = the (input ++ [] = input) (appendNilRightNeutral input) in
  rewrite appendNilRightNeutral input in
  -- after the rewrite, type I need to return is MySnocList input
  snoc
snocListHelper {input = input} snoc (x :: xs) =
  -- the type I need to return is MySnocList (input ++ (x :: xs))
  let rec = snocListHelper (Snoc snoc {x}) xs in
  let _ = the (MySnocList ((input ++ [x]) ++ xs)) rec in
  -- appendAssociative
  --   : (l : List a) -> (c : List a) -> (r : List a) -> l ++ (c ++ r) = (l ++ c) ++ r
  let rewriteRule = appendAssociative input [x] xs in
  let _ = the (input ++ ([x] ++ xs) = (input ++ [x]) ++ xs) rewriteRule in
  let _ = the (input ++ (x :: xs) = (input ++ [x]) ++ xs) rewriteRule in
  rewrite rewriteRule in
  -- after the rewrite, the type I need to return is MySnocList ((input ++ [x]) ++ xs)
  rec

data Proxy : a -> Type where
  MkProxy : Proxy a

testtest : (input : List b) -> Proxy input
testtest [] = MkProxy {a = []}
testtest (x :: xs) = MkProxy {a = ([x] ++ xs)}

total
mySnocList : (xs : List a) -> MySnocList xs
mySnocList xs = snocListHelper SLEmpty xs

total
reverseSnoc : {xs : List a} -> MySnocList xs -> List a
reverseSnoc SLEmpty = []
reverseSnoc (Snoc rec {x}) = x :: reverseSnoc rec

total
myReverseHelper : (xs : List a) -> MySnocList xs -> List a
myReverseHelper [] SLEmpty = []
myReverseHelper (ys ++ [x]) (Snoc rec) = x :: myReverseHelper ys rec

myReverse' : List a -> List a
myReverse' xs = myReverseHelper xs (Main.mySnocList xs)

snocListHelper' : (MySnocList input) -> (rest : List a) -> MySnocList (input ++ rest)
snocListHelper' {input} snoc [] = rewrite appendNilRightNeutral input in snoc
snocListHelper' {input} snoc (x :: xs) =
  let newSnoc = Snoc snoc {x} in
  let rec = snocListHelper' newSnoc xs in
  let rewriteRule = appendAssociative input [x] xs in
  -- need to return a value of type MySnocList (input ++ x :: xs)
  rewrite rewriteRule in
  -- now, need to return a value of type MySnocList ((input ++ [x]) ++ xs)
  rec

total
myReverse'' : List a -> List a
myReverse'' xs with (Main.mySnocList xs)
  myReverse'' [] | SLEmpty = []
  myReverse'' (ys ++ [x]) | (Snoc rec) = x :: (myReverse'' ys | rec)

total
myfoldl : (acc -> Int -> acc) -> acc -> List Int  -> acc
myfoldl f acc xs = foldr (\elem, ff, acc' => ff $ f acc' elem) id xs acc

total
isSuffix : Eq a => List a -> List a -> Bool
isSuffix xs ys with (Main.mySnocList xs)
  isSuffix [] ys | SLEmpty = True
  isSuffix (zs ++ [x]) ys | (Snoc rec) with (Main.mySnocList ys)
    isSuffix (zs ++ [x]) [] | (Snoc rec) | SLEmpty = False
    isSuffix (zs ++ [x]) (xs ++ [y]) | (Snoc rec) | (Snoc z) =
      x == y && isSuffix zs xs | rec | z


total
mergeSort' : Ord a => List a -> List a
mergeSort' xs with (splitRec xs)
  mergeSort' [] | SplitRecNil = []
  mergeSort' [x] | SplitRecOne = [x]
  mergeSort' (lefts ++ rights) | (SplitRecPair lrec rrec) =
    Main.merge (mergeSort' lefts | lrec) (mergeSort' rights | rrec)


equalSuffixHelper : Eq a => (accum : List a) -> (list1 : List a) -> (list2: List a) -> List a
equalSuffixHelper accum list1 list2 with (snocList list1)
  equalSuffixHelper accum [] _ | Empty = accum
  equalSuffixHelper accum (xs ++ [x]) list2 | (Snoc rec) with (snocList list2)
    equalSuffixHelper accum (xs ++ [x]) [] | (Snoc rec) | Empty = accum
    equalSuffixHelper accum (xs ++ [x]) (ys ++ [y]) | (Snoc rec) | (Snoc z) =
      if x == y
        then equalSuffixHelper (x :: accum) xs ys | rec | z
        else accum

equalSuffix : Eq a => List a -> List a -> List a
equalSuffix xs ys = equalSuffixHelper [] xs ys

