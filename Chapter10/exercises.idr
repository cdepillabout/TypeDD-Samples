
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



data SnocList : List a -> Type where
  SLEmpty : SnocList []
  Snoc : (rec : SnocList xs) -> SnocList (xs ++ [x])

-- total
-- snocList : (ls : List a) -> SnocList ls
-- snocList [] = SLEmpty
-- snocList (l :: ls) with (snocList ls)
--   snocList (l :: []) | SLEmpty = Snoc SLEmpty
--   snocList (l :: (ms ++ [m])) | ava@(Snoc rec {x = m} {xs = ms}) =
--     let papa = Snoc ava
--     in ?hfeafes

total
snocListHelper
  : {a : Type} ->
    (snoc : SnocList input) ->
    (rest : List a) ->
    SnocList (input ++ rest)
snocListHelper {input = input} snoc [] =
  -- the type I need to return is SnocList (input ++ [])
  let _ = the (SnocList input) snoc in
  -- appendNilRightNeutral : (l : List a) -> l ++ [] = l
  let _ = the (input ++ [] = input) (appendNilRightNeutral input) in
  rewrite appendNilRightNeutral input in
  -- after the rewrite, type I need to return is SnocList input
  snoc
snocListHelper {input = input} snoc (x :: xs) =
  -- the type I need to return is SnocList (input ++ (x :: xs))
  let rec = snocListHelper (Snoc snoc {x}) xs in
  let _ = the (SnocList ((input ++ [x]) ++ xs)) rec in
  -- appendAssociative
  --   : (l : List a) -> (c : List a) -> (r : List a) -> l ++ (c ++ r) = (l ++ c) ++ r
  let rewriteRule = appendAssociative input [x] xs in
  let _ = the (input ++ ([x] ++ xs) = (input ++ [x]) ++ xs) rewriteRule in
  let _ = the (input ++ (x :: xs) = (input ++ [x]) ++ xs) rewriteRule in
  rewrite rewriteRule in
  -- after the rewrite, the type I need to return is SnocList ((input ++ [x]) ++ xs)
  rec

data Proxy : a -> Type where
  MkProxy : Proxy a

testtest : (input : List b) -> Proxy input
testtest [] = MkProxy {a = []}
testtest (x :: xs) = MkProxy {a = ([x] ++ xs)}

total
snocList : (xs : List a) -> SnocList xs
snocList xs = snocListHelper SLEmpty xs

total
reverseSnoc : {xs : List a} -> SnocList xs -> List a
reverseSnoc SLEmpty = []
reverseSnoc (Snoc rec {x}) = x :: reverseSnoc rec

total
myReverseHelper : (xs : List a) -> SnocList xs -> List a
myReverseHelper [] SLEmpty = []
myReverseHelper (ys ++ [x]) (Snoc rec) = x :: myReverseHelper ys rec

myReverse' : List a -> List a
myReverse' xs = myReverseHelper xs (snocList xs)
