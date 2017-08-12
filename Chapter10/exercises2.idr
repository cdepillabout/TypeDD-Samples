
module Main

import Data.List.Views
import Data.Nat.Views
import Data.Vect
import Data.Vect.Views

total
merge : Ord a => (vect1 : Vect n a) -> (vect2 : Vect m a) -> Vect (n + m) a
merge [] ys = ys
merge {n} xs [] = rewrite plusZeroRightNeutral n in xs
merge {n = S n'} {m = S m'} (x :: xs) (y :: ys) =
  if x <= y
    then
      let rest' = Main.merge xs (y :: ys) in
      let everything' = x :: rest' in
      everything'
    else
      let rest = Main.merge {n = S n'} {m = m'} (x :: xs) ys in
      let everything = y :: rest in
      -- Before rewrite, the type of everything is:
      --     everything : Vect (S (S (n' + m'))) a
      -- I need to produce a:
      --     Vect (S (n' + (S m'))) a
      rewrite sym $ plusSuccRightSucc n' m' in
      -- Type of plusSuccRightSucc is:
      --     plusSuccRightSucc n' m' : S (n' + m') = n' + (S m')
      -- Type of sym plusSuccRightSucc is:
      --     sym $ plusSuccRightSucc n' m' : n' + (S m') = S (n' + m')
      -- After rewriting, I need to produce a:
      --     Vect (S (S (n' + m'))) a
      everything

total
mergeSort : Ord a => Vect n a -> Vect n a
mergeSort xs with (splitRec xs)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (ys ++ zs) | (SplitRecPair lrec rrec) =
    Main.merge (mergeSort ys | lrec) (mergeSort zs | rrec)


total
toBinary : (n : Nat) -> String
toBinary n with (halfRec n)
  toBinary Z | HalfRecZ = "0"
  toBinary (Z + Z) | (HalfRecEven rec) = "0"
  toBinary ((S n) + (S n)) | (HalfRecEven rec) = toBinary (S n) | rec ++ "0"
  toBinary (S (Z + Z)) | (HalfRecOdd rec) = "1"
  toBinary (S (S n + S n)) | (HalfRecOdd rec) = toBinary (S n) | rec ++ "1"

palindrome : String -> Bool
palindrome str = go $ unpack str
  where
    go : List Char -> Bool
    go xs with (vList xs)
      go [] | VNil = True
      go [_] | VOne = True
      go (x :: (ys ++ [y])) | (VCons rec) = if x == y then go ys | rec else False
