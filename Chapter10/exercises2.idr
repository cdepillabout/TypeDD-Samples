
module Main

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


