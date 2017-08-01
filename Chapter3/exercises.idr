
module Main

import Data.Vect

main : IO ()
main = putStrLn "hello"

allLengths : List String -> List Nat
allLengths [] = []
allLengths (word :: words) = length word :: allLengths words

xor : Bool -> Bool -> Bool
xor False y = y
xor True y = not y

isEven : Nat -> Bool
isEven Z = True
isEven (S k) = not $ isEven k

mutual
  isEven' : Nat -> Bool
  isEven' Z = True
  isEven' (S k) = isOdd k

  isOdd : Nat -> Bool
  isOdd Z = False
  isOdd (S k) = isEven' k


total allLengths' : Vect n String -> Vect n Nat
allLengths' [] = []
allLengths' (x :: xs) = length x :: allLengths' xs

insert : Ord a => (x : a) -> (sorted : Vect len a) -> Vect (S len) a
insert x [] = [x]
insert x (y :: xs) =
  case x < y of
    False => y :: insert x xs
    True => x :: y :: xs

total insSort : Ord a => Vect n a -> Vect n a
insSort [] = []
insSort (x :: xs) =
  let sorted = insSort xs
  in insert x sorted

map' : (a -> b) -> Vect n a -> Vect n b
map' f [] = []
map' f (x :: xs) = f x :: map' f xs

Matrix : Nat -> Nat -> Type -> Type
Matrix n m a = Vect n (Vect m a)

-- createEmtpy : Matrix n 0 a
-- createEmtpy = replicate n []

-- takeFirsts : Matrix m (S n) a -> (Vect m a, Matrix m n a)
-- takeFirsts [] = ([], [])
-- takeFirsts xs@(x :: xs') = (map head xs, map tail xs)

-- transposeMat : Matrix m n a -> Matrix n m a
-- transposeMat [] = createEmtpy
-- transposeMat ([] :: xs) = []
-- transposeMat ever@((x :: xs) :: ys) =
--   let (firstRow, rest) = takeFirsts ever
--   in firstRow :: transposeMat rest


createEmpties : Vect n (Vect 0 a)
createEmpties = replicate _ []

total transposeHelper
  : (x : Vect n a) -> (xs : Matrix n len a) -> Vect n (Vect (S len) a)
transposeHelper [] [] = []
transposeHelper (x :: xs) (y :: ys) = (x :: y) :: transposeHelper xs ys

total transposeMat : Matrix m n a -> Matrix n m a
transposeMat [] = createEmpties
transposeMat (x :: xs) =
  let xsTrans = transposeMat xs
  in transposeHelper x xsTrans

total transposeMat' : Matrix m n a -> Matrix n m a
transposeMat' [] = createEmpties
transposeMat' (x :: xs) =
  let xsTrans = transposeMat xs
  in zipWith (::) x xsTrans

addMatrix : Num a => Vect n (Vect m a) -> Vect n (Vect m a) -> Vect n (Vect m a)
-- addMatrix [] [] = []
-- addMatrix (x :: xs) (y :: ys) = zipWith (+) x y :: addMatrix xs ys
-- addMatrix [] [] = []
addMatrix = zipWith (zipWith (+))

total doRow : Num a => (xs : Vect m a) -> (yss : Matrix p m a) -> Vect p a
doRow xs = map (\ys => sum $ zipWith (*) xs ys)

total multMatrix : Num a => Matrix n m a -> Matrix m p a -> Matrix n p a
multMatrix xss yss =
  let transYss = transposeMat yss
  in map (\xs => doRow xs transYss) xss
