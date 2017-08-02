
module Main

import Data.Vect

data Tree a
  = Empty
  | Node (Tree a) a (Tree a)

%name Tree tree, tree1

insertIntoTree : Ord a => a -> Tree a -> Tree a
insertIntoTree x Empty = Node Empty x Empty
insertIntoTree x (Node tree y tree1) =
  case compare x y of
    LT => Node (insertIntoTree x tree) y tree1
    EQ => Node tree y tree1
    GT => Node tree y (insertIntoTree x tree1)

listToTree : Ord a => List a -> Tree a
listToTree = foldr insertIntoTree Empty

treeToList : Tree a -> List a
treeToList Empty = []
treeToList (Node tree x tree1) =
  treeToList tree ++ [x] ++ treeToList tree1


data Expr : Type where
  Val : Int -> Expr
  Add : Expr -> Expr -> Expr
  Sub : Expr -> Expr -> Expr
  Mult : Expr -> Expr -> Expr

%name Expr expr, expr1, expr2

evaluate : Expr -> Int
evaluate (Val x) = x
evaluate (Add x y) = evaluate x + evaluate y
evaluate (Sub x y) = evaluate x - evaluate y
evaluate (Mult x y) = evaluate x * evaluate y

maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe x y = do
  lala <- x
  baba <- y
  pure $ max lala baba


indexOnFin : (xs : Vect n a) -> (fin : Fin n) -> a
indexOnFin (x :: xs) FZ = x
indexOnFin (_ :: xs) (FS fin) = indexOnFin xs fin

tryIndex : Integer -> Vect n a -> Maybe a
tryIndex {n} x xs =
  case integerToFin x n of
    Nothing => Nothing
    (Just fin) => Just $ indexOnFin xs fin

data PowerSource = Petrol | Pedal | Electric

data Vehicle : PowerSource -> Type where
     Bicycle : Vehicle Pedal
     Car : (fuel : Nat) -> Vehicle Petrol
     Bus : (fuel : Nat) -> Vehicle Petrol
     Unicycle : Vehicle Pedal
     Motorcycle : (fuel : Nat) -> Vehicle Petrol


wheels : Vehicle power -> Nat
wheels Bicycle = 2
wheels (Car fuel) = 4
wheels (Bus fuel) = 4
wheels Unicycle = 1
wheels (Motorcycle fuel) = 2

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 200
refuel (Motorcycle fuel) = Motorcycle 50
refuel Bicycle impossible
refuel Unicycle impossible


vectTake : (n : Nat) -> Vect (n + m) a -> Vect n a
vectTake Z vs = []
vectTake (S k) (x :: xs) = x :: vectTake k xs


sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries pos xs ys = tryIndex pos $ zipWith (+) xs ys
