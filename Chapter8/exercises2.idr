
module Main

data Vect : Nat -> a -> Type where
  Nil : Vect 0 a
  (::) : a -> Vect n a -> Vect (S n) a

(++) : Vect m a -> Vect n a -> Vect (m + n) a
(++) [] ys = ys
(++) (x :: xs) ys = x :: (xs ++ ys)

reverseVect : {n : Nat} -> Vect n a -> Vect n a
reverseVect {n = Z} [] = []
reverseVect {n = S n} (x :: xs) =
  rewrite plusCommutative 1 n
  in reverseVect xs ++ [x]

reverseNilIsNil : reverseVect [] = []
reverseNilIsNil = Refl

reverseVectAppend : {n : Nat} -> (x : a) -> (xs : Vect n a) -> reverseVect (reverseVect xs ++ [x]) = (x :: xs)
reverseVectAppend {n = Z} x [] = Refl
reverseVectAppend {n = (S k)} x (y :: ys) =
  let ind = reverseVectAppend y ys
  in rewrite plusCommutative 1 k
  -- in rewrite ind
  in ?ajaha

reverseReverseIsId : {n : Nat} -> (vect : Vect n a) -> reverseVect (reverseVect vect) = vect
reverseReverseIsId {n = Z} [] = Refl
reverseReverseIsId {n = (S k)} (x :: xs) = 
  let lala = reverseVectAppend x xs
  in ?haha

