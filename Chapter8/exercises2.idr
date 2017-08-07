
module Main

data Vect : Nat -> a -> Type where
  Nil : Vect 0 a
  (::) : a -> Vect n a -> Vect (S n) a

(++) : Vect m a -> Vect n a -> Vect (m + n) a
(++) [] ys = ys
(++) (x :: xs) ys = x :: (xs ++ ys)

reverse_Proof : {n1 : Nat} -> {n2 : Nat} -> Vect ((S (S n1)) + n2) a1 -> Vect (S (plus n1 (S n2))) a1
reverse_Proof {n1 = n1} {n2 = n2} xs =
  rewrite sym (plusSuccRightSucc n1 n2)
  in xs

myReverse : {a : Type} -> Vect n a -> Vect n a
myReverse xs = reverse' [] xs
  where
    reverse' : {a : Type} -> {n : Nat} -> Vect n a -> Vect m a -> Vect (n + m) a
    reverse' {n = Z} acc [] = acc
    reverse' {n = S n} acc (x :: xs) = reverse_Proof (reverse' (x :: acc) xs)

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
  in ?jajajaj


myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = rewrite plusZeroRightNeutral m in Refl
myPlusCommutes (S k) m =
  rewrite sym (plusSuccRightSucc m k) in
  let ind = myPlusCommutes k m in
  rewrite ind in
  Refl

valueNotSucc : (x : Nat) -> x = S x -> Void
valueNotSucc _ Refl impossible

data MyDec : (prop : Type) -> Type where
  MyYes : prop -> MyDec prop
  MyNo : (prop -> Void) -> MyDec prop

checkNatEq3 : (f : (k = j) -> Void) -> (S k = S j) -> Void
checkNatEq3 f Refl = f Refl

checkNatEq : (n : Nat) -> (m : Nat) -> MyDec (n = m)
checkNatEq Z Z = MyYes Refl
checkNatEq Z (S k) = MyNo absurd
checkNatEq (S k) Z = MyNo $ absurd . sym
checkNatEq (S k) (S j) =
  case checkNatEq k j of
    (MyYes x) => MyYes $ cong x
    (MyNo f) => MyNo $ \Refl => f Refl

interface MyDecEq ty where
  total myDecEq : (val1 : ty) -> (val2 : ty) -> MyDec (val1 = val2)

total headUnequal
  : {xs : Vect n a} -> ((x = y) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
headUnequal p Refl = p Refl

total MyDecEq a => MyDecEq (Vect n a) where
  myDecEq [] [] = MyYes Refl
  myDecEq (x :: xs) (y :: ys) =
    case (myDecEq x y, myDecEq xs ys) of
      (MyYes Refl, MyYes Refl) => MyYes Refl
      (_, MyNo contra) => MyNo $ \Refl => contra Refl
      (MyNo contra, _) => MyNo $ headUnequal contra
