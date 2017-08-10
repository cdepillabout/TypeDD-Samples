
module Main


infixr 7 <=!

data (<=!) : {a : Type} -> (x : a) -> (y : a) -> Type where
  IsLessThanOrEq : Ord a => {x : a} -> {y: a} -> (prf : ((x <= y) = True)) -> x <=! y

example1 : 3 <=! 4
example1 = IsLessThanOrEq Refl

example2 : 0 <=! 0
example2 = IsLessThanOrEq Refl

example3 : 5 <=! 1 -> Void
example3 (IsLessThanOrEq Refl) impossible

-- isLessThanOrEq : Ord a => {a : Type} -> (x : a) -> (y : a) -> (x : a ** y : a ** Dec (x <=! y))
-- isLessThanOrEq x y = (x ** y ** 
--     case x <= y of
--       False => ?hfefaesf -- No $ \prf =>
--         -- case prf of
--         --   (IsLessThanOrEq {x=x} {y=y} prf2) => ?hf0ehsafesfa_1
--       -- True => Yes (IsLessThanOrEq ?hfe0afesaf_3)
--   )
 
 
