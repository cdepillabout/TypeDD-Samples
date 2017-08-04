
module Main


data Shape
  = Triangle Double Double
  | Rectangle Double Double
  | Circle Double

Eq Shape where
  (==) (Triangle x z) (Triangle y w) = x == z && y == w
  (==) (Rectangle x z) (Rectangle y w) = x == z && y == w
  (==) (Circle x) (Circle y) = x == y
  (==) (Triangle _ _) _ = False
  (==) (Rectangle x z) _ = False
  (==) (Circle x) _ = False


data Vect : Nat -> Type -> Type where
  Nil : Vect 0 a
  (::) : a -> Vect n a -> Vect (S n) a

Eq a => Eq (Vect n a) where
  (==) [] [] = True
  (==) (x :: z) (y :: w) = x == y && z == w

Foldable (Vect n) where
  foldr _ init [] = init
  foldr func init (x :: y) = func x $ foldr func init y

data FixT : (f : Type -> Type) -> Type where
  FixC : f (FixT f) -> FixT f

data ExprF num x
  = Val num
  | Add x x
  | Sub x x
  | Mul x x
  | Div x x
  | Abs x


Functor (ExprF a) where
  map func (Val x) = Val x
  map func (Add x y) = Add (func x) (func y)
  map func (Sub x y) = Sub (func x) (func y)
  map func (Mul x y) = Mul (func x) (func y)
  map func (Div x y) = Div (func x) (func y)
  map func (Abs x) = Abs (func x)

Expr : Type -> Type
Expr = FixT . ExprF

project : FixT f -> f (FixT f)
project (FixC x) = x

cata : Functor f => (f a -> a) -> FixT f -> a
cata func myfix = func (map (cata func) (project myfix))

evalF : (Neg num, Integral num) => ExprF num num -> num
evalF (Val x) = x
evalF (Add x y) = x + y
evalF (Sub x y) = x - y
evalF (Mul x y) = x * y
evalF (Div x y) = div x y
evalF (Abs x) = abs x

eval : (Neg num, Integral num) => Expr num -> num
eval = cata evalF

total add : Expr num -> Expr num -> Expr num
add x y = FixC (Add x y)

total mul : Expr num -> Expr num -> Expr num
mul x y = FixC (Mul x y)

total toVal : num -> Expr num
toVal x = FixC (Val x)

Num num => Num (Expr num) where
  (+) = add
  (*) = mul
  fromInteger = toVal . fromInteger

-- Neg ty => Neg (Expr ty) where
--   negate = Sub 0
--   (-) = Sub
--   abs = Abs

-- test : Expr Int
-- test = 3 + 4 * 6

-- Functor Expr where
--   map func (Val x) = Val $ func x
--   map func (Add x y) = Add (map func x) (map func y)
--   map func (Sub x y) = Sub (map func x) (map func y)
--   map func (Mul x y) = Mul (map func x) (map func y)
--   map func (Div x y) = Div (map func x) (map func y)
--   map func (Abs x) = Abs $ map func x
