
module Main

import Data.Vect

%default total

data StackCmd : Type -> Nat -> Nat -> Type where
  Push : Integer -> StackCmd () height (S height)
  Pop : StackCmd Integer (S height) height
  Top : StackCmd Integer (S height) (S height)

  GetStr : StackCmd String height height
  PutStr : String -> StackCmd () height height

  Pure : ty -> StackCmd ty height height
  (>>=) : StackCmd a x y -> (a -> StackCmd b y z) -> StackCmd b x z

testAdd : StackCmd Integer 0 0
testAdd = do
  Push 10
  Push 20
  val1 <- Pop
  val2 <- Pop
  Pure  (val1 + val2)

runStack
  : (stk : Vect inHeight Integer) ->
    StackCmd ty inHeight outHeight ->
    IO (ty, Vect outHeight Integer)
runStack stk (Push x) = pure ((), x :: stk)
runStack (x :: xs) Pop = pure (x, xs)
runStack (x :: xs) Top = pure (x, x :: xs)
runStack stk GetStr = do
  lin <- getLine
  pure (lin, stk)
runStack stk (PutStr str) = do
  putStr str
  pure ((), stk)
runStack stk (Pure x) = pure (x, stk)
runStack stk (x >>= f) = do
  (res, resVect) <- runStack stk x
  runStack resVect $ f res

data StackIO : Nat -> Type where
  Do : StackCmd a x y -> (a -> Inf (StackIO y)) -> StackIO x

namespace StackDo
  (>>=)
    : StackCmd a x y ->
      (a -> Inf (StackIO y)) ->
      StackIO x
  (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

run
  : Fuel ->
    Vect height Integer ->
    StackIO height ->
    IO ()
run (More fuel) stk (Do c f) = do
  (res, newStk) <- runStack stk c
  run fuel newStk $ f res
run Dry stk p = pure ()

data StkInput
  = Number Integer
  | Add
  | Subtract
  | Multiply
  | Negate
  | Discard

strToInput : String -> Maybe StkInput
strToInput "" = Nothing
strToInput "add" = Just Add
strToInput "subtract" = Just Subtract
strToInput "multiply" = Just Multiply
strToInput "negate" = Just Negate
strToInput "discard" = Just Discard
strToInput x =
  if all isDigit (unpack x)
    then Just . Number $ cast x
    else Nothing

mutual
  tryDef2 : (Integer -> Integer -> Integer) -> StackIO height
  tryDef2 f {height = (S (S k))} = do
    val1 <- Pop
    val2 <- Pop
    let res = f val1 val2
    Push res
    PutStr $ "Took " ++ show val1 ++ "off stack.\n"
    PutStr $ "Took " ++ show val2 ++ "off stack.\n"
    PutStr $ "Added " ++ show res ++ "to stack.\n"
    stackCalc
  tryDef2 _ {height = _} = do
    PutStr "Error: Not enough items on stack.\n"
    stackCalc

  tryDef1 : (Integer -> Integer) -> StackIO height
  tryDef1 f {height = (S k)} = do
    val1 <- Pop
    let res = f val1
    Push res
    PutStr $ "Took " ++ show val1 ++ "off stack.\n"
    PutStr $ "Added " ++ show res ++ "to stack.\n"
    stackCalc
  tryDef1 _ {height = _} = do
    PutStr "Error: Not enough items on stack.\n"
    stackCalc

  tryDis : StackIO height
  tryDis {height = (S k)} = do
    val1 <- Pop
    PutStr $ "Took " ++ show val1 ++ "off stack.\n"
    stackCalc
  tryDis {height = _} = do
    PutStr "Error: Not enough items on stack.\n"
    stackCalc

  stackCalc : StackIO height
  stackCalc = do
    PutStr "> "
    input <- GetStr
    case strToInput input of
      Nothing => do
        PutStr "Invalid input\n"
        stackCalc
      Just (Number x) => do
        Push x
        stackCalc
      Just Add => tryDef2 (+)
      Just Subtract => tryDef2 (-)
      Just Multiply => tryDef2 (*)
      Just Negate => tryDef1 (0 -)
      Just Discard => tryDis

partial
main : IO ()
main = run forever [] stackCalc
