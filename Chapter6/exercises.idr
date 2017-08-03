
module Main

StringOrInt : Bool -> Type
StringOrInt False = String
StringOrInt True = Int

getStringOrInt : (isInt : Bool) -> StringOrInt isInt
getStringOrInt False = "ninety-four"
getStringOrInt True = 94

valToString : (isInt : Bool) -> StringOrInt isInt -> String
valToString False x = trim x
valToString True x = cast x

valToString' : (isInt : Bool) -> (case isInt of
                                       False => String
                                       True => Int) -> String
valToString' False x = trim x
valToString' True x = cast x

AdderType : Nat -> Type
AdderType Z = Integer
AdderType (S k) = Integer -> AdderType k

adder : (numargs : Nat) -> (accum : Integer) -> AdderType numargs
adder Z accum = accum
adder (S k) accum = \int => adder k (int + accum)

-- adder' : (numargs : Nat) -> AdderType numargs
-- adder' Z = 0
-- adder' (S k) = \int => (adder' k) + int

data Format
  = Number Format
  | Str Format
  | Character Format
  | Float Format
  | Lit String Format
  | End

PrintfType : Format -> Type
PrintfType (Number x) = Int -> PrintfType x
PrintfType (Str x) = String -> PrintfType x
PrintfType (Character x) = Char -> PrintfType x
PrintfType (Float x) = Double -> PrintfType x
PrintfType (Lit x y) = PrintfType y
PrintfType End = String

printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt (Number x) acc = \int => printfFmt x (acc ++ cast int)
printfFmt (Str x) acc = \str => printfFmt x (acc ++ str)
printfFmt (Character x) acc = \c => printfFmt x (acc ++ strCons c "")
printfFmt (Float x) acc = \d => printfFmt x (acc ++ cast d)
printfFmt (Lit x y) acc = printfFmt y (acc ++ x)
printfFmt End acc = acc

toFormat : (str : String) -> Format
toFormat str = toFormat' $ unpack str
  where
    toFormat' : List Char -> Format
    toFormat' [] = End
    toFormat' ('%' :: 'd' :: chars) = Number $ toFormat' chars
    toFormat' ('%' :: 's' :: chars) = Str $ toFormat' chars
    toFormat' ('%' :: 'c' :: chars) = Character $ toFormat' chars
    toFormat' ('%' :: 'f' :: chars) = Float $ toFormat' chars
    toFormat' (char :: chars) = Lit (pack [char]) $ toFormat' chars

printf : (str : String) -> PrintfType (toFormat str)
printf str = printfFmt _ ""

printfTest : String
printfTest = printf "hello %c and %f and %d and %s" 'c' 1.1 100 "hello"

TupleVect : Nat -> Type -> Type
TupleVect Z x = ()
TupleVect (S k) x = (x, TupleVect k x)

myTup : TupleVect 4 String
myTup = ("good", "what", "who", "bad", ())
