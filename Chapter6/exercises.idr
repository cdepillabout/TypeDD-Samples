
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
adder Z accum = ?adder_rhs_1
adder (S k) accum = ?adder_rhs_2
