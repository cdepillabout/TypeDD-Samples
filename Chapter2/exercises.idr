
module Main

palidrome : Nat -> String -> Bool
palidrome len str = toLower str == toLower (reverse str) && length str >= len

counts : String -> (Nat, Nat)
counts input = (length (words input), length (cast input))

top_ten : Ord a => List a -> List a
top_ten list = take 10 $ reverse $ sort list

over_length : Nat -> List String -> Nat
over_length len list = length $ filter (> len) $ map length list

palidromeMain : IO ()
palidromeMain = repl "> " $ \input => show $ palidrome 3 input
