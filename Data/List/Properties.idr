module Data.List.Properties

%hide Prelude.List.reverse
%hide Prelude.Strings.reverse

%default total
%access public export


-- | Return the elements of a list in reverse order.
reverse' : List a -> List a -> List a
reverse' acc []      = acc
reverse' acc (x::xs) = reverse' (x::acc) xs

reverse : List a -> List a
reverse xs = reverse' [] xs

reverseNonEmpty : (xs : List a) -> NonEmpty xs -> NonEmpty (reverse xs)
reverseNonEmpty (x :: xs) IsNonEmpty = go [x] IsNonEmpty xs where
  go : (acc : List a) -> NonEmpty acc -> (xs : List a) -> NonEmpty (reverse' acc xs)
  go acc pr []        = pr
  go acc _  (x :: xs) = go (x :: acc) IsNonEmpty xs

reverseAppend : (xs : List a) -> (ys : List a) -> reverse' xs ys = reverse ys ++ xs
reverseAppend xs [] = Refl
reverseAppend xs (y :: ys) =
    rewrite reverseAppend [y] ys in
    rewrite sym $ appendAssociative (reverse' [] ys) [y] xs in
    rewrite reverseAppend (y :: xs) ys in
    Refl

reverseAppend' : (xs : List a) -> (ys : List a) -> (zs : List a) -> reverse' xs ys ++ zs = reverse' (xs ++ zs) ys
reverseAppend' xs ys zs =
    rewrite reverseAppend xs ys in
    rewrite reverseAppend (xs ++ zs) ys in
    rewrite appendAssociative (reverse' [] ys) xs zs in
    Refl


reverse2 : List a -> List a
reverse2 [] = []
reverse2 (x :: xs) = reverse2 xs ++ [x]

reverse2Append : (xs : List a) -> (ys : List a) -> reverse2 (xs ++ ys) = reverse2 ys ++ reverse2 xs
reverse2Append [] ys = rewrite appendNilRightNeutral (reverse2 ys) in Refl
reverse2Append (x :: xs) ys =
    rewrite appendAssociative (reverse2 ys) (reverse2 xs) [x] in
    rewrite reverse2Append xs ys in Refl

reverse2Involution : (xs : List a) -> xs = reverse2 (reverse2 xs)
reverse2Involution [] = Refl
reverse2Involution (x :: xs) =
    rewrite reverse2Append (reverse2 xs) [x] in
    rewrite reverse2Involution xs in
    Refl

reverse2Reverse : (xs : List a) -> reverse2 xs = reverse xs
reverse2Reverse [] = Refl
reverse2Reverse (x :: xs) =
    rewrite reverseAppend [x] xs in
    rewrite reverse2Reverse xs in
    Refl

-- TODO: Write a proof that doesn't need reverse2
reverseInvolution : (xs : List a) -> xs = reverse (reverse xs)
reverseInvolution xs =
    rewrite sym $ reverse2Reverse xs in
    rewrite sym $ reverse2Reverse (reverse2 xs) in
    rewrite reverse2Involution xs in
    Refl
