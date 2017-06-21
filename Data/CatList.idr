module Data.CatList

import Data.CatQueue

%default total
%access public export

-- | A strict catenable list.
-- |
-- | `CatList` may be empty, represented by `CatNil`.
-- |
-- | `CatList` may be non-empty, represented by `CatCons`. The `CatCons`
-- | data constructor takes the first element of the list and a queue of
-- | `CatList`.
data CatList a = CatNil | CatCons a (CatQueue (CatList a))

data NonEmptyCatList : CatList a -> Type where
  IsNonEmptyCatList : NonEmptyCatList (CatCons a as)

data EmptyCatList : CatList a -> Type where
  IsEmptyCatList : EmptyCatList CatNil

data SingletonCatList : CatList a -> Type where
  IsSingletonCatList : SingletonCatList (CatCons a (MkCatQueue [] []))

Eq l => Eq (CatList l) where
  (==) CatNil CatNil = True
  (==) CatNil (CatCons x y) = False
  (==) (CatCons x z) CatNil = False
  (==) (CatCons x z) (CatCons y w) = x == y && (assert_total (z == w))
  (/=) x y = not (x == y)


-- | Create an empty catenable list.
-- |
-- | Running time: `O(1)`
empty : CatList a
empty = CatNil

-- | Test whether a catenable list is empty.
-- |
-- | Running time: `O(1)`
null : CatList a -> Bool
null CatNil = True
null _ = False

-- | Links two catenable lists by making appending the queue in the
-- | first catenable list to the second catenable list. This operation
-- | creates a new catenable list.
-- |
-- | Running time: `O(1)`
link : CatList a -> CatList a -> CatList a
link CatNil cat = cat
link (CatCons a q) cat = CatCons a (snoc q cat)

-- | Append all elements of a catenable list to the end of another
-- | catenable list, create a new catenable list.
-- |
-- | Running time: `O(1)`
append : CatList a -> CatList a -> CatList a
append as CatNil = as
append CatNil as = as
append as bs = link as bs

-- | Append an element to the beginning of the catenable list, creating a new
-- | catenable list.
-- |
-- | Running time: `O(1)`
cons : a -> CatList a -> CatList a
cons a cat = append (CatCons a neutral) cat

-- | Create a catenable list with a single item.
-- |
-- | Running time: `O(1)`
singleton : a -> CatList a
singleton a = cons a CatNil

-- | Append an element to the end of the catenable list, creating a new
-- | catenable list.
-- |
-- | Running time: `O(1)`
snoc : CatList a -> a -> CatList a
snoc cat a = append cat (CatCons a neutral)

-- | Tail recursive version of foldr on `CatList`.
-- |
-- | Ensures foldl on `List` is tail-recursive.
foldr : (CatList a -> CatList a -> CatList a) -> CatList a -> CatQueue (CatList a) -> CatList a
foldr k b q = go q Nil
  where
    foldl : (acc -> e -> acc) -> acc -> List e -> acc
    foldl _ c Nil = c
    foldl k' c (b' :: as) = foldl k' (k' c b') as

    go : CatQueue (CatList a) -> List (CatList a -> CatList a) -> CatList a
    go xs ys = assert_total $ case uncons' xs of
      Nothing => foldl (\x => \i => i x) b ys
      Just (x, rest) => go rest ((k x) :: ys)

-- | Decompose a catenable list into a tuple of the first element and
-- | the rest of the catenable list.
-- |
-- | Running time: `O(1)`
-- |
-- | Note that any single operation may run in `O(n)`.
uncons : (l : CatList a) -> {auto prf : NonEmptyCatList l} -> (a, (CatList a))
uncons (CatCons a q) = (a, (if null q then CatNil else (foldr link CatNil q)))

uncons' : CatList a -> Maybe (a, (CatList a))
uncons' CatNil = Nothing
uncons' (CatCons a q) = Just (a, (if null q then CatNil else (foldr link CatNil q)))



-------------------------------------------------------------------------------
-- | Properties
-------------------------------------------------------------------------------

appendEmptyEmpty : (l : CatList a) -> (l' : CatList a) ->
                   {auto prf : EmptyCatList l} -> {auto prf : EmptyCatList l'} ->
                   EmptyCatList (append l l')
appendEmptyEmpty CatNil CatNil = IsEmptyCatList

singletonNonEmpty : SingletonCatList l -> NonEmptyCatList l
singletonNonEmpty IsSingletonCatList = IsNonEmptyCatList

consEmptyNonEmpty : (x : a) -> (l : CatList a) -> {auto prf : EmptyCatList l} -> NonEmptyCatList (cons x l)
consEmptyNonEmpty x CatNil = IsNonEmptyCatList

consEmptySingleton : (x : a) -> (l : CatList a) -> {auto prf : EmptyCatList l} -> SingletonCatList (cons x l)
consEmptySingleton x CatNil = IsSingletonCatList

snocEmptyNonEmpty : (x : a) -> (l : CatList a) -> {auto prf : EmptyCatList l} -> NonEmptyCatList (snoc l x)
snocEmptyNonEmpty x CatNil = IsNonEmptyCatList

snocEmptySingleton : (x : a) -> (l : CatList a) -> {auto prf : EmptyCatList l} -> SingletonCatList (snoc l x)
snocEmptySingleton x CatNil = IsSingletonCatList

appendNilRightNeutralCL : (l : CatList a) -> (l' : CatList a) -> {auto prf : EmptyCatList l'} -> l = append l l'
appendNilRightNeutralCL l CatNil = Refl

appendNilLeftNeutralCL : (l : CatList a) -> (l' : CatList a) -> {auto prf : EmptyCatList l'} -> l = append l' l
appendNilLeftNeutralCL CatNil CatNil = Refl
appendNilLeftNeutralCL (CatCons x y) CatNil = Refl
