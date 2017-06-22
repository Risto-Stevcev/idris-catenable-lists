module Test.Data.CatQueue

import Test.Assert
import Data.CatQueue

%access public export

-------------------------------------------------------------------------------

foo : CatQueue Nat
foo = MkCatQueue [1,2,3] []

bar : CatQueue Nat
bar = MkCatQueue [] [3,2,1]

baz : CatQueue Nat
baz = MkCatQueue [] []

x : CatQueue Nat
x = MkCatQueue [1] [2,3,4]

y : CatQueue Nat
y = MkCatQueue [5,6] [7,8,9]

z : CatQueue Nat
z = MkCatQueue [10,11,12] [13]
--[1] [2,3,4]   [5,6] [7,8,9]   [10,11,12] [13]

fooIsBar : IO ()
fooIsBar = assertEq foo bar

fooIsNotBaz : IO ()
fooIsNotBaz = assertNotEq foo baz

nullIsEmpty : IO ()
nullIsEmpty = assertTrue $ null (the (CatQueue String) neutral)

xyzAssociative : IO ()
xyzAssociative = do
  putStrLn $ show $ x <+> (y <+> z)
  putStrLn $ show $ (x <+> y) <+> z
  assertTrue $ x <+> (y <+> z) == (x <+> y) <+> z

