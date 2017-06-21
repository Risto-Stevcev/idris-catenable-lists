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

fooIsBar : IO ()
fooIsBar = assertEq foo bar

fooIsNotBaz : IO ()
fooIsNotBaz = assertNotEq foo baz

nullIsEmpty : IO ()
nullIsEmpty = assertTrue $ null (the (CatQueue String) neutral)

