module Test.Data.CatQueue

import Data.CatQueue

%access public export

assertEq : Eq a => (given : a) -> (expected : a) -> IO ()
assertEq g e = if g == e
    then putStrLn "Test Passed"
    else putStrLn "Test Failed"

assertNotEq : Eq a => (given : a) -> (expected : a) -> IO ()
assertNotEq g e = if not (g == e)
    then putStrLn "Test Passed"
    else putStrLn "Test Failed"

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
