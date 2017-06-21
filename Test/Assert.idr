module Test.Assert

%access export

assertEq : Eq a => (given : a) -> (expected : a) -> IO ()
assertEq g e = if g == e
    then putStrLn "Test Passed"
    else putStrLn "Test Failed"

assertNotEq : Eq a => (given : a) -> (expected : a) -> IO ()
assertNotEq g e = if not (g == e)
    then putStrLn "Test Passed"
    else putStrLn "Test Failed"

assertTrue : Bool -> IO ()
assertTrue p = if p
    then putStrLn "Test Passed"
    else putStrLn "Test Failed"

assertFalse : Bool -> IO ()
assertFalse p = if (not p)
    then putStrLn "Test Passed"
    else putStrLn "Test Failed"
