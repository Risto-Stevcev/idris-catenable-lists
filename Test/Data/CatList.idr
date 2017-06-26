module Test.Data.CatList

import Test.Assert
import Data.CatQueue
import Data.CatList

%access public export

-------------------------------------------------------------------------------

foo : CatList Nat
foo =
  CatCons 1
    (MkCatQueue
      [(CatCons 2
          (MkCatQueue
            [(CatCons 3 (MkCatQueue [] []))]
            [])
      )]
      [])

showFoo : IO ()
showFoo =
  assertEq
    (show foo)
    "CatCons 1 MkCatQueue [CatCons 2 MkCatQueue [CatCons 3 MkCatQueue [] []] []] []"
