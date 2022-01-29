
|||
||| This module serves only as code-generator for DecEq.idr
||| Updating that file by executing the following in a shell
||| idris2 -x main CodeGen/TermDecEq.idr > Lib/Terms/DecEq.idr
|||
module CodeGen.TermDecEq

import Data.List

symbols : List (List String)
symbols = [
  [ -- 3-ary
    "IfElse"
  ],
  [ -- binary
    "App   ", 
    "Pair  "
  ],
  [ -- unary
    "Fst   ",
    "Snd   ",
    "Succ  ",
    "Pred  ",
    "IsZero",
    "Y     "
  ],
  [ -- nullary    
    "T     ",
    "F     ",
    "Zero  ",
    "Unit  "
  ]
]

genUninhabitedImpl : String -> String -> String
genUninhabitedImpl x y = """
implementation Uninhabited (Symbol.\{x} = Symbol.\{y}) where uninhabited Refl impossible

"""

genUninhabited : String
genUninhabited = 
  concatMap impls symbols
  where
    implsWith : List String -> String -> String
    implsWith sym x = concatMap (genUninhabitedImpl x) $ filter (x /= ) sym
    impls : List String -> String
    impls sym = concatMap (implsWith sym) sym



genDecEqYes : String -> String
genDecEqYes x  = "  decEq \{x} \{x} = Yes Refl\n"

genDecEqNo : String -> String -> String
genDecEqNo x y = "  decEq \{x} \{y} = No absurd\n"

genDecEq : String
genDecEq = """
implementation DecEq (Symbol k) where
\{concatMap yesImpls symbols}
\{concatMap noImpls symbols}
""" where
      yesImpls : List String -> String
      yesImpls sym = concat $ map genDecEqYes sym
      noImplsWith : List String -> String -> String
      noImplsWith sym x = concatMap (genDecEqNo x ) $ filter (x /= ) sym
      noImpls : List String -> String
      noImpls sym = concatMap (noImplsWith sym) sym




genImplementation : String
main : IO ()

main = putStr genImplementation
genImplementation = """
-- !!!
-- !!! THIS FILE IS AUTO-GENERATED, DO NOT MODIFY IT DIRECTLY
-- !!!

module Lib.Terms.DecEq

import Lib.Terms
import public Decidable.Equality

\{genUninhabited}

\{genDecEq}
"""