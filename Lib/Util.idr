
module Lib.Util

import Lib.Terms

%default total

public export
JustS : Symbol ar -> Vect ar (PCFTerm k) -> Maybe (PCFTerm k)
JustS s arg = Just $ S s arg

