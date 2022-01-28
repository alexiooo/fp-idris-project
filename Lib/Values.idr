
module Lib.Values

import Lib.PCF

-- A certain subset of terms are called `values'

public export
data PCFValue = T 
              | F 
              | Zero 
              | Succ PCFValue
              | I
              | P PCFTerm PCFTerm
              | L PCFType PCFTerm

public export
fromTerm : PCFTerm -> Maybe PCFValue
fromTerm T          = Just T
fromTerm F          = Just F
fromTerm Zero       = Just Zero
fromTerm (Succ t)   = do v <- fromTerm t
                         Just (Succ v)
fromTerm I          = Just I
fromTerm (P m n)    = Just (P m n)
fromTerm (L t m)  = Just (L t m)
fromTerm _          = Nothing

public export
toTerm : PCFValue -> PCFTerm
toTerm T          = T
toTerm F          = F
toTerm Zero       = Zero
toTerm (Succ v)   = Succ (toTerm v)
toTerm I          = I
toTerm (P m n)    = P m n
toTerm (L t m)    = L t m

-- Firstly, the only value which has type `Unit`, is I

-- unitTypeValue : (v : PCFValue) -> typeOfClosed = Just Unit -> v /=

-- Values correspond exactly to terms that are in normal forms.
-- That is, terms that cannot be reduced further, as is expressed by the smallStep function returning Nothing

valuesAreNormalForms : (v : PCFValue) -> smallStep (toTerm v) = Nothing
valuesAreNormalForms T        = Refl
valuesAreNormalForms F        = Refl
valuesAreNormalForms Zero     = Refl
valuesAreNormalForms I        = Refl
valuesAreNormalForms (P m n)  = ?p
valuesAreNormalForms (L t m)  = ?l

-- >   normalFormsAreValues : (t : PCFTerm) -> {auto hnf : smallStep t = Nothing} -> exists (\v -> fromTerm t = Just v)
-- >   normalFormsAreValues = ?undefined2
