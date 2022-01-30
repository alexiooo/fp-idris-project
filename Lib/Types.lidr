
< module Lib.Types

< public export
> data PCFType = PCFBool
>              | PCFNat
>              | PCFUnit
>              | (~>) PCFType PCFType
>              | (*) PCFType PCFType
>
> infixr 10 ~>

We want our types to be comparable. This definition enforces unique readability.

< public export
> implementation Eq PCFType where
>   PCFBool  == PCFBool  = True
>   PCFNat   == PCFNat   = True
>   PCFUnit  == PCFUnit  = True
>   (a ~> b) == (c ~> d) = a == c && b == d
>   (a * b)  == (c * d)  = a == c && b == d
>   _        == _        = False


< public export
< Show PCFType where
<   show PCFBool = "bool"
<   show PCFNat  = "nat"
<   show PCFUnit = "unit"
<   show (x ~> y) = "(" ++ show x ++ " ~> " ++ show y ++ ")" 
<   show (x * y)  = "(" ++ show x ++ " * "  ++ show y ++ ")" 