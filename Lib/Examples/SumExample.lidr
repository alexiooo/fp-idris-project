
> module Lib.Examples.SumExample
<
< import public Lib.PCF
< import public Lib.Types.TypeOf
> import public Lib.DSL



As an aside, the Lib.DSL module allows us to write PCF terms using more familiar notation, such as
  * using λ instead of L for lambda abstraction
  * writing if' p (then' m) (else' n)
  * using nat' and bool' as types
  * writing t ^ u for application, rather than App t u 
Note the ' marks, which differentiate the embedded PCF notation from Idris

Still, it is merely sugar for PCFTerm inhabitants, so it is only relevant for making nicer 
reading PCF code

< public export
> sum : ClosedPCFTerm
> sum = Y $ λ (nat' ~> nat' ~> nat') $ λ nat' $ λ nat' $
>               (if' (IsZero (V 0))) 
>                 (then' (V 1))
>                 (else' (Succ ((V 2) ^ (V 1) ^ (Pred (V 0)))))