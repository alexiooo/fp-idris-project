< module Lib.Examples.SumEvaluation
<
< import public Lib.Reduction
< import public Lib.Examples.SumExample

> sum_2_3 : ClosedPCFTerm
> sum_2_3 = sum ^ (Succ (Succ Zero)) ^ (Succ (Succ (Succ Zero)))

> type_sum_2_3 : Maybe PCFType
> type_sum_2_3 = typeOfClosed sum_2_3   -- == Just PCFNat