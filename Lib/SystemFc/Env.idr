
module Lib.SystemFc.Env 

import  Lib.SystemFc.TermTyp

public export
TermCtx : Type
TermCtx = Term -> Typ

public export
TypVarCtx : Type
TypVarCtx = List (TypVar, Kind)

public export
ValConstrCtx : Type
ValConstrCtx = List (ValConstr, Kind)

public export
CoercConstCtx : Type
CoercConstCtx = List (CoercConst, Kind)


public export
Context : Type
Context = (TypVarCtx, ValConstrCtx, CoercConstCtx)
