
module Lib.SystemFc.Env 

import  Lib.SystemFc.TermTyp

public export
TermCtx : Type
TermCtx = List (TypVar, Kind)

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


lookup : Eq a => List (a, b) -> a -> Maybe b
lookup ((key, val) :: rs) needle  = if key == needle then Just val else lookup rs needle
lookup []                 _       = Nothing


export
lookupTypVar : Context -> TypVar -> Maybe Kind
lookupTypVar (ctx, _, _) v = lookup ctx v

export
lookupValConstr : Context -> ValConstr -> Maybe Kind
lookupValConstr (_, ctx, _) v = lookup ctx v

export
lookupCoercConst : Context -> CoercConst -> Maybe Kind
lookupCoercConst (_, _, ctx) v = lookup ctx v