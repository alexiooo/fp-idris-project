module Lib.Existentials

-- See https://gist.github.com/adituv/dcea611d75722560a3af64f5ae651804

public export
exists : {k : Type} -> (k -> Type) -> Type
exists t = (b : Type) -> ({a : _} -> t a -> b) -> b

packExists : {k : Type} -> {t : k -> Type} -> {a : k} -> t a -> exists t
packExists x = \b, f => f x

unpackExists : {k : Type} -> {t : k -> Type} -> exists t -> {b : Type} -> ({a : k} -> t a -> b) -> b
unpackExists exT {b = b'} f = exT b' f
