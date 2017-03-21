structure Env : ENV =
struct

structure S = Symbol
structure T = Types

type access = int (* TODO: ??? *)
type ty = T.ty
datatype enventry = VarEntry of {ty: ty}
		  | FunEntry of {formals: ty list, result: ty}

val base_tenv = S.empty
val base_tenv = S.enter (base_tenv, S.symbol "int", T.WINT)
val base_tenv = S.enter (base_tenv, S.symbol "string", T.STRING)

val base_venv = S.empty
val base_venv = S.enter (base_venv, S.symbol "print",
                         FunEntry {formals=[T.STRING], result=T.UNIT})
val base_venv = S.enter (base_venv, S.symbol "flush",
                         FunEntry {formals=[], result=T.UNIT})
val base_venv = S.enter (base_venv, S.symbol "getchar",
                         FunEntry {formals=[], result=T.STRING})
val base_venv = S.enter (base_venv, S.symbol "ord",
			             FunEntry {formals=[T.STRING], result=T.INT})
val base_venv = S.enter (base_venv, S.symbol "chr",
                         FunEntry {formals=[T.INT], result=T.STRING})
val base_venv = S.enter (base_venv, S.symbol "size",
                         FunEntry {formals=[T.STRING], result=T.INT})
val base_venv = S.enter (base_venv, S.symbol "substring",
                         FunEntry {formals=[T.STRING, T.INT, T.INT], result=T.STRING})
val base_venv = S.enter (base_venv, S.symbol "concat",
                         FunEntry {formals=[T.STRING, T.STRING], result=T.STRING})
val base_venv = S.enter (base_venv, S.symbol "not",
                         FunEntry {formals=[T.INT], result=T.INT})
val base_venv = S.enter (base_venv, S.symbol "exit",
                         FunEntry {formals=[T.INT], result=T.UNIT})
end
