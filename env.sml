structure Env : ENV =
struct

structure S = Symbol
structure T = Types
structure Trans = Translate

type access = int (* TODO: ??? *)
type ty = T.ty
datatype enventry = VarEntry of {access: Translate.access,
				                 ty: ty}
		          | FunEntry of {level: Translate.level,
				                 formals: ty list,
				                 result: ty}

val base_tenv = S.empty
val base_tenv = S.enter (base_tenv, S.symbol "int", T.WINT)
val base_tenv = S.enter (base_tenv, S.symbol "string", T.STRING)

val base_venv = S.empty
val base_venv = S.enter (base_venv, S.symbol "print",
                         FunEntry {formals=[T.STRING], level=Trans.outermost, result=T.UNIT})
val base_venv = S.enter (base_venv, S.symbol "flush",
                         FunEntry {formals=[], level=Trans.outermost, result=T.UNIT})
val base_venv = S.enter (base_venv, S.symbol "getchar",
                         FunEntry {formals=[], level=Trans.outermost, result=T.STRING})
val base_venv = S.enter (base_venv, S.symbol "ord",
			             FunEntry {formals=[T.STRING], level=Trans.outermost, result=T.INT})
val base_venv = S.enter (base_venv, S.symbol "chr",
                         FunEntry {formals=[T.INT], level=Trans.outermost, result=T.STRING})
val base_venv = S.enter (base_venv, S.symbol "size",
                         FunEntry {formals=[T.STRING], level=Trans.outermost, result=T.INT})
val base_venv = S.enter (base_venv, S.symbol "substring",
                         FunEntry {formals=[T.STRING, T.INT, T.INT], level=Trans.outermost, result=T.STRING})
val base_venv = S.enter (base_venv, S.symbol "concat",
                         FunEntry {formals=[T.STRING, T.STRING], level=Trans.outermost, result=T.STRING})
val base_venv = S.enter (base_venv, S.symbol "not",
                         FunEntry {formals=[T.INT], level=Trans.outermost, result=T.INT})
val base_venv = S.enter (base_venv, S.symbol "exit",
                         FunEntry {formals=[T.INT], level=Trans.outermost, result=T.UNIT})
end
