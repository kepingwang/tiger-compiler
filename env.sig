signature ENV =
sig
  type access
  type ty
  datatype enventry = VarEntry of {access: Translate.access,
				   ty: ty}
		    | FunEntry of {level: Translate.level,
				   formals: ty list,
				   result: ty}
  val base_tenv : ty Symbol.table       (* predefined types *)
  val base_venv : enventry Symbol.table (* predefined functions *)
end
