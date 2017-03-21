structure Semant =
struct

structure S = Symbol
structure T = Types
structure A = Absyn
structure E = Env
val err = ErrorMsg.error

type venv = E.enventry Symbol.table
type tenv = T.ty Symbol.table

(* Translate module is reserved for intermediate code *)
structure Translate = struct type exp = unit end
type expty = {exp: Translate.exp, ty: T.ty}

val loop_nest_level = ref 0

fun say s = TextIO.output (TextIO.stdOut, s ^"\n")

fun has_duplicate_item [] = (0, false)
  | has_duplicate_item ((x, pos)::xs) =
    if (List.exists (fn (y, pos_y) => x = y) xs)
    then (pos, true)
    else (has_duplicate_item xs)

fun actualTy ty = (
	case ty of
		T.NAME(_, real_ty) => (actualTy (Option.valOf (!real_ty)) )
	  | real_ty => real_ty
)

fun checkCycle (ty, pos) =
  let
      fun next curr_ty =
        case curr_ty of
            T.NAME(_, real_ty) => Option.valOf (!real_ty)
          | t => t
      fun check (visited_ty, curr_ty) =
        case curr_ty of
            T.NAME _ => if (List.exists (fn t => t = curr_ty) visited_ty) then true
                      else check (curr_ty::visited_ty, (next curr_ty))
          | _ => false
      val next_ty = next ty
  in
      if check ([ty], next_ty) then
          (err pos "There's a cycle in type declaration."; true)
      else
          false
  end


fun checkRecord (ty, pos) =
  (case actualTy ty of
       T.RECORD _ => true
     | T.BOTTOM => true
     | T.NIL => true
     | t => (err pos ("Record expected, but get: " ^ (T.toString t)); false)
  )
fun checkInt (ty, pos) =
  (case actualTy ty of
       T.INT => true
     | T.WINT => true
     | T.BOTTOM => true
     | t => (err pos ("Int expected, but get: " ^ (T.toString t)); false)
  )
fun checkString (ty, pos) =
  (case actualTy ty of
       T.STRING => true
     | T.BOTTOM => true
     | t => (err pos ("String expected, but get: " ^ (T.toString t)); false)
  )
fun checkArray (ty, pos) =
  (case actualTy ty of
       T.ARRAY _ => true
     | T.BOTTOM => true
     | t => (err pos ("Array expected, but get: " ^ (T.toString t)); false)
  )
fun checkUnit (ty, pos) =
  (case actualTy ty of
       T.UNIT => true
     | T.BOTTOM => true
     | t => (err pos ("Unit expected, but get: " ^ (T.toString t)); false)
  )

fun lookT (tenv, tname, pos) =
  ( case S.look (tenv, tname) of
        SOME(ty) => actualTy ty
      | NONE => (err pos ("Type:" ^ (S.name tname) ^ " not found"); T.BOTTOM)
  )

fun shallowLookT (tenv, tname, pos) =
  ( case S.look (tenv, tname) of
        SOME(ty) => ty
      | NONE => (err pos ("Type:" ^ (S.name tname) ^ " not found"); T.BOTTOM)
  )

fun isSubTypeOf super sub =
  if super = sub
  then true
  else case super of
           T.RECORD _ => (case sub of
                              T.NIL => true
                            | T.BOTTOM => true
                            | _ => false
                         )
         | T.INT => (case sub of
                         T.WINT => true
                       | T.BOTTOM => true
                       | _ => false
                    )
         | T.BOTTOM => true
         | _ => ( case sub of
                      T.BOTTOM => true
                    | _ => false
                )
fun isAssignable left right =
  if left = right
  then true
  else case left of
           T.RECORD _ => (case right of
                              T.NIL => true
                            | T.BOTTOM => true
                            | _ => false
                         )
         | T.WINT => (case right of
                         T.INT => true
                       | T.BOTTOM => true
                       | _ => false
                     )
         | T.BOTTOM => true
         | _ => ( case right of
                      T.BOTTOM => true
                    | _ => false
                )


fun isCompatible a b = (isSubTypeOf a b) orelse (isSubTypeOf b a)
fun findSuperType a b = if isSubTypeOf a b
                        then a
                        else
                            if isSubTypeOf b a
                            then b
                            else T.BOTTOM

(* TODO in general: what type to return when err? Now I return T.INT *)

fun transExp (venv:venv, tenv:tenv) =
  let
      fun trexp (A.VarExp(var)) = trvar var
        | trexp (A.NilExp) = {exp=(),ty=T.NIL}
        | trexp (A.IntExp(num)) = {exp=(),ty=T.INT}
        | trexp (A.StringExp(str,pos)) = {exp=(),ty=T.STRING}
        | trexp (A.CallExp{func=func_name,args,pos}) =
          let
              (*check if types of args match formals*)
              fun trcall ([], [], result) = {exp=(),ty=result}
                | trcall (formal_head::formal_tail,arg_head::arg_tail, result) =
                  let
                      val {exp = arg_exp, ty = arg_ty} = trexp arg_head
                      val {exp = tail_exp, ty = tail_ty} = trcall (formal_tail, arg_tail, result)
                  in
                      if isAssignable (actualTy formal_head) arg_ty
                      then
                          {exp=(), ty=result}
                      else
                          (err pos ("Function argument types do not match its declaration. Get: " ^ (T.toString arg_ty) ^ " Expected: " ^ (T.toString (actualTy formal_head)) );{exp=(), ty=result})
                  end
                | trcall ([], _, result) = (err pos "Too many arguments."; {exp=(), ty=result})
                | trcall (_, [], result) = (err pos "Too few arguments."; {exp=(), ty=result})
          in
	          case S.look(venv,func_name) of
	              SOME(E.FunEntry{formals,result}) => trcall(formals, args, result)
	            | _ => (err pos ("function "^S.name func_name^" not defined"); {exp=(),ty=T.BOTTOM})
          end
        | trexp (A.OpExp{left,oper,right,pos}) = troper(left,oper,right,pos)
        | trexp (A.RecordExp{fields = field_inst_list, typ = rec_name, pos}) =
          let
              val rec_ty = lookT (tenv, rec_name, pos)
              (* A record instantiation must define the value of all the fields
                 and in the same order as in the definition of the record type. *)
              fun tr_record_inst ([], []) = ()
                | tr_record_inst ((dec_fname,dec_ty)::dec_tail, (inst_fname, inst_exp, pos)::inst_dec)  =
                  let
                      val {exp, ty} = trexp inst_exp
                  in
                      if (S.name dec_fname) = (S.name inst_fname)
                      then if  isAssignable (actualTy dec_ty) (actualTy ty)
                           then ()
                           else (err pos "Field instantiation expression has a wrong type.")
                      else (err pos ("Incorrect field name:" ^ S.name inst_fname);())
                  end
                | tr_record_inst ([], _) = err pos "Too many fields."
                | tr_record_inst (_, []) = err pos "Too few fields."
          in
              case rec_ty of
                  T.RECORD (field_dec_list, unq) => {exp=tr_record_inst (field_dec_list, field_inst_list), ty=rec_ty}
                | _ => ({exp=(), ty=rec_ty})
          end
	    | trexp (A.SeqExp([])) =
	      {exp=(),ty=T.UNIT}
        | trexp (A.SeqExp([(exp,pos)])) =
	      trexp exp
        | trexp (A.SeqExp((exp,pos)::exp_tail)) =
	      let
              val {exp=head_exp, ty=head_ty} = trexp exp
	          val {exp=rest_exp, ty=rest_ty} = trexp (A.SeqExp exp_tail)
	      in
              {exp=(), ty=rest_ty}
	      end
        | trexp (A.AssignExp{var,exp,pos}) =
	      let
	          val {exp=left_exp,ty=left_ty} = trvar var
	          val {exp=right_exp,ty=right_ty} = trexp exp
	      in
              case left_ty of
                  T.INT => (err pos "Cannot assign to loop variable"; {exp=(), ty=T.UNIT})
                | _ => (
	                  if isAssignable left_ty right_ty
	                  then {exp=(),ty=T.UNIT}
	                  else (err pos ("The types of operand for operator assignment do not match. left: " ^ (T.toString left_ty) ^" right: " ^ (T.toString right_ty)); {exp=(),ty=T.UNIT})
                  )
	      end
        | trexp (A.IfExp{test,then',else'=SOME(else'),pos}) =
	      (* Note!!!:
	 if-then-else return the type of exp2 and exp3
	 if-then must return void *)
	      let
              val {exp=test_exp, ty=test_ty} = trexp test
	          val {exp=if_exp,ty=then_ty} = trexp then'
	          val {exp=else_exp,ty=else_ty} = trexp else'
	      in
              checkInt(test_ty, pos);
              if (isCompatible then_ty else_ty)
	          then {exp=(),ty=findSuperType then_ty else_ty}
	          else (err pos "Types of then branch and else branch do not match."; {exp=(),ty=T.BOTTOM})
	      end
        | trexp (A.IfExp{test,then',else'=NONE,pos}) =
          let
              val {exp=test_exp, ty=test_ty} = trexp test
	          val {exp=if_exp,ty=then_ty} = trexp then'
          in
              checkInt(test_ty, pos);
              checkUnit(then_ty, pos);
	          {exp=(),ty=T.UNIT}
          end
        | trexp (A.WhileExp{test,body,pos}) =
          let
              val {exp=test_exp, ty=test_ty} = trexp test
          in
              loop_nest_level := !loop_nest_level + 1;
              let
	              val {exp=body_exp,ty=body_ty} = trexp body
              in
                  loop_nest_level := !loop_nest_level - 1;
	              checkInt(test_ty, pos);
	              checkUnit(body_ty, pos);
	              {exp=(),ty=T.UNIT}
              end
          end
        | trexp (A.ForExp{var=id,escape,lo,hi,body,pos}) =
	      (* for id := exp1 to exp2 do exp3 *)
	      (* id is a variable implicitly declared by for statement, *)
	      (* whose scope only covers exp3, but cannot be assigned to in exp3 *)
	      (*     The start and end index must be of type *)
	      (* int. The variable is of type int and must not be *)
	      (* assigned to in the body. The body must be of type *)
	      (* void. The result type is void. *) (* ??? how to do this ??? *)
          let
              val {exp=lo_exp, ty=lo_ty} = trexp lo
              val {exp=hi_exp, ty=hi_ty} = trexp hi
              val venv' = S.enter (venv, id, E.VarEntry {ty=T.INT})
          in
              loop_nest_level := !loop_nest_level + 1;
              let
                  val {exp=body_exp, ty=body_ty} = transExp (venv', tenv) body
              in
                  loop_nest_level := !loop_nest_level - 1;
                  checkInt(lo_ty, pos);
                  checkInt(hi_ty, pos);
                  checkUnit(body_ty, pos);
                  {exp=(), ty=T.UNIT}
              end
          end
        | trexp (A.BreakExp(pos)) = (if !loop_nest_level = 0
                                     then err pos "Break can only be inside a loop."
                                     else ();
                                     {exp=(),ty=T.BOTTOM})
        | trexp (A.LetExp{decs=[],body,pos}) =
	      trexp body
        | trexp (A.LetExp{decs=[dec],body,pos}) =
	      let
              val {venv=venv',tenv=tenv'} = transDec(venv,tenv,dec)
	      in
              transExp(venv',tenv') body
	      end
        | trexp (A.LetExp{decs=dec::decs,body,pos}) =
	      let
	          val {venv=venv',tenv=tenv'} = transDec(venv,tenv,dec)
	      in
	          transExp (venv',tenv') (A.LetExp{decs=decs,body=body,pos=pos})
	      end
        | trexp (A.ArrayExp{typ,size,init, pos}) =
          (* The tyId must refer to an array type. *)
          (* The expression in square brackets must be int, and *)
          (* the expression after of must match the element *)
          (* type of the array. The result type is the array type. *)
	      let
              val arr_ty = lookT (tenv, typ, pos)
              val {exp=size_exp, ty=size_ty} = trexp size
              val {exp=init_exp, ty=init_ty} = trexp init
	      in
              if checkArray (arr_ty, pos)
              then
                  if checkInt (size_ty, pos)
                  then
                      case arr_ty of
                          T.ARRAY (ele_ty, _) => if isAssignable (actualTy ele_ty) init_ty
                                                  then {exp=(), ty=arr_ty}
                                                  else (err pos "Init type doesn't match array dec.";{exp=(), ty=arr_ty})
                        | _ => {exp=(), ty=T.BOTTOM}
                  else (err pos "Size type should be Int."; {exp=(), ty=arr_ty})
              else {exp=(), ty=T.BOTTOM}
	      end
      and troper (left,oper,right,pos) =
          let
              val {exp=left_exp, ty=left_ty} = trexp left
              val {exp=right_exp, ty=right_ty} = trexp right
          in
              case oper of
                  (A.PlusOp | A.MinusOp | A.TimesOp | A.DivideOp ) => (
                   checkInt(left_ty, pos);
                   checkInt(right_ty, pos);
                   {exp=(), ty=T.INT}
               )
               |  (A.EqOp | A.NeqOp ) => (
                   if isCompatible left_ty right_ty
                   then {exp=(), ty=T.INT}
                   else (err pos ("Left and right types are not compatible, where left :" ^ (T.toString left_ty) ^ " right :" ^ (T.toString right_ty));{exp=(), ty=T.INT})
               )
               | (A.LtOp | A.LeOp | A.GtOp | A.GeOp) => (
                   if isCompatible left_ty right_ty
                   then case left_ty of
                         (T.STRING | T.INT
                         | T.WINT) => {exp=(), ty=T.INT}
                         | _ => (err pos "Only string or int can be compared for order."; {exp=(), ty=T.INT})
                   else (err pos ("Left and right types are not compatible, where left :" ^ (T.toString left_ty) ^ " right :" ^ (T.toString right_ty));{exp=(), ty=T.INT})

               )
          end
      and trvar (A.SimpleVar(id, pos)) =
          (
            case S.look(venv,id) of
	            SOME(E.VarEntry{ty=var_ty}) => {exp=(), ty=actualTy var_ty}
	          | _ =>
                (
	              err pos ("Undefined variable " ^ S.name id);
	              {exp=(), ty=T.BOTTOM}
                )
          )
        | trvar (A.FieldVar(var, id, pos)) =
	      let
	          val {exp=var_exp, ty=var_ty} = trvar var
	          val fieldList =
	              case var_ty of
		              T.RECORD (fieldList, uniq) => fieldList
		            | t => (err pos ("Variable not record, but " ^ (T.toString t)); [])
              fun findFieldTy ([], fname) = (err pos ("Field "^S.name fname ^ " doesn't exist."); {exp=(), ty=T.BOTTOM})
                | findFieldTy ((dec_name, dec_ty)::ftail, fname) =
                  if dec_name = fname
                  then {exp=(), ty=actualTy dec_ty}
                  else findFieldTy (ftail, fname)
	      in
              findFieldTy (fieldList, id)
	      end
        | trvar (A.SubscriptVar(var, index, pos)) =
	      let
	          val {exp=var_exp, ty=var_ty} = trvar var
              val {exp=index_exp, ty=index_ty} = trexp index
	      in
              checkInt(index_ty, pos);
              checkArray(var_ty, pos);
              case var_ty of
                  T.ARRAY (ele_ty, _) => {exp=(), ty=actualTy ele_ty}
                | _ => {exp=(), ty=T.BOTTOM}
	      end
  in
      trexp
  end
and transDec (venv,tenv,A.FunctionDec(fundecs)) : {venv:venv,tenv:tenv} =
    let
        fun addFunDec ({name=func_name, params, result, body, pos}, venv) =
          let
              fun findParamType {name=var_name, escape, typ=type_name, pos} = lookT (tenv, type_name, pos)
              val formals_ty = map findParamType params
              val result_ty = case result of
                                  SOME(type_name, pos) => lookT (tenv, type_name, pos)
                                | NONE => T.UNIT
          in
              S.enter (venv, func_name, E.FunEntry {formals=formals_ty, result=result_ty})
          end
        val venv' = foldl addFunDec venv fundecs
        fun addFunParam ({name=var_name, escape, typ=type_name, pos}, venv) = S.enter (venv, var_name, E.VarEntry {ty=lookT (tenv, type_name, pos)})
        fun transFunBody {name, params, result, body, pos} = let
            val venv'' = foldl addFunParam venv' params
            val {exp=body_exp, ty=body_ty} = transExp (venv'', tenv) body
            val result_ty = case result of
                                SOME(type_name, pos) => lookT (tenv, type_name, pos)
                              | NONE => T.UNIT
        in
            if isAssignable result_ty body_ty
            then ()
            else (err pos "Type of function body doesn't match declaration.";())
        end
        val (dup_pos, dup_bool) = has_duplicate_item (map (fn {name, params, result, body, pos} => (name, pos)) fundecs)
    in
        if  dup_bool then err dup_pos "Duplicated names in a sequence of function declarations."
        else ();
        map transFunBody fundecs;
        {venv=venv',tenv=tenv}
    end
  | transDec (venv,tenv,A.VarDec{name,escape,typ=type_option,init,pos}) =
    let
        (*If the init exp is "Nil" then the type can only be type_optoin *)
        val {exp=init_exp,ty=init_ty} = transExp (venv,tenv) init
    in
        case type_option of
            SOME(type_name, pos) =>
            let
                val dec_ty = lookT (tenv, type_name, pos)
                val venv' = S.enter (venv, name, E.VarEntry {ty=dec_ty})
            in
                if isAssignable dec_ty init_ty
                then {venv=venv', tenv=tenv}
                else (err pos "Init expression has a different type from declaration.";{venv=venv', tenv=tenv})
            end
          | NONE =>
            case init_ty of
                T.NIL => (err pos "Record type must be specified when init with Nil.";{venv=S.enter (venv, name, E.VarEntry {ty=T.BOTTOM}), tenv=tenv})
              | T.INT => ({venv=S.enter (venv, name, E.VarEntry {ty=T.WINT}), tenv=tenv})
              | _ => ({venv=S.enter (venv, name, E.VarEntry {ty=init_ty}), tenv=tenv})
    end
  | transDec (venv,tenv,A.TypeDec(decList)) =
    (* Using foldl recursively add each symbol name into our environment, next we will give each an 'actual type'*)
    let
        val tenv' = List.foldl (fn({name, ...},tenv) => S.enter(tenv,name,T.NAME(name,ref NONE))) tenv decList
        val (dup_pos, dup_bool) = has_duplicate_item (map (fn {name, ty, pos} => (name, pos)) decList)
    in
        if  dup_bool then err dup_pos "Duplicated names in a sequence of type declarations."
        else ();
        List.map (fn({name, ty, pos}) => (
                      case S.look(tenv',name) of
                          SOME(T.NAME (_, tyOpRef)) => tyOpRef := SOME(transTy (tenv', ty))
                        | _ => ())) decList;
        let
            val typ_list = map (fn {name, ty, pos} => (shallowLookT (tenv', name, pos), pos)) decList
            val results = map checkCycle typ_list
            val cycle_found = foldl (fn (curr,acc) => curr orelse acc) false results
            fun reset_types [] = ()
              | reset_types ((T.NAME(_, ty_ref), _)::tail) = (ty_ref := SOME(T.BOTTOM); reset_types tail)
              | reset_types (head::tail) = ()
        in
            if cycle_found then reset_types typ_list
            else ()
        end;
        {venv=venv, tenv=tenv'}
    end
(* we take in an A.NameType and return the true T.Type, unless we can't find it*)
and transTy (tenv, A.NameTy(tid,pos)) =
    (
      case S.look(tenv, tid) of
          SOME(ty) => ty
        | NONE => (err pos ("cannot find type "^S.name tid); T.BOTTOM)
    )
  | transTy (tenv, A.RecordTy(fields)) =
    let (* What is record escape? *)
        val tfields = map (fn {name,escape,typ,pos} =>
                              case S.look(tenv,typ) of
                                  SOME(ty) => (name,ty)
			                    | NONE => (err pos ("cannot find field type: " ^ (S.name typ)); (name,T.BOTTOM))
			              ) fields
        val (dup_pos, dup_bool) = has_duplicate_item (map (fn {name,escape, typ, pos} => (name, pos)) fields)
    in
        if  dup_bool then err dup_pos "Duplicated names in the record field."
        else ();
        T.RECORD (tfields, ref ())
    end
  | transTy (tenv, A.ArrayTy(tid,pos)) =
    (
      case S.look(tenv, tid) of
	      SOME(ty) => T.ARRAY (ty, ref ())
        | NONE => (err pos ("cannot find array type"^S.name tid); T.BOTTOM)
    )

fun transProg (exp:A.exp) : unit =
  let
      val expty = transExp(E.base_venv, E.base_tenv) exp
  in
      ()
  end


end
