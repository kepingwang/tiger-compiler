structure Semant =
struct

structure S = Symbol
structure T = Types
structure A = Absyn
structure E = Env
val err = ErrorMsg.error

type venv = E.enventry Symbol.table
type tenv = T.ty Symbol.table

structure Trans = Translate

type expty = {exp: Trans.exp, ty: T.ty}

(* IR: TODO FindEscape *)

val loop_nest_level = ref 0

fun say s = TextIO.output (TextIO.stdOut, s ^"\n")

fun has_error () = !ErrorMsg.anyErrors

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

(* IR *)
fun transExp (venv:venv, tenv:tenv, level:Trans.level, break_dest:Trans.exp) =
  let
      fun trexp (A.VarExp(var)) = trvar var
        | trexp (A.NilExp) = {exp=Trans.nil(), ty=T.NIL}
        | trexp (A.IntExp(num)) = {exp=Trans.int(num),ty=T.INT}
        | trexp (A.StringExp(str,pos)) = {exp=Trans.string(str),ty=T.STRING}
        | trexp (A.CallExp{func=func_name,args,pos}) =
          let
              (* trargs(formals: T.ty list, args: A.exp list) : Trans.exp list *)
              (* type check arguments and return Trans.exp list of arguments *)
              fun trargs ([], []) : Trans.exp list = []
                | trargs (formal_head::formal_tail, arg_head::arg_tail) =
                  let
                      val {exp=arg_exp, ty=arg_ty} = trexp arg_head
                      val _ =
                          if (isAssignable (actualTy formal_head) arg_ty)
                          then ()
                          else (err pos ("Function argument types do not match its declaration. Get: " ^ (T.toString arg_ty) ^ " Expected: " ^ (T.toString (actualTy formal_head))))
                      val tailExpList = trargs(formal_tail, arg_tail)
                  in
                      arg_exp::tailExpList
                  end
                | trargs ([], _) = (err pos "Too many arguments."; [])
                | trargs (_ ,[]) = (err pos "Too few arguments."; [])
          in
              case S.look(venv,func_name) of
                  SOME(E.FunEntry{level=dec_level,formals,result}) =>
                  let
                      val arg_exp_list = trargs(formals, args)
                  in
                      if has_error ()
                      then {exp=Trans.errorExp (),ty=T.BOTTOM}
                      else { exp=Trans.call(level,dec_level,arg_exp_list),
                             ty=result
                           }
                  end
                | _ => ( err pos ("function "^S.name func_name^" not defined");
                         {exp=Trans.errorExp (),ty=T.BOTTOM}
                       )
          end
        | trexp (A.OpExp{left,oper,right,pos}) = troper(left,oper,right,pos)
        | trexp (A.RecordExp{fields = field_inst_list, typ = rec_name, pos}) =
          let
              val rec_ty = lookT (tenv, rec_name, pos)
              (* A record instantiation must define the value of all the fields
             and in the same order as in the definition of the record type. *)
              (* tr_record_inst(decList, instList) returns an inst list of Trans.exp *)
              fun tr_record_inst ([], []) = []
                | tr_record_inst ((dec_fname,dec_ty)::dec_tail, (inst_fname, inst_exp, pos)::inst_tail)  =
                  let
                      val {exp, ty} = trexp inst_exp
                      val instTailExpList = tr_record_inst (dec_tail, inst_tail)
                      val check =
                          if (S.name dec_fname) = (S.name inst_fname)
                          then if  isAssignable (actualTy dec_ty) (actualTy ty)
                               then ()
                               else (err pos "Field instantiation expression has a wrong type."; ())
                          else (err pos ("Incorrect field name:" ^ S.name inst_fname); ())
                  in
                      exp::instTailExpList
                  end
                | tr_record_inst ([], _) = (err pos "Too many fields."; [])
                | tr_record_inst (_, []) = (err pos "Too few fields."; [])
          in
              case rec_ty of
                  T.RECORD (field_dec_list, unq) => (
                   {
                     exp=Trans.record(
                         tr_record_inst (field_dec_list, field_inst_list)
                     ),
                     ty=rec_ty
                   }
               )
                | _ => ({exp=Trans.nil(), ty=rec_ty})
          end
        | trexp (A.SeqExp([])) =
          {exp=Trans.nil(),ty=T.UNIT}
        | trexp (A.SeqExp([(exp,pos)])) =
          trexp exp
        | trexp (A.SeqExp((exp,pos)::exp_tail)) =
          let
              val {exp=head_exp, ty=head_ty} = trexp exp
              val {exp=rest_exp, ty=rest_ty} = trexp (A.SeqExp exp_tail)
          in
              {exp=Trans.addToSeq(head_exp, rest_exp), ty=rest_ty}
          end
        | trexp (A.AssignExp{var,exp,pos}) =
          let
              val {exp=left_exp,ty=left_ty} = trvar var
              val {exp=right_exp,ty=right_ty} = trexp exp
          in
              case left_ty of
                  T.INT => (
                   err pos "Cannot assign to loop variable";
                   {exp=Trans.nil(), ty=T.UNIT}
               )
                | _ => (
                    if isAssignable left_ty right_ty
                    then {exp=Trans.assign(left_exp, right_exp),ty=T.UNIT}
                    else (err pos ("The types of operand for operator assignment do not match. left: " ^ (T.toString left_ty) ^" right: " ^ (T.toString right_ty)); {exp=Trans.nil(),ty=T.UNIT})
                )
          end
        | trexp (A.IfExp{test,then',else'=SOME(else'),pos}) =
          (* Note!!!:
   if-then-else return the type of exp2 and exp3
   if-then must return void *)
          let
              val {exp=test_exp, ty=test_ty} = trexp test
              val {exp=then_exp,ty=then_ty} = trexp then'
              val {exp=else_exp,ty=else_ty} = trexp else'
          in
              checkInt(test_ty, pos);
              if (isCompatible then_ty else_ty)
              then {
                  exp=Trans.ifThenElse(test_exp, then_exp, else_exp),
                  ty=findSuperType then_ty else_ty
              }
              else (
                  err pos "Types of then branch and else branch do not match.";
                  {exp=Trans.nil(),ty=T.BOTTOM}
              )
          end
        | trexp (A.IfExp{test,then',else'=NONE,pos}) =
          let
              val {exp=test_exp, ty=test_ty} = trexp test
              val {exp=then_exp,ty=then_ty} = trexp then'
          in
              checkInt(test_ty, pos);
              checkUnit(then_ty, pos);
              {
                exp=Trans.ifThen(test_exp, then_exp),
                ty=T.UNIT
              }
          end
        | trexp (A.WhileExp{test,body,pos}) =
          let
              val {exp=test_exp, ty=test_ty} = trexp test
              val break_dest_new = Trans.newBreakDest()
          in
              loop_nest_level := !loop_nest_level + 1;
              let
                  val {exp=body_exp,ty=body_ty} = transExp (venv,tenv,level,break_dest_new) body
              in
                  loop_nest_level := !loop_nest_level - 1;
                  checkInt(test_ty, pos);
                  checkUnit(body_ty, pos);
                  {exp=Trans.whileExp(test_exp, body_exp, break_dest_new),ty=T.UNIT}
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
              val i_access = Trans.allocLocal level (!escape)
              val venv' = S.enter (venv, id, E.VarEntry {access=i_access, ty=T.INT})
              val i_var_exp = Trans.simpleVar (i_access, level)
              val break_dest_new = Trans.newBreakDest()
          in
              loop_nest_level := !loop_nest_level + 1;
              let
                  val {exp=body_exp, ty=body_ty} = transExp (venv',tenv,level,break_dest_new) body
              in
                  loop_nest_level := !loop_nest_level - 1;
                  checkInt(lo_ty, pos);
                  checkInt(hi_ty, pos);
                  checkUnit(body_ty, pos);
                  if has_error ()
                  then {exp=Trans.errorExp (), ty=T.UNIT}
                  else {exp=Trans.forExp(i_var_exp, lo_exp, hi_exp, body_exp, break_dest), ty=T.UNIT}
              end
          end
        | trexp (A.BreakExp(pos)) = (
            if !loop_nest_level = 0
            then err pos "Break can only be inside a loop."
            else ();
            if has_error()
            then {exp=Trans.errorExp(), ty=T.BOTTOM}
            else {exp=Trans.breakExp(break_dest), ty=T.BOTTOM}
        )
        | trexp (A.LetExp{decs=decs,body,pos}) =
          let
              (* val foldl : ('a * 'b -> 'b) -> 'b -> 'a list -> 'b  *)
              fun combineEnv (
                  dec,
                  {venv=venv,tenv=tenv,init_list=init_list}
              ) =
                let
                    val {venv=venv',tenv=tenv',init_exp=init_exp} =
                        transDec(venv,tenv,level,dec)
                in
                    {venv=venv',tenv=tenv',init_list=init_list @ init_exp}
                end
              val {venv=venv',tenv=tenv',init_list=init_list} = (
                  foldl combineEnv
                        {venv=venv,tenv=tenv,init_list=[]}
                        decs
              )
              val {exp=body_exp, ty=body_ty} = transExp (venv',tenv',level,break_dest) body
              val initiated_body_exp = Trans.initBeforeBody(init_list, body_exp)
          in
              {exp=initiated_body_exp, ty=body_ty}
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
                          T.ARRAY (ele_ty, _) => (
                           if isAssignable (actualTy ele_ty) init_ty
                           then {exp=Trans.array(size_exp, init_exp), ty=arr_ty}
                           else (err pos "Init type doesn't match array dec.";
                                 {exp=Trans.nil(), ty=arr_ty})
                       )
                        | _ => {exp=Trans.nil(), ty=T.BOTTOM}
                  else (err pos "Size type should be Int."; {exp=Trans.nil(), ty=arr_ty})
              else {exp=Trans.nil(), ty=T.BOTTOM}
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
                   {exp=Trans.binop(oper, left_exp, right_exp), ty=T.INT}
               )
               |  (A.EqOp | A.NeqOp ) => (
                   if isCompatible left_ty right_ty
                   then (
                       case left_ty of
                           T.STRING => {exp=Trans.stringRelop (oper, left_exp, right_exp), ty=T.INT}
                         | _ => {exp=Trans.relop(oper, left_exp, right_exp), ty=T.INT}
                   )
                   else (err pos ("Left and right types are not compatible, where left :" ^ (T.toString left_ty) ^ " right :" ^ (T.toString right_ty));
                         {exp=Trans.nil(), ty=T.INT})
               )
               | (A.LtOp | A.LeOp | A.GtOp | A.GeOp) => (
                   if isCompatible left_ty right_ty
                   then case left_ty of
                            (T.STRING | T.INT
                            | T.WINT) => {exp=Trans.relop(oper, left_exp, right_exp), ty=T.INT}
                          | _ => (err pos "Only string or int can be compared for order.";
                                  {exp=Trans.nil(), ty=T.INT})
                   else (err pos ("Lneft and right types are not compatible, where left :" ^ (T.toString left_ty) ^ " right :" ^ (T.toString right_ty));
                         {exp=Trans.nil(), ty=T.INT})
               )
          end
      and trvar (A.SimpleVar(id, pos)) =
          (
            case S.look(venv,id) of
                SOME(E.VarEntry{access, ty=var_ty}) => {
                 exp=Trans.simpleVar(access, level), ty=actualTy var_ty
             }
              | _ => (err pos ("Undefined variable " ^ S.name id);
                      {exp=Trans.nil(), ty=T.BOTTOM})
          )
        | trvar (A.FieldVar(var, id, pos)) =
          let
              val {exp=var_exp, ty=var_ty} = trvar var
              val fieldList =
                  case var_ty of
                      T.RECORD (fieldList, uniq) => fieldList
                    | t => (err pos ("Variable not record, but " ^ (T.toString t)); [])
              fun findFieldTy ([], fname, field_offset) = (
                  err pos ("Field "^S.name fname ^ " doesn't exist.");
                  {exp=Trans.nil(), ty=T.BOTTOM}
              )
                | findFieldTy ((dec_name, dec_ty)::ftail, fname, field_offset) =
                  if dec_name = fname
                  then {exp=Trans.recordField(var_exp, field_offset), ty=actualTy dec_ty}
                  else findFieldTy (ftail, fname, field_offset+1)
          in
              findFieldTy (fieldList, id, 0)
          end
        | trvar (A.SubscriptVar(var, index, pos)) =
          let
              val {exp=var_exp, ty=var_ty} = trvar var
              val {exp=index_exp, ty=index_ty} = trexp index
          in
              checkInt(index_ty, pos);
              checkArray(var_ty, pos);
              case var_ty of
                  T.ARRAY (ele_ty, _) => {
                   exp=Trans.arraySubscript(var_exp, index_exp),
                   ty=actualTy ele_ty
               }
                | _ => {exp=Trans.nil(), ty=T.BOTTOM}
          end
  in
      trexp
  end
(* val {venv=venv',tenv=tenv',level=level',break_dest=break_dest',init_exp=init_exp} = *)
(* transDec(venv,tenv,level,break_dest,dec) *)
and transDec (venv,tenv,level, A.FunctionDec(fundecs)) :
    {venv:venv,tenv:tenv,init_exp:Trans.exp list} =
    let
        fun addFunDec ({name=func_name, params, result, body, pos}, venv) =
          let
              fun findParamType {name=var_name, escape, typ=type_name, pos} = lookT (tenv, type_name, pos)
              fun findEscList {name, escape, typ, pos} = !escape
              val formals_ty = map findParamType params
              val esc_list = map findEscList params
              val result_ty = case result of
                                  SOME(type_name, pos) => lookT (tenv, type_name, pos)
                                | NONE => T.UNIT
              val level' = Trans.newLevel {func_name=(Symbol.name func_name), parent=level, formals=esc_list}
          in
              S.enter (venv, func_name, E.FunEntry {level=level', formals=formals_ty, result=result_ty})
          end
        val venv' = foldl addFunDec venv fundecs
        fun addFunParam (({name=var_name, escape, typ=type_name, pos}, access), venv) =
          S.enter (venv, var_name, E.VarEntry {access=access, ty=lookT (tenv, type_name, pos)})
        fun transFunBody {name, params, result, body, pos} =
          let
              val level =
                  case S.look (venv', name) of
                      SOME(E.FunEntry{level,formals,result}) => level
                    | _ => level (* IR TODO: cannot be reached*)
              val access_list = Trans.formals level
              val venv'' = foldl addFunParam venv' (ListPair.zip(params, access_list))
              val {exp=body_exp, ty=body_ty} = transExp (venv'', tenv, level, Trans.newBreakDest() ) body
              val _ = Trans.procEntryExit {level=level, body=body_exp}
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
        {venv=venv',tenv=tenv, init_exp=[]}
    end
  | transDec (venv,tenv,level, A.VarDec{name,escape,typ=type_option,init,pos}) =
    let
        val {exp=init_exp,ty=init_ty} = transExp (venv,tenv,level,Trans.newBreakDest () ) init
        val access = Trans.allocLocal level (!escape)
        val val_exp = Trans.simpleVar (access, level)
        val init_assign_exp = Trans.assign (val_exp, init_exp)
        val venv' =
            case type_option of
                SOME(type_name, pos) =>
                let
                    val dec_ty = lookT (tenv, type_name, pos)
                    val venv' = S.enter (venv, name, E.VarEntry {access=access, ty=dec_ty})
                in
                    if isAssignable dec_ty init_ty
                    then venv'
                    else (err pos "Init expression has a different type from declaration."; venv')
                end
              | NONE => (
                  case init_ty of
                      T.NIL => (err pos "Record type must be specified when init with Nil.";
                                S.enter (venv, name, E.VarEntry {access=access, ty=T.BOTTOM}))
                    | T.INT => S.enter (venv, name, E.VarEntry {access=access, ty=T.WINT})
                    | _ => S.enter (venv, name, E.VarEntry {access=access, ty=init_ty})
              )
    in
        {venv=venv',tenv=tenv, init_exp=[init_assign_exp] }
    end
  | transDec (venv,tenv,level,A.TypeDec(decList)) =
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
        {venv=venv, tenv=tenv', init_exp=[]}
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

fun transProg (exp:A.exp) : Trans.frag list =
  let
      (* TODO outermost should contain system functions? *)
      val _ = FindEscape.findEscape exp
      val outermost = Trans.outermost
      val {exp=body_exp, ty=_} = transExp(E.base_venv, E.base_tenv, outermost, Trans.newBreakDest() ) exp
      val _ = Trans.procEntryExit {level=outermost, body=body_exp}
  in
      Trans.getResult()
  end

end
