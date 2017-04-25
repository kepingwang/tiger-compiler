signature TRANSLATE =
sig
  type level
  type access (* not the same as Frame.access *) (* access of a var*)

  val outermost : level
  val newLevel : { (* newLevel calls newFrame *)
    (* semant.sml only knows about level, doesn't know about frame *)
    (* when calling Frame.newFrame, Translate passes static link as
     an extra escaped parameter. Frame.newFrame(label, true::formals) *)
      func_name: string,
      parent: level,
      formals: bool list
  } -> level
  val formals : level -> access list
  (* get the formals without the static link *)
  val allocLocal : level -> bool -> access


  type exp
  type Aexp
  val nil: unit->exp
  val int: int->exp
  val string: string->exp
  val call: level * level * exp list -> exp
  val assign: exp * exp -> exp
  val record: exp list -> exp
  val breakExp: exp -> exp
  val recordField: exp * int -> exp
  val arraySubscript: exp * exp -> exp
  val initBeforeBody: exp list * exp -> exp
  val array: exp * exp -> exp
  val ifThen: exp * exp -> exp
  val ifThenElse: exp * exp * exp -> exp
  val newBreakDest: unit -> exp
  val whileExp: exp * exp * exp -> exp
  val forExp: exp * exp * exp * exp * exp -> exp
  val simpleVar : (access * level) -> exp
  val procEntryExit : {level: level, body: exp} -> unit
  val stringRelop: Aexp * exp * exp -> exp
  val relop: Aexp * exp * exp -> exp
  val binop: Aexp * exp * exp -> exp
  val addToSeq: exp * exp -> exp
  val errorExp: unit -> exp
  structure Frame : FRAME
  type frag
  val getResult : unit -> Frame.frag list
end

structure Translate : TRANSLATE =
struct
structure Frame : FRAME = MipsFrame
datatype level = LEVEL of {parent: level, frame: Frame.frame, uniq: unit ref}
               | OUTERMOST of {frame: Frame.frame}(* ? *)
(* level needs to be kept track of *)
type access = level * Frame.access
type frag = Frame.frag
(* Frame shouldn't know anything about static links, it is the responsibility of Translate. *)
fun getFrame (LEVEL {frame, ...}) = frame
  | getFrame (OUTERMOST {frame, ...}) = frame
fun parentLevel (LEVEL {parent, ...}) = parent
  | parentLevel outerlevel = outerlevel
fun newLevel {func_name, parent, formals} =
  (* pass static link as an extra element *)
  LEVEL {parent=parent,
         frame=Frame.newFrame {func_name = func_name, name=Temp.newlabel(), formals=true::formals},
         uniq=ref ()}
fun levelName level = Frame.name (getFrame level)
val outermost = OUTERMOST {frame=Frame.newFrame {func_name="main", name = Temp.mainlabel, formals = [true] } }
structure A = Absyn
type Aexp = A.oper
structure T = Tree
(* Translate from Absyn.exp to exp *)
datatype exp = Ex of Tree.exp
	         | Nx of Tree.stm
	         | Cx of Temp.label * Temp.label -> Tree.stm

fun seq [] = Tree.LABEL (Temp.newlabel() )
  | seq [s1] = s1
  | seq [s1, s2] = Tree.SEQ (s1, s2)
  | seq (head :: tail) = Tree.SEQ(head, seq tail)
fun unEx (Ex e) = e
  | unEx (Nx s) = T.ESEQ(s, T.CONST 0)
  | unEx (Cx c) =
    let
        val result = Temp.newtemp ()
        val t_label = Temp.newlabel ()
        val f_label = Temp.newlabel ()
    in
        T.ESEQ(seq [
                    T.MOVE (T.TEMP result, T.CONST 1),
                    c (t_label, f_label),
                    T.LABEL f_label,
                    T.MOVE(T.TEMP result, T.CONST 0),
                    T.LABEL t_label
                ],
               T.TEMP result)
    end

fun unNx (Ex e) = T.EXP e
  | unNx (Nx s) = s
  | unNx (Cx c) =
    let
        val label = Temp.newlabel ()
    in
        seq [
            c (label, label),
            T.LABEL label
        ]
    end

(*Nx case will never occur.
 *We can improve the following by consider unCx(CONST 0/1)
 *)
exception Impossible
fun unCx (Ex e) = (fn (t_label, f_label) => T.CJUMP (T.NE, e, T.CONST 0, t_label, f_label))
  | unCx (Nx s) = (fn (t_label, f_label) => raise Impossible)
  | unCx (Cx c) = c

val fragList : frag list ref = ref []
fun getResult () = !fragList
fun getStaticLink level =
  let
      val static_link::_ = Frame.formals (getFrame level)
  in
      static_link
  end
fun traceStaticLink (dec_level, curr_level, exp) =
  (*return the address of FP of dec_level*)
  if dec_level = curr_level
  then exp
  else traceStaticLink (dec_level, parentLevel curr_level,
                        Frame.exp (getStaticLink curr_level) exp) (*TREE.MEM (...) *)

fun formals level =
  (case level of
       LEVEL {frame={formals = formals, ...}, ...} =>
       let
           val _ :: user_formals = formals
           val formals_access = map (fn x => (level, x)) user_formals
       in
           formals_access
       end
     | OUTERMOST _ => []
  )
fun errorExp () = Ex (T.CONST 0)
fun simpleVar ( (dec_level, access), use_level) = Ex (Frame.exp access (
                                                           traceStaticLink (dec_level, use_level, T.TEMP Frame.FP)
                                                       )
                                                     )
fun addToSeq (exp1, exp2) = Ex (Tree.ESEQ (unNx exp1, unEx exp2))
fun allocLocal level esc =
  let
      val frame = getFrame level
  in
      (level, Frame.allocLocal frame esc)
  end
fun nil() = Ex (Tree.CONST 0)
fun int number = Ex (Tree.CONST number)
fun string str =
  let
      val str_label = Temp.newlabel()
  in
      ( fragList := Frame.STRING (str_label, str) :: !fragList;
        Ex (Tree.NAME str_label)
      )
  end
fun call (call_level, dec_level, exp_list) =
  let
      val func_label = levelName dec_level
      val arg_list = map unEx exp_list
  in
      Ex (Tree.CALL (Tree.NAME func_label, traceStaticLink(parentLevel dec_level, call_level, T.TEMP Frame.FP) :: arg_list))
  end


fun assign (left_exp, right_exp) = Nx (Tree.MOVE (unEx left_exp, unEx right_exp) )

fun record field_exps =
  let
      val n = List.length field_exps
      val r = Temp.newtemp()
      val (init_seq, _) = foldl (fn (exp, (s_list, offset)) => (
                                     unNx (assign ((Ex (Tree.MEM
                                                            (if offset = 0 then
                                                                T.TEMP r
                                                            else
                                                                T.BINOP
                                                                    (T.PLUS, T.TEMP r, T.CONST (offset * Frame.wordSize)
                                                                    )
                                                            )
                                                       )
                                                   ),
                                                       exp
                                                      )
                                         ) :: s_list, offset + 1
                                )) ([], 0) field_exps
      val all_seq = Tree.MOVE (T.TEMP r, Frame.externalCall ("malloc", [T.CONST (n * Frame.wordSize)])) :: init_seq
  in
      Ex (Tree.ESEQ (seq all_seq, T.TEMP r))
  end

fun recordField (var_exp, offset) = Ex (T.MEM (
                                             if offset = 0 then
                                                 unEx var_exp
                                             else
                                                 T.BINOP (T.PLUS, unEx var_exp, T.CONST (offset * Frame.wordSize)))
                                       )

fun breakExp done_lb =
  let
      val (T.LABEL done_lb) = unNx done_lb
  in
      Nx (T.JUMP (T.NAME done_lb, [done_lb]))
  end

fun initBeforeBody (init_exp_list, body_exp) =
  let
      val seq_list = map unNx init_exp_list
      val body_exp = unEx body_exp
  in
      Ex (T.ESEQ (seq seq_list, body_exp))
  end

(*length is added by initArray*)
fun array (size_exp, init_exp) =
  Ex (
      Frame.externalCall ("initArray", [unEx size_exp, unEx init_exp])
  )

fun arraySubscript (var_exp, index_exp) =
  let
      val var_addr_reg = Temp.newtemp()
      val index_reg = Temp.newtemp()
      val assign_addr_stmt = T.MOVE(T.TEMP var_addr_reg, unEx var_exp)
      val assign_index_stmt = T.MOVE(T.TEMP index_reg, unEx index_exp)
      val get_size_exp = T.MEM(T.BINOP(T.MINUS, T.TEMP var_addr_reg, T.CONST 1))
      val valid_lb = Temp.newlabel()
      val invalid_lb = Temp.newlabel()
      val check_stmt = T.CJUMP (T.LT, T.TEMP index_reg, get_size_exp, valid_lb, invalid_lb)
      val exit_stmt = T.EXP (Frame.externalCall ("exit", [T.CONST 1]))
      val get_exp = T.MEM (T.BINOP (T.PLUS, T.TEMP var_addr_reg, T.TEMP index_reg))
  in
      Ex (T.ESEQ (
      seq[
          assign_addr_stmt,
          assign_index_stmt,
          check_stmt,
          T.LABEL invalid_lb,
          exit_stmt,
          T.LABEL valid_lb
      ],
      get_exp
      ))
  end

structure A = Absyn

fun binop (A.PlusOp, Ex(T.CONST 0), right_exp) = Ex ( unEx right_exp)
  | binop (A.PlusOp, left_exp, Ex(T.CONST 0)) = Ex (unEx left_exp)
  | binop (A_oper, left_exp, right_exp) =
  let
      val left_exp = unEx left_exp
      val right_exp = unEx right_exp
  in
      case A_oper of
          A.PlusOp => Ex (T.BINOP (T.PLUS, left_exp, right_exp))
        | A.MinusOp => Ex (T.BINOP (T.MINUS, left_exp, right_exp))
        | A.TimesOp => Ex (T.BINOP (T.MUL, left_exp, right_exp))
        | A.DivideOp => Ex (T.BINOP (T.DIV, left_exp, right_exp))
  end

fun stringRelop (Aoper, left_exp, right_exp) =
  case Aoper of
      A.EqOp => Ex (Frame.externalCall ("stringEqual", [unEx left_exp, unEx right_exp]))
    | A.NeqOp => Ex (T.BINOP(T.MINUS, T.CONST 1, Frame.externalCall ("stringEqual", [unEx left_exp, unEx right_exp])))
    | _ => Ex (T.CONST 0)
fun relop (A_oper, left_exp, right_exp) =
  let
      val T_relop =
	      case A_oper of
	          A.EqOp => T.EQ
	        | A.NeqOp => T.NE
	        | A.LtOp => T.LT
	        | A.LeOp => T.LE
	        | A.GtOp => T.GT
	        | A.GeOp => T.GE
      val left_exp = unEx left_exp
      val right_exp = unEx right_exp
      fun cjump_fun (t_label, f_label) =
		    T.CJUMP (T_relop, left_exp, right_exp, t_label, f_label)
  in
    Cx cjump_fun
  end

fun ifThen (test, exp1) =
  let
      val tlb = Temp.newlabel()
      val flb =Temp.newlabel()
      val jump_stmt = (unCx test) (tlb, flb)
      val body_stmt = unNx exp1
  in
      Nx (seq [
          jump_stmt,
          T.LABEL tlb,
          body_stmt,
          T.LABEL flb
      ])
  end
fun ifThenElse (test, exp1, exp2) =
    let
        val tlb = Temp.newlabel ()
        val flb =Temp.newlabel ()
        val join_lb =Temp.newlabel ()
        val result = Temp.newtemp ()
        val jump_stmt = (unCx test) (tlb, flb)
        val t_branch_exp = unEx exp1
        val f_branch_exp = unEx exp2
    in
        Ex (T.ESEQ (seq [
                         jump_stmt,
                         T.LABEL flb,
                         T.MOVE (T.TEMP result ,f_branch_exp),
                         T.JUMP (T.NAME join_lb, [join_lb]),
                         T.LABEL tlb,
                         T.MOVE (T.TEMP result ,t_branch_exp),
                         T.LABEL join_lb
                     ],
                    T.TEMP result
                   )
           )
    end

fun newBreakDest () =  Nx (T.LABEL (Temp.newlabel () ))
fun whileExp (test, body, done_lb) =
  let
      val (T.LABEL done_lb) = unNx done_lb
      val start_lb = Temp.newlabel ()
      val cont_lb = Temp.newlabel ()
      val jump_stmt = (unCx test) (cont_lb, done_lb)
      val body_stmt = unNx body
  in
      Nx (seq [
               T.LABEL start_lb,
               jump_stmt,
               T.LABEL cont_lb,
               body_stmt,
               T.JUMP (T.NAME start_lb, [start_lb]),
               T.LABEL done_lb
           ]
         )
  end
fun forExp (i_exp, lo, hi, body, done_lb) =
  let
      val (T.LABEL done_lb) = unNx done_lb
      val limit = Temp.newtemp()
      val i_exp = unEx i_exp
      val start_lb = Temp.newlabel ()
      val cont_lb = Temp.newlabel ()
      val jump_stmt = T.CJUMP (T.LE, i_exp, T.TEMP limit , cont_lb, done_lb)
      val inc_stmt = T.MOVE(i_exp, T.BINOP (T.PLUS, i_exp, T.CONST 1))
      val body_stmt = unNx body
  in
      Nx (seq [
               T.MOVE (i_exp, unEx lo),
               T.MOVE (T.TEMP limit, unEx hi),
               T.LABEL start_lb,
               jump_stmt,
               T.LABEL cont_lb,
               body_stmt,
               inc_stmt,
               T.JUMP (T.NAME start_lb, [start_lb]),
               T.LABEL done_lb
         ])
  end

fun procEntryExit {level, body} =
  let
      val frame = getFrame level
      val body_with_return = T.MOVE (T.TEMP Frame.RV, unEx body)
      val fixed_body = Frame.procEntryExit1 (frame, body_with_return)
  in
      fragList := Frame.PROC {body=fixed_body, frame = frame} :: !fragList
  end
end
