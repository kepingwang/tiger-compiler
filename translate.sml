signature TRANSLATE =
sig
  type level
  type access (* not the same as Frame.access *) (* access of a var*)

  val outermost : level
  val newLevel : { (* newLevel calls newFrame *)
    (* semant.sml only knows about level, doesn't know about frame *)
    (* when calling Frame.newFrame, Translate passes static link as
     an extra escaped parameter. Frame.newFrame(label, true::formals) *)
    parent: level,
    formals: bool list
  } -> level
  val formals : level -> access list
  (* get the formals without the static link *)
  val allocLocal : level -> bool -> access


  type exp
  val transNil: unit->exp
  val transInt: int->exp
  val transString: string->exp
  val transIfThen: exp * exp -> exp
  val transIfThenElse: exp * exp * exp -> exp
  val transNewBreakDest: unit -> exp
  val transWhile: exp * exp * exp -> exp
  val transFor: exp * exp * exp * exp * exp -> exp
  val simpleVar : (access * level) -> exp
  val procEntryExit : {level: level, body: exp} -> unit
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
fun newLevel {parent, formals} =
  (* pass static link as an extra element *)
  LEVEL {parent=parent,
         frame=Frame.newFrame {name=Temp.newlabel(), formals=true::formals},
         uniq=ref ()}
val outermost = OUTERMOST {frame=Frame.newFrame  {name = Temp.newlabel(), formals = [true] } }
fun levelName level = Frame.name (getFrame level)
structure A = Absyn
structure T = Tree
(* Translate from Absyn.exp to exp *)
datatype exp = Ex of Tree.exp
	         | Nx of Tree.stm
	         | Cx of Temp.label * Temp.label -> Tree.stm

fun seq [] = Tree.SEQ (Tree.LABEL (Temp.newlabel() ), Tree.LABEL (Temp.newlabel()))
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
fun unCx (Ex e) = (fn (t_label, f_label) => T.CJUMP (T.NE, e, T.CONST 0, t_label, f_label))
  | unCx (Nx s) = (fn (t_label, f_label) => seq [s, T.JUMP (T.NAME f_label, [f_label])])
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
fun simpleVar ( (dec_level, access), use_level) = Ex (Frame.exp access (
                                                           traceStaticLink (dec_level, use_level, T.TEMP Frame.FP)
                                                       )
                                                     )

fun allocLocal level esc =
  let
      val frame = getFrame level
  in
      (level, Frame.allocLocal frame esc)
  end
fun transNil() = Ex (Tree.CONST 0)
fun transInt number = Ex (Tree.CONST number)
fun transString str =
  let
      val str_label = Temp.newlabel()
  in
      ( fragList := Frame.STRING (str_label, str) :: !fragList;
        Ex (Tree.NAME str_label)
      )
  end
fun transCall (call_level, dec_level, exp_list) =
  let
      val func_label = levelName dec_level
      val arg_list = map unEx exp_list
  in
      Ex (Tree.CALL (Tree.NAME func_label, traceStaticLink(parentLevel dec_level, call_level, T.TEMP Frame.FP) :: arg_list))
  end


fun transAssign (left_exp, right_exp) = Nx (Tree.MOVE (unEx left_exp, unEx right_exp) )

fun transRecord field_exps =
  let
      val n = List.length field_exps
      val r = Temp.newtemp()
      val (init_seq, _) = foldl (fn (exp, (s_list, offset)) => (
                                    unNx (transAssign ((Ex (Tree.MEM
                                                           (T.BINOP
                                                                (T.PLUS, T.TEMP r, T.CONST (offset * Frame.wordSize)
                                                                )
                                                           ))
                                                       ),
                                                       exp
                                                      )
                                         ) :: s_list, offset + 1
                                )) ([], 0) field_exps
      val all_seq = Tree.MOVE (T.TEMP r, Frame.externalCall ("malloc", [T.CONST (n * Frame.wordSize)])) :: init_seq
  in
      Tree.ESEQ (seq all_seq, T.TEMP r)
  end

fun procEntryExit {level, body} =
  let
      val frame = getFrame level
      val fixed_body = Frame.procEntryExit1 (frame, unNx body)
  in
      fragList := Frame.PROC {body=fixed_body, frame = frame} :: !fragList
  end

fun transIfThen (test, exp1) =
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
fun transIfThenElse (test, exp1, exp2) =
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
                         T.LABEL tlb,
                         T.MOVE (T.TEMP result ,t_branch_exp),
                         T.JUMP (T.NAME join_lb, [join_lb]),
                         T.LABEL flb,
                         T.MOVE (T.TEMP result ,f_branch_exp),
                         T.LABEL join_lb
                     ],
                    T.TEMP result
                   )
           )
    end

fun transNewBreakDest () =  Nx (T.LABEL (Temp.newlabel () ))
fun transWhile (test, body, done_lb) =
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
               body_stmt,
               T.JUMP (T.NAME start_lb, [start_lb]),
               T.LABEL done_lb
           ]
         )
  end
fun transFor (i_exp, lo, hi, body, done_lb) =
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
               body_stmt,
               inc_stmt,
               T.JUMP (T.NAME start_lb, [start_lb]),
               T.LABEL done_lb
         ])
  end
end
