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
    name: Temp.label,
    formals: bool list
  } -> level
  val formals : level -> access list
  (* get the formals without the static link *)
  val allocLocal : level -> bool -> access

  val transNil: unit->exp
  val transInt: int->exp
  val transString: string->exp 


  type exp
  val simpleVar : (access * level) -> exp
  val procEntryExit : {level: level, body: exp} -> unit
  structure Frame : FRAME
  type frag
  val getResult : unit -> Frame.frag list
end

structure Translate : TRANSLATE =
struct
type level = {frame, unit ref} (* ? *)
(* level needs to be kept track of *)
type access = level * Frame.access
(* Frame shouldn't know anything about static links, it is the responsibility of Translate. *)
fun newLevel {parent, name, formals} =
  (* pass static link as an extra element *)
  {Frame.newFrame {name, true::formals}, unique = ref () }
val levelName : level -> Temp.label
val getFrame : level -> frame
val parentLevel : level -> level
structure A = Absyn
structure T = Tree
(* Translate from Absyn.exp to exp *)
datatype exp = Ex of Tree.exp
	     | Nx of Tree.stm
	     | Cx of Temp.label * Temp.label -> Tree.stm

type frag = Frame.frag
val fragList = ref []
fun getResult () = !fragList
fun traceStaticLink (dec_level, curr_level, exp) =
  if dec_level = curr_level
  then exp
  else traceStaticLink (dec_level, parentLevel curr_level,
                        Frame.exp (Frame.getStaticLink (getFrame curr_level)) exp) (*TREE.MEM (...) *)

fun getLevelFP level = T.TEMP(Frame.FP) (* ??? *)
fun simpleVar ( (_, Frame.InReg t), _) = Ex (Tree.TEMP t)
  | simpleVar ( (dec_level, access), use_level) = Ex (Frame.exp access traceStaticLink(dec_level, use_level, T.TEMP Frame.FP))
  (* this access is first generated from Translate.allocLocal *)
  Frame.exp access (getLevelFP level)
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
      Ex (Tree.CALL (Tree.NAME func_label, traceStaticLink(parentLevel dec_level, curr_level, T.TEMP Frame.FP) :: arg_list))
  end

fun addToSeq (exp1, exp2) =
  Nx (Tree.SEQ (unNx exp1, unNx exp2))

fun seq [s1, s2] = Tree.SEQ (s1, s2)
  | seq head :: tail = Tree.SEQ(head, seq tail)

fun transAssign (left_exp, right_exp) = Nx (Tree.MOVE (unEx left_exp, unEx right_exp) )

fun transRecord fieldExps =
  let
      val n = List.length fieldExps
      val r = Temp.newtemp()
      val (init_seq, _) = foldl fn (exp, (s_list, offset)) => (
                               unNx (transAssign ((Ex Tree.MEM
                                                      (T.BINOP
                                                           (T.PLUS, T.TEMP r, CONST (offset * Frame.wordSize)
                                                           )
                                                      )
                                                  ),
                                                  unEx exp
                                                 )
                                    ) :: s_list, offset + 1
                                )
      val all_seq = Tree.MOVE (Tree.TEMP r, Tree.CALL (Tree.NAME (Temp.namedlabel "malloc"), CONST (n * Frame.wordSize))) :: init_seq
  in
      Tree.ESEQ (seq all_seq, Tree.TEMP r)
  end

fun transFun fundec : Tree.stm = (* build everything to a Tree.stm *)
  let
  (* Prologue *)
  (* 1. assembly specific pseudo-instructions, announcing function begin *)
  (* 2. label for function name *)
  (* 3. an instruction to adjust the stack pointer (to allocate a new frame) *)
  (* 4. instructions to save "escaping" args into the frame *)
  (*   and to move non-escaping args into fresh temp registers. *)
  (* 5. store instructions to save any callee-save registers -
       including the return address register - used within the function. *)
  (* Body *)
  (* 6. the function body. Ex *)
  val body = Ex(#body fundec)
  (* Epilogue *)
  (* 7. an instruction to move the return value to the register reserved *)
  val out = T.MOVE(Frame.RV, body)
  (* 8. load instructions to restore the callee-save registers *)
  (* 9. instruction to reset the stack pointer *)
  (* 10. a return instruction (JUMP to the return address) *)
  (* 11. pseudo-instructions, as needed, to announce function end *)
  in
    ()
  end
end
