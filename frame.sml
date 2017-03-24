signature FRAME =
sig
  type frame
  type access
  datatype frag = PROC of {body: Tree.stm, frame: frame}
		        | STRING of Temp.label * string
  val newFrame: {name: Temp.label,
		 formals: bool list} -> frame
  val name: frame -> Temp.label
  val formals: frame -> access list
  val allocLocal: frame -> bool -> access
  (* true if if the new variable escapes and needs to go in the frame. false -> can be allocated in register. *)

  val RV : Temp.temp (* as seen by callee*)

  val procEntryExit1 : frame * Tree.stm -> Tree.stm
  val FP : Temp.temp (* frame pointer *)
  val wordSize : int
  val exp : access -> Tree.exp -> Tree.exp
  val externalCall: string * Tree.exp list -> Tree.exp
  (* more...  *)
end


structure MipsFrame : FRAME =
struct

datatype access = InFrame of int |
		          InReg of Temp.temp

(* formals are function parameters *)
(* frame is a data structure holding: *)
(* 1. locations of all formals *)
(* 2. instructions required for "view shift" *)
(* 3. number of locals allocated so far *)
(* 4. the label where the function's machine code is to begin *)
type frame = {name: Temp.label,
			  formals: access list,
              stack_local_count: int ref}
datatype frag = PROC of {body: Tree.stm, frame: frame}
		      | STRING of Temp.label * string
val FP = Temp.newtemp() (* frame pointer *)
val RV = Temp.newtemp() (* return value reg*)
val wordSize = 4 (* ? *)
fun exp access exp =
  (* used to turn a Frame.access into Tree.exp, exp param is the address of the FP*)
  case access of
      InFrame(k) => Tree.MEM(Tree.BINOP(Tree.PLUS, exp, Tree.CONST(k)))
    | InReg(tempReg) => Tree.TEMP(tempReg)
fun procEntryExit1 (frame , body) = body

fun allocLocalImpl stack_local_count true =
  let
      val newLocal = InFrame (~(!stack_local_count * wordSize))
  in
      stack_local_count := !stack_local_count + 1;
      newLocal
  end
  | allocLocalImpl _ false = InReg (Temp.newtemp())

fun newFrame {name, formals = formals_esc} =
  (* formals: true for each escape parameter *)
  let
      val stack_local_count = ref 0
      val formals_access = map (allocLocalImpl stack_local_count) formals_esc
  in
      {name=name,
	   formals=formals_access,
	   stack_local_count=stack_local_count}
  end

fun name {name, formals, stack_local_count} = name

fun formals  {name, formals, stack_local_count} = formals

fun allocLocal {name, formals, stack_local_count} esc = allocLocalImpl stack_local_count esc

fun externalCall (name, param_list) = Tree.CALL(Tree.NAME(Temp.namedlabel(name)), param_list)

fun procEntryExit1 (frame, body) = body
end
