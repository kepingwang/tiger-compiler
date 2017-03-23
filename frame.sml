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
  val getStaticLink: frame -> access
  (* true if if the new variable escapes and needs to go in the frame. false -> can be allocated in register. *)

  val RV : Temp.temp (* as seen by callee*)

  val procEntryExit1 : frame * Tree.stm -> Tree.stm
  val FP : Temp.temp (* frame pointer *)
  val wordSize : int
  val exp : access -> Tree.exp -> Tree.exp
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
val wordSize = 8 (* ? *)
fun exp access exp =
  (* used to turn a Frame.access into Tree.exp, exp param is the address of the FP*)
  case access of
      InFrame(k) => Tree.MEM(Tree.BINOP(Tree.PLUS, exp, Tree.CONST(k)))
    | InReg(tempReg) => Tree.TEMP(tempReg)
fun procEntryExit1 (frame , body) = body

fun allocLocalImpl stack_local_count true =
  let
      val newLocal = InFrame (!stack_local_count * wordSize)
  in
      stack_local_count := !stack_local_count + 1;
      newLocal
  end
  | allocLocalImpl _ false = InReg (Temp.newtemp())

fun getStaticLink frame = InFrame(0)
fun newFrame {name, formals = formals_esc} =
  (* formals: true for each escape parameter *)
  let
      val stack_local_count = ref 1 (*1 reserved for static link*)
      fun alloc_formals (reg_avail, esc::esc_tail) =
        if esc orelse reg_avail = 0
        then (allocLocalImpl stack_local_count esc) :: alloc_formals (reg_avail, esc_tail)
        else InReg (Temp.newtemp()) :: alloc_formals (reg_avail - 1, esc_tail)
        | alloc_formals (_, []) = []
      val formals_access = alloc_formals (4, formals_esc)
  in
      {name=name,
	   formals=formals_access,
	   stack_local_count=stack_local_count}
  end

fun name {name, formals, stack_local_count} = name

fun formals  {name, formals, stack_local_count} = formals

fun allocLocal {name, formals, stack_local_count} esc = allocLocalImpl stack_local_count esc


end

