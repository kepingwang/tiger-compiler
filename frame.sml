signature FRAME =
sig
  type frame
  type access
  val newFrame: {name: Temp.label,
		 formals: bool list} -> frame
  val name: frame -> Temp.label
  val formals: frame -> access list
  val allocLocal: frame -> bool -> access
  (* true if if the new variable escapes and needs to go in the frame. false -> can be allocated in register. *)

  val RV : Temp.temp (* as seen by callee*)

  datatype frag = PROC of {body: Tree.stm, frame: frame}
		| STRING of Temp.label * string
  val procEntryExit1 : frame * Tree.stm -> Tree.stm
  val FP : Temp.temp (* frame pointer *)
  val wordSize : int
  val exp : access -> Tree.exp -> Tree.exp
  (* more...  *)
end				    

structure Frame : FRAME = MipsFrame
			    
structure MipsFrame : FRAME =
struct

type T = Tree : TREE

(* formals are function parameters *)
(* frame is a data structure holding: *)
(* 1. locations of all formals *)
(* 2. instructions required for "view shift" *)
(* 3. number of locals allocated so far *)
(* 4. the label where the function's machine code is to begin *)
datatype frame = FrameDict of {name: Temp.label,
			       formals: access list,
			       locals: access list}
				(* TODO: frame pointer, stack pointer, return address...*)

datatype access = InFrame of int |
		  InReg of Temp.temp

fun allocFormalImpl escape : access =
  (* TODO alloc formal *)
  if escape then InFrame 8 (* where? *)
  else InReg Temp.newtemp()

fun allocLocalImpl escape : access = (* TODO*)
  if escape then InFrame 8
  else InReg Temp.newtemp()
	     
fun newFrame {name: nameLabel,
	      formals: escList} =
  (* formals: true for each escape parameter *)
  let
    paramLocs = map allocFormalImpl escList 
  in
    FrameDict {name: nameLabel,
	       formals: paramLocs,
	       locals: []}
  end

fun name FrameDict{name, _, _} = name

fun formals FrameDict{_, formals, _} = formals

fun allocLocal FrameDict{name, formals, locals} esc =
  (* order of locals? *)
  let
    newLocal = allocLocalImpl esc
  in
    FrameDict {name, formals, newLocal::locals}
  end

val FP = Temp.newtemp() (* frame pointer *)
val wordSize = 8 (* ? *)
fun exp access (T.TEMP(fp)) =
  (* used to turn a Frame.access into Tree.exp*)
  case access of
      InFrame(k) => T.MEM(T.BINOP(T.PLUS, T.TEMP(FP), T.CONST(k))
    | InReg(tempReg) => T.TEMP(tempReg)
						   
    
end
