signature TRANSLATE =
sig
  type level
  type access (* not the same as Frame.access*)

  val outermost : level
  val newLevel : {
    parent: level,
    name: Temp.label,
    formals: bool list
  } -> level
  val formals : level -> access list
  val allocLocal : level -> bool -> access

  type exp
  val unEx : exp -> Tree.exp
  val unNx : exp -> Tree.stm
  val unCx : exp -> (Temp.label * Temp.label) -> Tree.stm
  val simpleVar : (access * level) -> exp
  val procEntryExit : {level: level, body: exp} -> unit
						     
  structure Frame : FRAME
  type frag
  val getResult : unit -> Frame.frag list
				     
end

structure Translate : TRANSLATE =
struct
type level = frame (* ? *)
(* level needs to be kept track of *)
type access = level * Frame.access
(* Frame shouldn't know anything about static links, it is the responsibility of Translate. *)
fun newLevel {parent, name, formals} =
  (* pass static link as an extra element *)
  Frame.newFrame {name, true::formals}


structure A = Absyn
structure T = Tree
(* Translate from Absyn.exp to exp *)
datatype exp = Ex of Tree.exp
	     | Nx of Tree.stm
	     | Cx of Temp.label * Temp.label -> Tree.stm

type frag = Frame.frag
val fragList = []
fun getResult () = fragList

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
