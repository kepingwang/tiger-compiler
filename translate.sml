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

		 
end
