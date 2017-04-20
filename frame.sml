signature FRAME =
sig
  type frame
  type access
  type register = string
  datatype frag = PROC of {body: Tree.stm, frame: frame}
		        | STRING of Temp.label * string
  val newFrame: {func_name:string,
                 name: Temp.label,
		         formals: bool list} -> frame
  val name: frame -> Temp.label
  val func_name: frame -> string
  val formals: frame -> access list
  val allocLocal: frame -> bool -> access
  (* true if if the new variable escapes and needs to go in the frame. false -> can be allocated in register. *)

  val ZERO : Temp.temp (* as seen by callee*)
  val RV : Temp.temp (* as seen by callee*)
  val RA : Temp.temp (* as seen by callee*)
  val FP : Temp.temp (* frame pointer *)
  val SP : Temp.temp (* frame pointer *)
  val ARGS : Temp.temp list
  val callersaves : Temp.temp list
  val calleesaves : Temp.temp list

  val tempMap : register Temp.Map.map
  val registers: register list

  val procEntryExit1 : frame * Tree.stm -> Tree.stm
  val procEntryExit2 : frame * Assem.instr list -> Assem.instr list
  val procEntryExit3 : frame * Assem.instr list -> {prolog:string, body:Assem.instr list, epilog : string}
  val wordSize : int
  val exp : access -> Tree.exp -> Tree.exp
  val externalCall: string * Tree.exp list -> Tree.exp
  (* more...  *)
  val register_name: Temp.temp -> string
end


structure MipsFrame : FRAME =
struct

datatype access = InFrame of int |
		          InReg of Temp.temp
type register = string

(* formals are function parameters *)
(* frame is a data structure holding: *)
(* 1. locations of all formals *)
(* 2. instructions required for "view shift" *)
(* 3. number of locals allocated so far *)
(* 4. the label where the function's machine code is to begin *)
type frame = {func_name:string,
              name: Temp.label,
			  formals: access list,
              stack_local_count: int ref}
datatype frag = PROC of {body: Tree.stm, frame: frame}
		      | STRING of Temp.label * string
val ZERO = Temp.newtemp()
val AT = Temp.newtemp()
val RV = Temp.newtemp()
val v1 = Temp.newtemp()
val ARGS = [Temp.newtemp(), Temp.newtemp(), Temp.newtemp(), Temp.newtemp()]
val tRegs = [Temp.newtemp(), Temp.newtemp(), Temp.newtemp(), Temp.newtemp(),
             Temp.newtemp(), Temp.newtemp(), Temp.newtemp(), Temp.newtemp()]
val sRegs = [Temp.newtemp(), Temp.newtemp(), Temp.newtemp(), Temp.newtemp(),
             Temp.newtemp(), Temp.newtemp(), Temp.newtemp(), Temp.newtemp()]
val t8 = Temp.newtemp()
val t9 = Temp.newtemp()
val k0 = Temp.newtemp()
val k1 = Temp.newtemp()
val GP = Temp.newtemp()
val SP = Temp.newtemp()
val FP = Temp.newtemp()
val RA = Temp.newtemp()

val specialRegs = [
  ZERO, AT, RV, SP, FP, RA
]
val ARGS = ARGS
val callersaves = tRegs @ [v1, t8, t9, k0, k1, GP]
val calleesaves = sRegs

structure TMap = Temp.Map
val tempMap = TMap.empty
val tempMap = TMap.insert (tempMap, ZERO, "zero")
val tempMap = TMap.insert (tempMap, AT, "at")
val tempMap = TMap.insert (tempMap, RV, "v0")
val tempMap = TMap.insert (tempMap, v1, "v1")
val (tempMap, _) = foldl (fn (temp, (map, num)) =>
                        (TMap.insert(map, temp, "a"^(Int.toString num)), num+1))
                    (tempMap, 0)
                    ARGS
val (tempMap, _) = foldl (fn (temp, (map, num)) =>
                        (TMap.insert (map, temp, "t"^(Int.toString num)), num+1))
                    (tempMap, 0)
                    tRegs
val (tempMap, _) = foldl (fn (temp, (map, num)) =>
                        (TMap.insert(map, temp, "s"^(Int.toString num)), num+1))
                    (tempMap, 0)
                    sRegs
val tempMap = TMap.insert (tempMap, t8, "t8")
val tempMap = TMap.insert (tempMap, t9, "t9")
val tempMap = TMap.insert (tempMap, k0, "k0")
val tempMap = TMap.insert (tempMap, k1, "k1")
val tempMap = TMap.insert (tempMap, GP, "gp")
val tempMap = TMap.insert (tempMap, SP, "sp")
val tempMap = TMap.insert (tempMap, FP, "fp")
val tempMap = TMap.insert (tempMap, RA, "ra")




(* registers not used: zero, at *)
val registers = [ "zero",
                  "v0", "v1", (* return values *)
                 "a0", "a1", "a2", "a3", (* function parameters *)
                 "t0", "t1", "t2", "t3", "t4", "t5", "t6", "t7", (* callersave *)
                 "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", (* calleesave, function variables *)
                 "t8", "t9", (* two more temporary variables *)
                 "k0", "k1", (* kernel use variables, may change unexpectedly *)
                 "gp", (* global pointer *)
                 "sp", (* stack pointer *)
                 "fp", (* frame pointer or subroutine variable? x*)
                 "ra" (* return address of the last subroutine call *)
                ]
fun register_name t = if t = RV then "$v0"
                      else if t=RA then "$ra"
                      else if t=FP then "$fp"
                      else if t=SP then "$sp"
                      else if t=ZERO then "$r0"
                      else if t=List.nth (ARGS, 0) then "$a0"
                      else if t=List.nth (ARGS, 1) then "$a1"
                      else if t=List.nth (ARGS, 2) then "$a2"
                      else if t=List.nth (ARGS, 3) then "$a3"
                      else Temp.makestring t
val wordSize = 4 (* ? *)
fun func_name {func_name, name, formals, stack_local_count} = func_name
fun exp access exp =
  (* used to turn a Frame.access into Tree.exp, exp param is the address of the FP*)
  case access of
      InFrame(k) => Tree.MEM(Tree.BINOP(Tree.PLUS, exp, Tree.CONST(k)))
    | InReg(tempReg) => Tree.TEMP(tempReg)
fun procEntryExit1 (frame , body) = body

fun allocLocalImpl stack_local_count true =
  let
      val newLocal = InFrame ((!stack_local_count * wordSize))
  in
      stack_local_count := !stack_local_count + 1;
      newLocal
  end
  | allocLocalImpl stack_local_count false = (stack_local_count := !stack_local_count+1;  InReg (Temp.newtemp()))

fun newFrame {func_name, name, formals = formals_esc} =
  (* formals: true for each escape parameter *)
  let
      val stack_local_count = ref 0
      val formals_access = map (allocLocalImpl stack_local_count) formals_esc
  in
      {func_name=func_name,
       name=name,
	   formals=formals_access,
	   stack_local_count=stack_local_count}
  end

fun name {name, formals, stack_local_count, func_name} = name

fun formals  {name, formals, stack_local_count, func_name} = formals

fun allocLocal {name, formals, stack_local_count, func_name} esc = allocLocalImpl stack_local_count esc

fun externalCall (name, param_list) = Tree.CALL(Tree.NAME(Temp.namedlabel(name)), param_list)

fun procEntryExit1 (frame, body) = body

fun procEntryExit2 (frame, body_instr) =
    body_instr @ [Assem.OPER{
                       assem="",
                       src=[ZERO, RA, SP] @ calleesaves,
                       dst=[],
                       jump=SOME[]}]
fun procEntryExit3 ({func_name, name, formals, stack_local_count}, body_instr) = {
    prolog = "Procedure " ^ func_name ^ "\n",
    body = Assem.LABEL {assem=(Symbol.name name)^":", lab=name}:: body_instr,
    epilog = "End " ^ func_name ^ "\n"
}
end
