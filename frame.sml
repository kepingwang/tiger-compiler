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
  val string : Temp.label * string -> string
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

val allRegs = [
    ("zero", Temp.newtemp()),
    ("v0", Temp.newtemp()),
    ("v1", Temp.newtemp()),
    ("a0", Temp.newtemp()),
    ("a1", Temp.newtemp()),
    ("a2", Temp.newtemp()),
    ("a3", Temp.newtemp()),
    ("t0", Temp.newtemp()),
    ("t1", Temp.newtemp()),
    ("t2", Temp.newtemp()),
    ("t3", Temp.newtemp()),
    ("t4", Temp.newtemp()),
    ("t5", Temp.newtemp()),
    ("t6", Temp.newtemp()),
    ("t7", Temp.newtemp()),
    ("s0", Temp.newtemp()),
    ("s1", Temp.newtemp()),
    ("s2", Temp.newtemp()),
    ("s3", Temp.newtemp()),
    ("s4", Temp.newtemp()),
    ("s5", Temp.newtemp()),
    ("s6", Temp.newtemp()),
    ("s7", Temp.newtemp()),
    ("t8", Temp.newtemp()),
    ("t9", Temp.newtemp()),
    ("sp", Temp.newtemp()),
    ("fp", Temp.newtemp()),
    ("ra", Temp.newtemp())
] (*no k0, k1, and at*)
fun findRegTemp name =
  let
      val (_, temp) = Option.valOf (List.find (fn (n, t) => name = n) allRegs)
  in
      temp
  end
fun findRegTemps nameList = map findRegTemp nameList
val registers = map (fn (name, temp) => name) allRegs
val ZERO = findRegTemp "zero"
val RV = findRegTemp "v0"
val ARGS = findRegTemps ["a0", "a1", "a2", "a3"]
val SP = findRegTemp "sp"
val FP = findRegTemp "fp"
val RA = findRegTemp "ra"

val specialRegs = [
  ZERO, RV, SP, FP, RA
]
val callersaves = findRegTemps ["t0", "t1", "t2", "t3", "t4", "t5", "t6", "t7", "t8", "t9",
                                "v1", "a0", "a1", "a2", "a3"
                               ]
val calleesaves = findRegTemps ["s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7"]

structure TMap = Temp.Map
val tempMap = foldl (fn ((name, temp), map) =>
                        TMap.insert (map, temp, name)
                    ) TMap.empty allRegs
fun register_name t =
  case TMap.find (tempMap, t) of
      SOME(name) => name
    | NONE => Temp.makestring t
val wordSize = 4 (* ? *)
fun func_name {func_name, name, formals, stack_local_count} = func_name
fun exp access exp =
  (* used to turn a Frame.access into Tree.exp, exp param is the address of the FP*)
  case access of
      InFrame(0) => Tree.MEM(exp)
    | InFrame(k) => Tree.MEM(Tree.BINOP(Tree.PLUS, exp, Tree.CONST(k)))
    | InReg(tempReg) => Tree.TEMP(tempReg)

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

fun string  (label, str) = ".data\n" ^(Symbol.name label) ^ ":\n .asciiz \"" ^ str ^"\"\n"
structure T = Tree
fun procEntryExit1 (frame , body) =
  let
      val {name, formals, stack_local_count, func_name} = frame
      fun setupParam (access, (stmt,n)) =
        if n < 4 then
            (case access of
                 InReg t => (T.SEQ(
                                  T.MOVE (T.TEMP t,
                                          T.TEMP (List.nth (ARGS, n))
                                         )
                                 ,stmt)
                            , n+1)
               | InFrame (k) => (T.SEQ(
                                      (T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP FP, T.CONST k)),
                                              T.TEMP(List.nth (ARGS, n))
                                             )
                                      ), stmt)
                                , n+1)
            )
        else
            (case access of
                 InReg t => (T.SEQ(
                                  T.MOVE (T.TEMP t,
                                          T.MEM(T.BINOP(T.PLUS, T.TEMP FP, T.CONST (n*wordSize) ))
                                         ),
                                  stmt
                              )
                            , n+1)
               | InFrame(k) => (stmt, n+1)
            )
      val (body, _) = foldl setupParam (body, 0) formals

      fun saveLoadReg (temp, stmt) =
        let
            val access = allocLocal frame true
            val location_exp = exp access (T.TEMP FP)
        in
            T.SEQ(
                T.SEQ(
                    T.MOVE(location_exp, T.TEMP(temp)),
                    stmt),
                T.MOVE(T.TEMP(temp), location_exp)
            )
        end
      val body = foldl saveLoadReg body calleesaves
  in
      body
  end

fun procEntryExit2 (frame, body_instr) =
    body_instr @ [Assem.OPER{
                       assem="",
                       src=[ZERO, RA, SP, FP] @ calleesaves,
                       dst=[],
                       jump=SOME[]}]
fun procEntryExit3 ({func_name, name, formals, stack_local_count}, body_instr) = {
    prolog = ".text\n# Procedure " ^ func_name ^ "\n",
    body = Assem.LABEL {assem=(Symbol.name name)^":", lab=name}:: body_instr,
    epilog = "# End " ^ func_name ^ "\n"
}
end
