signature REG_ALLOC =
sig
    structure Frame : FRAME
    type allocation = Frame.register Temp.Map.map
    val alloc : Assem.instr list * Frame.frame ->
                Assem.instr list * allocation
end

structure RegAlloc : REG_ALLOC =
struct
structure Frame = MipsFrame
type allocation = Frame.register Temp.Map.map

exception Spill
                                 
fun alloc (assems, frame) =
  let
    val fgraph = MakeGraph.instrs2graph assems
    val igraph = Liveness.interferenceGraph fgraph
    val (allocation, spillList) = Color.color {
          interference=igraph,
          initial=Frame.tempMap,
          spillCost=(fn x => 1), (* not used now *)
          registers=Frame.registers
        }
    (* TODO: if spill, change assems *)
    val () = case List.length spillList of
                 0 => ()
               | _ => raise Spill
  in
    (assems, allocation)
  end
end
                       
