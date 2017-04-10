(* manages control-flow graphs. *)
(* Each instruction or basic block is represented by a node in the flow graph*)
(* now only focus on list of instructions *)
signature FLOW =
sig
  structure Graph : FUNCGRAPH
  datatype ins = INS of {
             id: int,
             def: Temp.temp list,
             use: Temp.temp list,
             ismove: bool
           }
  type 'a flowgraph
end


structure Flow : FLOW =
struct
structure Graph = FuncGraph(struct type ord_key = int
                                   val compare = Int.compare
                            end)
datatype ins = INS of {
           id: int,
           def: Temp.temp list,
           use: Temp.temp list,
           ismove: bool
         }                      
type 'a flowgraph = 'a Graph.graph
end

  
structure MakeGraph :
          sig
            val instrs2graph: Assem.instr list -> Flow.ins Flow.Graph.graph
          end
= struct
(* The Flow.Graph.node list correspond to the instrucions. *)
(* In making the flow graph, the jump fields of instr are used in creating *)
(* control-flow edges. And the use and def info is attached to the nodes *)
(* by means of the use and def tables of the flowgraph.*)

structure F = Flow
structure T = Temp
structure G = Flow.Graph

fun instrs2graph instrs =
  let
    val g = G.empty
    val ins0 = F.INS {id=0,def=[],use=[T.newtemp()],ismove=false}
    val g = G.addNode (g, 2, ins0)
  in
    g
  end
  
end
