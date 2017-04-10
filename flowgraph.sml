(* manages control-flow graphs. *)
(* Each instruction or basic block is represented by a node in the flow graph*)
(* now only focus on list of instructions *)
signature FLOW =
sig
  structure Graph : FUNCGRAPH
  datatype ins = INS of {
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
(* In making the flow graph, the jump fields of instr are used in creating *)
(* control-flow edges. And the use and def info is attached to the nodes *)
(* by means of the use and def tables of the flowgraph.*)

structure S = Symbol
structure A = Assem
structure F = Flow
structure T = Temp
structure G = Flow.Graph

fun instrs2graph instrs =
  let
    val nidCount = ref 0
    fun procNode (A.OPER{assem,dst,src,jump}, (g,labelTable)) =
      let
        val ins = F.INS {def=dst, use=src, ismove=false}
        val nid = !nidCount
        val () = nidCount := nid+1
      in
        (G.addNode (g, nid, ins), labelTable)
      end
      | procNode (A.LABEL{assem,lab}, (g,labelTable)) =
        let
          val nid = !nidCount
          val labelTable = S.enter (labelTable, lab, nid)
        in
          (g, labelTable)
        end
      | procNode (A.MOVE{assem,dst,src}, (g,labelTable)) = 
        let
          val ins = F.INS {def=[dst], use=[src], ismove=true}
          val nid = !nidCount
          val () = nidCount := nid+1
        in
          (G.addNode (g, nid, ins), labelTable)
        end
    val (graph, labelTable) = foldl procNode (G.empty, S.empty) instrs
    (* Ddd ending node in case the last instr has no successor *)
    (* NOTE: this might not be needed *)
    val graph = G.addNode (graph, !nidCount, F.INS{def=[],use=[],ismove=false})

    val nidCount = ref 0
                       
    exception LabelNotFound of T.label
    fun lookNid (table, lab) =
      case S.look (table, lab) of
          SOME(nid) => nid
        | NONE => (raise LabelNotFound(lab); 0)
                       
    fun procEdge (A.OPER{assem,dst,src,jump}, g) =
      let
        val nid = !nidCount
        val () = nidCount := nid+1
      in
        case jump of
            SOME(labels) =>
            foldl (fn (lab, g) =>
                      G.addEdge (g, {from=nid, to=(lookNid (labelTable, lab))})
                  ) g labels
          | NONE => G.addEdge (g, {from=nid, to=nid+1})
      end
      | procEdge (A.LABEL{assem, lab}, g) = g
      | procEdge (A.MOVE{assem, dst, src}, g) =
        let
          val nid = !nidCount
          val () = nidCount := nid+1
        in
          G.addEdge (g, {from=nid, to=nid+1})
        end
    val graph = foldl procEdge graph instrs 
  in
    graph
  end
  
end
