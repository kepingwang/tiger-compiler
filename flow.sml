(* manages control-flow graphs. *)
(* Each instruction or basic block is represented by a node in the flow graph*)
structure Flow :
          sig
	        structure Graph
	        datatype flowgraph =
		             FGRAPH of {control: Graph.graph,
                                def: Temp.temp list Graph.Table.table,
                                use: Temp.temp list Graph.Table.table,
                                ismove: bool Graph.Table.table}
          end
= struct
end

    
structure MakeGraph:
          sig
            val instrs2graph: Assem.instr list ->
                              Flow.flowgraph * Flow.Graph.node list
          end
= struct
(* The Flow.Graph.node list correspond to the instrucions. *)
(* In making the flow graph, the jump fields of instr are used in creating *)
(* control-flow edges. And the use and def info is attached to the nodes *)
(* by means of the use and def tables of the flowgraph.*)

end

structure Liveness :
          sig
            datatype igraph =
                     IGRAPH of {
                       graph: IGraph.graph,
                       tnode: Temp.temp -> IGraph.node,
                       gtemp: IGraph.node -> Temp.temp,
                       moves: (IGraph.node * IGraph.node) list
                     }
            val interferenceGraph :
                Flow.flowgraph ->
                igraph * (Flow.Graph.node -> Temp.temp list)
            (* Return an igraph and a table mapping each flow-graph node *)
            (* to the set of temps that are live-out at that node. *)
                           
            val show : outstream * igraph -> unit
          end
=
struct
end
