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
