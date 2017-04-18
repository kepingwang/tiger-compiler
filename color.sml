signature COLOR =
sig
    structure Frame : FRAME
    type allocation = Frame.register Temp.Map.map
    val color: {interference: Liveness.igraph,
                initial: allocation,
                spillCost: Graph.node -> int,
                registers: Frame.register list}
               -> allocation * Temp.temp list
end

structure Color :> COLOR =
struct
structure Graph = Flow.Graph
fun color (IGRAPH{graph, tnode, moves}, initial, spillCost, regs) =
  let
      val k = List.length regs
      fun removeLowDegNode (graph, initial, k) =
        let
            fun findFirst [] = NONE
              | findFirst node::nodelist =
                let
                    val temp = Graph.nodeInfo node
                    val degree = Graph.outDegree node
                in
                    case Temp.Map.find (initial, temp) of
                        SOME(_) => findFirst nodelist
                      | NONE => if degree < k
                                then SOME(node)
                                else findFirst nodelist
                end
        in
            case findFirst (Graph.nodes graph) of
                SOME(node) => (Graph.removeNode (graph, Graph.getNodeID node), SOME(Graph.getNodeID node))
              | NONE => (graph, NONE)
        end
      fun spillNode (graph, initial) =
        let
            fun findFirst [] = NONE
              | findFirst node::nodelist =
                let
                    val temp = Graph.nodeInfo node
                in
                    case Temp.Map.find (initial, temp) of
                        SOME(_) => findFirst nodelist
                      | NONE => SOME(node)
                end
        in
            case findFirst (Graph.nodes graph) of
                SOME(node) => (Graph.removeNode (graph, Graph.getNodeID node), SOME(Graph.getNodeID node))
              | NONE => (graph, NONE)
        end
      fun createStack (graph, initial, k) =
        let
            fun removeNode graph =
              case removeLowDegNode (graph, initial, k) of
                  (graph', SOME(nid)) =>  (graph, nid)::(removeNode graph')
                | (graph', NONE) =>
                  let
                  in
                      case spillNode (graph', initial) of
                          (graph'', SOME(nid)) => (graph', nid)::(removeNode graph'')
                        | (graph'', NONE) => []
                  end
        in
            List.rev (removeNode graph)
        end
  in
  end
end
