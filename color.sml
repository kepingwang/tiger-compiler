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
structure Frame = MipsFrame
type allocation = Frame.register Temp.Map.map
structure Graph = Flow.Graph
structure TSet = Temp.Set
structure TMap = Temp.Map
structure ColorSet = SplaySetFn(Frame.register)
fun color (IGRAPH{graph, tnode, moves}, initial, spillCost, regs) =
  let
      val k = List.length regs
      fun isPrecolored temp = (case Temp.Map.find (initial, temp) of
                                   SOME(_) => true
                                 | NONE => false
                              )
      fun removeLowDegNode graph =
        let
            fun findFirst [] = NONE
              | findFirst node::nodelist =
                let
                    val temp = Graph.nodeInfo node
                    val degree = Graph.outDegree node
                in
                    if isPrecolored temp then
                        findFirst nodelist
                    else
                        if degree < k then
                            SOME(node)
                        else
                            findFirst nodelist
                end
        in
            case findFirst (Graph.nodes graph) of
                SOME(node) => (Graph.removeNode (graph, Graph.getNodeID node), SOME(Graph.getNodeID node))
              | NONE => (graph, NONE)
        end
      fun spillNode graph =
        let
            fun findFirst [] = NONE
              | findFirst node::nodelist =
                let
                    val temp = Graph.nodeInfo node
                in
                    if isPrecolored temp then
                        findFirst nodelist
                    else
                        SOME(node)
                end
        in
            case findFirst (Graph.nodes graph) of
                SOME(node) => (Graph.removeNode (graph, Graph.getNodeID node), SOME(Graph.getNodeID node))
              | NONE => (graph, NONE)
        end
      (*Initially, no color is used*)
      val available_color = ColorSet.addList (ColorSet.empty, regs)
      (*select a color for nid, considering its neighbors and return a new color_alloc*)
      fun selectColor(graph, nid, color_alloc) =
        let
            (*mark the color used by a node*)
            fun deleteUsedColor (node, color_set) =
              let
                  val temp = Graph.nodeInfo node
              in
                  case TMap.find (color_alloc, temp) of
                      SOME(color) => ColorSet.delete (color_set, color)
                    | NONE => color_set  (*This node is not colored, a spill node*)
              end
            val avail_color_set = Graph.foldSuccs' graph deleteUsedColor available_color (Graph.getNode (graph, nid))
            val avail_color_list = ColorSet.listItems avail_color_set
            fun findFirstColor [] = NONE (*no color available*)
              | findFirstColor (head::color_list) = SOME(head)
        in
            findFirstColor avail_color_list
        end

      (*Color graph, return (color_allocation, spill)*)
      fun colorGraph graph =
        (
          case removeLowDegNode graph of
              (graph', SOME(nid)) => (*trivial nodes*)
              let
                  val (color_alloc, spills) = colorGraph graph'
                  val temp = Graph.nodeInfo (Graph.getNode (graph, nid))
                  val color = Option.valOf (selectColor(graph, nid, color_alloc))
              in
                  (TMap.insert (color_alloc, temp, color), spills)
              end
            | (graph, NONE) => (*potential spilling or base case*)
              (case spillNode graph of
                   (graph', SOME(nid)) => (*potential spilling*)
                   let
                       val (color_alloc, spills) = colorGraph graph'
                       val temp = Graph.nodeInfo (Graph.getNode (graph, nid))
                   in
                       case selectColor(graph, nid, color_alloc) of
                           SOME(color) => (TMap.insert (color_alloc, temp, color), spills) (*No real spill*)
                         | NONE => (color_alloc, temp::spills) (*real spill*)
                   end
                 | (graph, NONE) => (initial, []) (*base case, return the initial allocation*)
              )
        )
  in
      colorGraph graph
  end
end
