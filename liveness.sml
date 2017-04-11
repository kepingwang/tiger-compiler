structure Liveness :
          sig
            structure Graph = FuncGraph(struct type ord_key = int
                                               val compare = Int.compare
                                        end)
            datatype igraph =
                     IGRAPH of {
                       graph: Temp.temp Graph.graph,
                       tnode: Temp.temp -> Temp.temp Graph.node,
                       moves: Temp.temp Graph.edge list
                     }
            val interferenceGraph :
                Flow.ins Flow.flowgraph -> igraph
                                             (* Return an igraph and a table mapping each flow-graph node *)
                                             (* to the set of temps that are live-out at that node. *)
                                             
                                             (* val show : outstream * igraph -> unit *)
          end
=
struct
structure Graph = FuncGraph(struct type ord_key = int
                                   val compare = Int.compare
                            end)
datatype igraph =
         IGRAPH of {
           graph: Temp.temp Graph.graph,
           tnode: Temp.temp -> Temp.temp Graph.node,
           moves: Temp.temp Graph.edge list
         }

structure TSet = Temp.Set
structure TMap = Temp.Map

datatype live = LIVE of {
           defset: TSet,
           useset: TSet,
           liveIn: TSet ref,
           liveOut: TSet ref
         }

fun listToSet tempList =
  let
    val set = TSet.empty
  in
    TSet.addList (set, tempList)
  end
    


fun initlgraph fgraph =
  let
    val lgraph = Graph.foldNodes (
          fn (insNode, lgraph) =>
             let
               val {def,use,ismove} = Graph.nodeInfo insNode
               val live = LIVE {defset=listToSet def, useset=listToSet use,
                                liveIn=ref TSet.empty, liveOut=ref TSet.empty}
             in
               Graph.addNode (lgraph, Graph.getNodeID insNode, live)
             end
        ) Graph.empty fgraph
    val lgraph = Graph.foldNodes (
          fn (insNode, lgraph) =>
             let
               val nid = Graph.getNodeID insNode
               val succsIDs = Graph.succs insNode
             in
               foldl (
                 fn (succsID, lgraph) =>
                    Graph.addEdge (lgraph, {from=nid, to=succsID})
               ) lgraph succsIDs
             end
        ) lgraph fgraph
  in
    lgraph
  end
    
    
fun updateLive lgraph = (* update one round *)
  let
    fun calcLive (liveNode, changed) =
      let
        val {defset, useset, liveIn, liveOut} = Graph.nodeInfo liveNode
        val liveInSetOld = !liveIn
        val liveOutSetOld = !liveOut
        val () = liveIn := TSet.union (useset, TSet.difference (!liveOut, defset))
        val () = liveOut := Graph.foldSuccs'
                              fgraph
                              (fn (snode, accset) => 
                                  let
                                    val {liveIn,...} = Graph.nodeInfo snode
                                  in
                                    TSet.union (accset, !liveIn)
                                  end
                              )
                              TSet.empty
                              liveNode
      in
        changed orelse liveInSetOld <> !liveIn orelse liveOutSetOld <> !liveOut
      end
  in
    Graph.foldNodes calcLive false lgraph (* return true if changed *)
  end
    
fun createLiveGraph fgraph =
  let
    val lgraph = initlgraph fgraph
    fun updateUntilStable lgraph =
      if updateLive lgraph then updateUntilStable lgraph
      else lgraph
  in
    updateUntilStable lgraph
  end        


datatype live = LIVE of {
           defset: TSet,
           useset: TSet,
           liveIn: TSet ref,
           liveOut: TSet ref
         }

                          
fun createIGraphFromLGraph lgraph =
  let
    val counter = ref 0
    val tmap = TMap.empty
    val igraph = Graph.empty

    fun addTemp (temp, (igraph, tmap)) =
      case TMap.find tempMap temp of
          SOME(i) => (igraph, tmap)
        | NONE =>
          let
            val nid = !counter
            val () = counter := nid + 1
          in
            (
              Graph.addNode (igraph, nid, temp),
              TMap.insert (temp, nid)
            )
          end

    (* add temps *)
    val (igraph, tmap) = Graph.foldNodes (
          fn (lnode, (igraph, tmap)) =>
             let
               val {defset,useset,liveIn,liveOut} = Graph.nodeInfo lnode
               val (igraph, tmap) = TSet.foldl addTemp (igraph, tmap) defset
               val (igraph, tmap) = TSet.foldl addTemp (igraph, tmap) useset
             in
               (igraph, map)
             end
        ) (igraph, tmap) lgraph

    exception TempNotFound
    fun lookNid temp =
      case TMap.find (tmap, temp) of
          SOME(nid) => nid
        | NONE => raise TempNotFound

    fun addIEdge (lnode, igraph) =
      let
        val {defset,useset,liveIn,liveOut} = Graph.nodeInfo lnode
        val igraph = TSet.foldl (
              fn (defTemp, igraph) =>
                 TSet.foldl (
                   fn (outTemp, igraph) =>
                      Graph.doubleEdge (igraph, lookNid defTemp, lookNid outTemp)
                 ) igraph !liveOut
            ) igraph defset                                                 
      in
        igraph
      end
        
    (* add edges *)
    val igraph = Graph.foldNodes addIEdge igraph lgraph
                                 
  in
    (igraph, tmap)
  end
                     (* IGRAPH of { *)
                     (*   graph: Temp.temp Graph.graph, *)
                     (*   tnode: Temp.temp -> Temp.temp Graph.node, *)
                     (*   moves: Temp.temp Graph.edge list *)
                     (* } *)

    
fun interferenceGraph fgraph =
  let
    val lgraph = createLiveGraph fgraph
    val (igraph, tmap) = createIGraphFromLGraph lgraph
    fun lookNode temp = Graph.getNode (igraph, lookNid temp)
  in
    IGRAPH {
      graph=igraph,
      tnode=lookNode,
      moves=[] (* TODO: list of move edges *)
    }
  end
    

