structure Liveness :
          sig
              structure Graph : FUNCGRAPH
              datatype igraph =
                       IGRAPH of {
                           graph: Temp.temp Graph.graph,
                           tnode: Temp.temp -> Temp.temp Graph.node,
                           moves: Temp.temp Graph.edge list
                       }
              val interferenceGraph : Flow.ins Flow.flowgraph -> igraph
              (* Return an igraph and a table mapping each flow-graph node *)
              (* to the set of temps that are live-out at that node. *)

              val show : igraph -> unit
          end
=
struct
structure Graph = Flow.Graph
datatype igraph =
         IGRAPH of {
             graph: Temp.temp Graph.graph,
             tnode: Temp.temp -> Temp.temp Graph.node,
             moves: Temp.temp Graph.edge list
         }

structure TSet = Temp.Set
structure TMap = Temp.Map

datatype live = LIVE of {
             defset: TSet.set,
             useset: TSet.set,
             ismove: bool,
             liveIn: TSet.set ref,
             liveOut: TSet.set ref
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
                     val Flow.INS{def,use,ismove} = Graph.nodeInfo insNode
                     val live = LIVE {defset=listToSet def, useset=listToSet use, ismove=ismove,
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
            val LIVE {defset, useset, liveIn, liveOut, ismove} = Graph.nodeInfo liveNode
            val liveInSetOld = !liveIn
            val liveOutSetOld = !liveOut
            val () = liveIn := TSet.union (useset, TSet.difference (!liveOut, defset))
            val () = liveOut := Graph.foldSuccs'
                                    lgraph
                                    (fn (snode, accset) =>
                                        let
                                            val LIVE {defset, useset, liveIn, liveOut, ismove}= Graph.nodeInfo snode
                                        in
                                            TSet.union (accset, !liveIn)
                                        end
                                    )
                                    TSet.empty
                                    liveNode
        in
            changed orelse (not (TSet.equal (liveInSetOld ,!liveIn) )) orelse (not (TSet.equal (liveOutSetOld , !liveOut) ) )
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
exception TempNotFound
fun lookNidM tmap temp =
  case TMap.find (tmap, temp) of
      SOME(nid) => nid
    | NONE => raise TempNotFound

fun createIGraphFromLGraph lgraph =
  let
      val counter = ref 0
      val tmap = TMap.empty
      val igraph = Graph.empty

      fun addTemp (temp, (igraph, tmap)) =
        case TMap.find (tmap, temp) of
            SOME(i) => (igraph, tmap)
          | NONE =>
            let
                val nid = !counter
                val () = counter := nid + 1
            in
                (
                  Graph.addNode (igraph, nid, temp),
                  TMap.insert (tmap, temp, nid)
                )
            end

      (* add temps *)
      val (igraph, tmap) = Graph.foldNodes (
              fn (lnode, (igraph, tmap)) =>
                 let
                     val LIVE {defset,useset,liveIn,liveOut,ismove} = Graph.nodeInfo lnode
                     val (igraph, tmap) = TSet.foldl addTemp (igraph, tmap) defset
                     val (igraph, tmap) = TSet.foldl addTemp (igraph, tmap) useset
                 in
                     (igraph, tmap)
                 end
          ) (igraph, tmap) lgraph


      val lookNid = lookNidM tmap

      fun addIEdge (lnode, (igraph, moveEdges)) =
        let
            val LIVE {defset,useset,liveIn,liveOut,ismove} = Graph.nodeInfo lnode
            val (igraph, moveEdges) = TSet.foldl (
                    fn (defTemp, (igraph, moveEdges)) => (
                        TSet.foldl (
                            fn (outTemp, (igraph, moveEdges)) =>
                               if ismove then
                                   let
                                       val (useTemp::_) = TSet.listItems useset
                                       val srcID = lookNid useTemp
                                       val dstID = lookNid defTemp
                                   in
                                       if (useTemp = outTemp) then (igraph, {from=srcID, to=dstID}::moveEdges)
                                       else (Graph.doubleEdge (igraph, dstID, lookNid outTemp), moveEdges)
                                   end
                               else (Graph.doubleEdge (igraph, lookNid defTemp, lookNid outTemp), moveEdges)
                        ) (igraph, moveEdges) (!liveOut)
                    )
                ) (igraph, moveEdges) defset
        in
            (igraph, moveEdges)
        end

      (* add edges *)
      val (igraph, moveEdges) = Graph.foldNodes addIEdge (igraph, []) lgraph

  in
      (igraph, tmap, moveEdges)
  end
(* IGRAPH of { *)
(*   graph: Temp.temp Graph.graph, *)
(*   tnode: Temp.temp -> Temp.temp Graph.node, *)
(*   moves: Temp.temp Graph.edge list *)
(* } *)


fun interferenceGraph fgraph =
  let
      val lgraph = createLiveGraph fgraph
      val (igraph, tmap, moveEdges) = createIGraphFromLGraph lgraph
      fun lookNode temp = Graph.getNode (igraph, lookNidM tmap temp)
  in
      IGRAPH {
          graph=igraph,
          tnode=lookNode,
          moves=moveEdges
      }
  end

fun show (IGRAPH{graph, tnode, moves}) =
  let
      fun toString (nid, temp) = MipsFrame.register_name temp
  in
      Graph.printGraph toString graph
  end

end
