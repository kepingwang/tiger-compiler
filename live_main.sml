structure Main = struct

   structure Tr = Translate
   structure Frame = MipsFrame
   (* structure R = RegAlloc *)
   structure F = Flow
   structure G = Flow.Graph

 fun getsome (SOME x) = x

 fun emitproc out (Frame.PROC{body,frame}) =
   let val _ = print ("emit " ^ (Frame.func_name frame) ^ "\n")
       (*         val _ = Printtree.printtree(out,body); *)
	   val stms = Canon.linearize body
       (*         val _ = app (fn s => Printtree.printtree(out,s)) stms; *)
       val stms' = Canon.traceSchedule(Canon.basicBlocks stms)
	   val instrs =   List.concat(map (MipsGen.codegen frame) stms') 
       val instrs' = Frame.procEntryExit2 (frame, instrs)
       val {prolog, body, epilog} = Frame.procEntryExit3 (frame, instrs')
       val format0 = Assem.format(Frame.register_name)
       val graph = MakeGraph.instrs2graph instrs'
       fun strTL templist =
         foldl (fn (t, s) => s ^ " " ^ (Temp.makestring t)) "" templist
       fun nodeToString (nid, Flow.INS{def, use, ismove}) =
         (Int.toString nid) ^ ", def:" ^ (strTL def) ^ ", use:" ^ (strTL use)
       val () = G.printGraph nodeToString graph
   in
       TextIO.output(out, prolog);
       app (fn i => (TextIO.output(out,format0 i); TextIO.output(out, "\n"))) body;
       TextIO.output(out, epilog)
   end
   | emitproc out (Frame.STRING(lab,s)) = TextIO.output(out, (Symbol.name lab) ^": " ^ s ^"\n")

 fun withOpenFile fname f = 
   let val out = TextIO.openOut fname
   in (f out before TextIO.closeOut out) 
	  handle e => (TextIO.closeOut out; raise e)
   end

 fun compile filename =
   let val program =  filename
       val absyn_tree = Parse.parse program
       val frag_list = Semant.transProg absyn_tree
       fun printFrag (Frame.PROC {body, frame}) =
         (
           let
	           val stms = Canon.linearize body
               val stms' = Canon.traceSchedule(Canon.basicBlocks stms)
           in
               let
	               val instrs =   List.concat(map (MipsGen.codegen frame) stms')
                   val instrs' = Frame.procEntryExit2 (frame, instrs)
                   val {prolog, body, epilog} = Frame.procEntryExit3 (frame, instrs')
                   val format0 = Assem.format(Frame.register_name)
               in
                   TextIO.output(TextIO.stdOut, prolog);
                   app (fn i => (TextIO.output(TextIO.stdOut, format0 i); print("\n"))) body;
                   TextIO.output(TextIO.stdOut, epilog);
                   let
                       val fgraph = MakeGraph.instrs2graph body
                       val igraph = Liveness.interferenceGraph fgraph
                       fun strTL templist =
                         foldl (fn (t, s) => s ^ " " ^ (Temp.makestring t)) "" templist
                       fun nodeToString (nid, Flow.INS{def, use, ismove}) =
                         (Int.toString nid) ^ ", def:" ^ (strTL def) ^ ", use:" ^ (strTL use) ^ ", move: " ^ (Bool.toString ismove)
                                                                                                                 (* val () = G.printGraph nodeToString fgraph *)
                       val () = print ("Inference Graph for " ^ prolog)
                   in
                       Liveness.show igraph
                   end
               end;
               print("\n\n")
           end)
         | printFrag (Frame.STRING (label, str)) = (
             print (Symbol.name label);
             print (": " ^ str ^ "\n")
         )
   in
       map printFrag frag_list;
       if !ErrorMsg.anyErrors then print "ERROR FOUND\n" else ()
   end
 fun iGraph filename =
   let val program =  filename
       val absyn_tree = Parse.parse program
       val frag_list = Semant.transProg absyn_tree
       fun printFrag (Frame.PROC {body, frame}) =
         (
           let
	           val stms = Canon.linearize body
               val stms' = Canon.traceSchedule(Canon.basicBlocks stms)
           in
               let
	               val instrs =   List.concat(map (MipsGen.codegen frame) stms')
                   val instrs' = Frame.procEntryExit2 (frame, instrs)
                   val {prolog, body, epilog} = Frame.procEntryExit3 (frame, instrs')
                   val format0 = Assem.format(Frame.register_name)
               in
                   let
                       val fgraph = MakeGraph.instrs2graph body
                       val igraph = Liveness.interferenceGraph fgraph
                       val () = print ("Inference Graph for " ^ prolog)
                   in
                       Liveness.show igraph
                   end
               end;
               print("\n\n")
           end)
         | printFrag (Frame.STRING (label, str)) = (
             print (Symbol.name label);
             print (": " ^ str ^ "\n")
         )
   in
       map printFrag frag_list;
       if !ErrorMsg.anyErrors then print "ERROR FOUND\n" else ()
   end
  fun assembly filename =
   let val program =  filename
       val absyn_tree = Parse.parse program
       val frag_list = Semant.transProg absyn_tree
       fun printFrag (Frame.PROC {body, frame}) =
         (
           let
	           val stms = Canon.linearize body
               val stms' = Canon.traceSchedule(Canon.basicBlocks stms)
           in
               let
	               val instrs =   List.concat(map (MipsGen.codegen frame) stms')
                   val instrs' = Frame.procEntryExit2 (frame, instrs)
                   val {prolog, body, epilog} = Frame.procEntryExit3 (frame, instrs')
                   val format0 = Assem.format(Frame.register_name)
                   val (body', allocation) = RegAlloc.alloc (body, Frame.frame)
                   fun tempName temp =
                     "$" ^ (Option.valOf (Temp.Map.find (allocation, tempf)))
                   val format1 = Assem.format(tempName)
               in
                   TextIO.output(TextIO.stdOut, prolog);
                   app (fn i => (TextIO.output(TextIO.stdOut, format1 i); print("\n"))) body;
                   TextIO.output(TextIO.stdOut, epilog)
               end;
               print("\n\n")
           end)
         | printFrag (Frame.STRING (label, str)) = (
             print (Symbol.name label);
             print (": " ^ str ^ "\n")
         )
   in
       map printFrag frag_list;
       if !ErrorMsg.anyErrors then print "ERROR FOUND\n" else ()
   end
end



