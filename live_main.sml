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
   let val absyn_tree = Parse.parse filename
       val frags = Semant.transProg absyn_tree
   in 
     withOpenFile (filename ^ ".s") 
	              (fn out => (app (emitproc out) frags))
   end

end



