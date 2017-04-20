CM.make "sources.cm";
SMLofNJ.Internals.TDP.mode := true;
structure G = Flow.Graph;
structure Frame = MipsFrame;
let val program =  "$1"
    val absyn_tree = Parse.parse program
    val frag_list = Semant.transProg absyn_tree
    fun printFrag (Frame.PROC {body, frame}) =
      ( print (Symbol.name (Frame.name frame) );
        print (":\n");
        Printtree.printtree (TextIO.stdOut, body);
        print ("Linearized:\n");
        let
	        val stms = Canon.linearize body
            val stms' = Canon.traceSchedule(Canon.basicBlocks stms)
        in
            app (fn s => Printtree.printtree(TextIO.stdOut,s)) stms';
            print ("Graph:\n");
            let
	            val instrs =   List.concat(map (MipsGen.codegen frame) stms')
                val instrs' = Frame.procEntryExit2 (frame, instrs)
                val {prolog, body, epilog} = Frame.procEntryExit3 (frame, instrs')
                val format0 = Assem.format(Frame.register_name)

            in
                let
                    val fgraph = MakeGraph.instrs2graph body
                    val igraph = Liveness.interferenceGraph fgraph
                    fun strTL templist =
                      foldl (fn (t, s) => s ^ " " ^ (Temp.makestring t)) "" templist
                    fun nodeToString (nid, Flow.INS{def, use, ismove}) =
                      (Int.toString nid) ^ ", def:" ^ (strTL def) ^ ", use:" ^ (strTL use) ^ ", move: " ^ (Bool.toString ismove)
                                                                                                              (* val () = G.printGraph nodeToString fgraph *)
                in
                    Liveness.show igraph
                end;
                print ("Assembly:\n");
                TextIO.output(TextIO.stdOut, prolog);
                app (fn i => (TextIO.output(TextIO.stdOut, format0 i); print("\n"))) body;
                TextIO.output(TextIO.stdOut, epilog);
                let
                    val (body', allocation) = RegAlloc.alloc (body, frame)
                    fun tempName temp =
                      "$" ^ (Option.valOf (Temp.Map.find (allocation, temp)))
                    val format1 = Assem.format(tempName)
                in
                    print("colored:\n");
                    TextIO.output(TextIO.stdOut, prolog);
                    app (fn i => (TextIO.output(TextIO.stdOut, format1 i); print("\n"))) body';
                    TextIO.output(TextIO.stdOut, epilog)
                end
            end;
            print("\n\n")
        end)
      | printFrag (Frame.STRING (label, str)) = (
          print (Symbol.name label);
          print (": " ^ str ^ "\n")
      )
in
    PrintAbsyn.print (TextIO.stdOut , absyn_tree);
    map printFrag frag_list;
    if !ErrorMsg.anyErrors then print "ERROR FOUND\n" else ()
end
