CM.make "sources.cm";
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
            app (fn s => Printtree.printtree(TextIO.stdOut,s)) stms
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
