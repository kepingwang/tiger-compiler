CM.make "sources.cm";
let val program =  "$1"
    val absyn_tree = Parse.parse program
    val frag_list = Semant.trans absyn_tree
    fun printFrag Frame.PROC {body, frame} = Printtree.printtree (TextIO.stdOut, body)
      | printFrag Frame.STRING (label, str) = print ("String Frag:" ^ str)
in
    PrintAbsyn.print (TextIO.stdOut , tree);
    map printFrag frag_list;
    if !ErrorMsg.anyErrors then print \"ERROR FOUND\\n\" else \(\)
end
