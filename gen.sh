#!/bin/bash
echo CM.make \"sources.cm\"\;
echo let val program =  \"$1\"
echo val tree = Parse.parse program
echo in
echo PrintAbsyn.print \(TextIO.stdOut , tree\)\;
echo Semant.transProg tree\;
echo if !ErrorMsg.anyErrors then print \"ERROR FOUND\\n\" else \(\)
echo end
