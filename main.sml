structure Main = struct

   structure Tr = Translate
   structure Frame = MipsFrame
   structure T = Tree
   structure A = Assem
   (* structure R = RegAlloc *)

 fun getsome (SOME x) = x

 fun emitproc out (Frame.PROC{body,frame}) =
   let val _ = print ("emit " ^ (Frame.func_name frame) ^ "\n")
       fun compile_proc (body, frame) =
         let
             fun compile body =
               let
                   val stms = Canon.linearize body
                   val stms = Canon.traceSchedule(Canon.basicBlocks stms)
	               val instrs =   List.concat(map (MipsGen.codegen frame) stms)
                   val instrs = Frame.procEntryExit2 (frame, instrs)
                   val {prolog, body=instrs, epilog} = Frame.procEntryExit3 (frame, instrs)
                   val (allocation, spillList) = RegAlloc.alloc (instrs, frame)
                   fun tempExists (stmt, spill_temp) =
                     let
                         fun spstmt (T.SEQ (stmt1, stmt2)) = spstmt stmt1 orelse spstmt stmt2
                           | spstmt (T.LABEL l) = false
                           | spstmt (T.JUMP (exp, l)) = spexp exp
                           | spstmt (T.CJUMP (r, exp1, exp2, l1, l2)) =
                             spexp exp1 orelse spexp exp2
                           | spstmt (T.MOVE(exp1, exp2)) = spexp exp1 orelse spexp exp2
                           | spstmt (T.EXP exp) = spexp exp
                         and spexp (T.BINOP (b, exp1, exp2)) = spexp exp1 orelse spexp exp2
                           | spexp (T.MEM exp) = spexp exp
                           | spexp (T.TEMP temp) = if temp = spill_temp then true else false
                           | spexp (T.ESEQ (stmt, exp)) = spstmt stmt orelse spexp exp
                           | spexp (T.NAME l) = false
                           | spexp (T.CONST i) = false
                           | spexp (T.CALL (exp, exp_l)) =
                             spexp exp orelse
                             let
                                 val found = foldl (fn (exp, found) => found orelse spexp exp) false exp_l
                             in
                                 found
                             end
                     in
                         spstmt stmt
                     end
                   fun selectTemp [] = NONE
                     | selectTemp (head::tail) = if tempExists (body, head) then SOME(head) else selectTemp tail
                   exception spillFailed
                   fun cleanMove [] = []
                     | cleanMove (A.MOVE{assem, dst, src}::ins_tail) = if Temp.Map.find (allocation, dst) = Temp.Map.find (allocation, src) then
                                                                         cleanMove ins_tail
                                                                     else
                                                                         A.MOVE {assem=assem, dst=dst, src=src}::(cleanMove ins_tail)
                     | cleanMove (ins::ins_tail) = ins::cleanMove(ins_tail)
               in
                   case spillList of
                       [] => (prolog, cleanMove(instrs), epilog, allocation)
                     | _ => (
                         case selectTemp spillList of
                             NONE => raise spillFailed
                           | SOME(temp) =>
                             let
                                 val _ = print("Spilling " ^ (Frame.register_name temp) ^ "\n")
                                 val spilled_body = Frame.spillTemp (frame, body, temp)
                             in
                                 compile spilled_body
                             end
                     )
               end
         in
             compile body
         end
       val (prolog, instrs, epilog, allocation) = compile_proc (body, frame)
       fun tempName temp =
         "$" ^ (Option.valOf (Temp.Map.find (allocation, temp)))
       val format1 = Assem.format(tempName)
   in
       TextIO.output(out, prolog);
       app (fn i => (TextIO.output(out,format1 i); TextIO.output(out, "\n"))) instrs;
       TextIO.output(out, epilog)
   end
   | emitproc out (Frame.STRING(lab,s)) = TextIO.output(out, Frame.string (lab, s) )

 fun withOpenFile fname f = 
   let val out = TextIO.openOut fname
   in (f out before TextIO.closeOut out) 
	  handle e => (TextIO.closeOut out; raise e)
   end 
 exception SyntaxError
 fun compile filename = 
   let val absyn_tree = Parse.parse filename
   in
       if !ErrorMsg.anyErrors then () else
       let
           val frags = Semant.transProg absyn_tree
       in
           if !ErrorMsg.anyErrors then () else
           let
               val runtime_ins = TextIO.openIn "runtimele.s"
               val sys_ins = TextIO.openIn "sysspim.s"
               fun readAll (ins, outs) =
                 let
                     val str_op = TextIO.inputLine ins
                 in
                     case str_op of
                         SOME(s) => (TextIO.output (outs, s); readAll (ins, outs))
                       | NONE => ()
                 end
           in
               withOpenFile (filename ^ ".s")
	                        (fn out =>
                                (readAll (runtime_ins, out);
                                 readAll (sys_ins, out);
                                 (app (emitproc out) frags))
                            )
           end
       end
   end
end




