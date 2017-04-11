signature CODEGEN =
sig
    structure Frame : FRAME
    val codegen : Frame.frame -> Tree.stm -> Assem.instr list
    exception Unmatched
end

structure MipsGen : CODEGEN =
struct
structure Frame = MipsFrame
structure A = Assem
structure T = Tree
val calldefs= Frame.callersaves @ [Frame.RV, Frame.RA]
exception Unmatched
fun codegen frame stm =
  let
      val assem_list : A.instr list ref = ref nil
      fun emit instr = assem_list := (instr :: !assem_list)
      fun munchStm (T.LABEL lab) = emit(
            A.LABEL {assem=(Symbol.name lab)^":", lab = lab}
        )
        | munchStm (T.MOVE (T.TEMP dst,
                            T.MEM (T.BINOP(T.PLUS, T.TEMP src, T.CONST offset)))) =
          emit(A.OPER {
                    assem="lw `d0, " ^ (Int.toString offset) ^ "(`s0)",
                    dst=[dst],
                    src=[src],
                    jump=NONE
              })
        | munchStm (T.MOVE (T.TEMP dst,
                            T.MEM (T.BINOP(T.PLUS, T.CONST offset, T.TEMP src)))) =
          emit(A.OPER {
                    assem="lw `d0, " ^ (Int.toString offset) ^ "(`s0)",
                    dst=[dst],
                    src=[src],
                    jump=NONE
              })
        | munchStm (T.MOVE (T.TEMP dst, T.MEM src_exp)) =
          emit(A.OPER {
                    assem="lw `d0, 0(`s0)",
                    dst=[dst],
                    src=[munchExp src_exp],
                    jump=NONE
              })
        | munchStm (T.MOVE (T.TEMP dst, T.TEMP src)) =
          emit(A.MOVE {
                    assem="move `d0, `s0",
                    dst=dst,
                    src=src
              })
        | munchStm (T.MOVE (T.TEMP dst, T.CONST c)) =
          emit(A.OPER {
                    assem="li `d0, " ^ (Int.toString c),
                    dst=[dst],
                    src=[],
                    jump=NONE
              })
        | munchStm (T.MOVE (T.TEMP dst, T.NAME lab)) =
          emit(A.OPER {
                    assem="la `d0, " ^ (Symbol.name lab),
                    dst=[dst],
                    src=[],
                    jump=NONE
              })
        | munchStm (T.MOVE (T.TEMP dst, src_exp)) =
          emit(A.MOVE {
                    assem="move `d0, `s0",
                    dst=dst,
                    src=munchExp src_exp
              })
        | munchStm (T.MOVE (T.MEM (T.TEMP dst_addr), T.TEMP src_val)) =
          emit(A.OPER{
                    assem="sw `s0, 0(`s1)",
                    dst=[],
                    src=[src_val, dst_addr],
                    jump = NONE
              })
        | munchStm (T.MOVE (
                         T.MEM (
                             T.BINOP(T.PLUS, T.TEMP base_addr, T.CONST offset)),
                         T.TEMP src_val)) =
          emit(A.OPER{
                    assem="sw `s0, " ^(Int.toString offset) ^"(`s1)",
                    dst=[],
                    src=[src_val, base_addr],
                    jump = NONE
              })
        | munchStm (T.MOVE (T.MEM addr_exp, T.TEMP src_val)) =
          emit(A.OPER{
                    assem="sw `s0, 0(`s1)",
                    dst=[],
                    src=[src_val, munchExp addr_exp],
                    jump = NONE
              })
        | munchStm (T.MOVE (T.MEM addr_exp, val_exp)) =
          emit(A.OPER{
                    assem="sw `s0, 0(`s1)",
                    dst=[],
                    src=[munchExp val_exp, munchExp addr_exp],
                    jump = NONE
              })
        | munchStm (T.JUMP ((T.NAME lab), label_list)) =
          emit(A.OPER{
                    assem="j "^(Symbol.name lab),
                    dst=[],
                    src=[],
                    jump =SOME label_list
              })
        | munchStm (T.JUMP (label_exp, label_list)) =
          emit(A.OPER{
                    assem="jr `s0",
                    dst=[],
                    src=[munchExp label_exp],
                    jump = SOME label_list
              })
        | munchStm (T.CJUMP (T.EQ, T.TEMP t1, T.TEMP t2, t_label, f_label)) =
          emit(A.OPER{
                    assem="beq `s0, `s1, "^(Symbol.name t_label),
                    src=[t1, t2],
                    dst=[],
                    jump = SOME [t_label, f_label]
              })
        | munchStm (T.CJUMP (T.EQ, exp1, exp2, t_label, f_label)) =
          emit(A.OPER{
                    assem="beq `s0, `s1, "^(Symbol.name t_label),
                    src=[munchExp exp1, munchExp exp2],
                    dst=[],
                    jump = SOME [t_label, f_label]
              })
        | munchStm (T.CJUMP (T.NE, T.TEMP t1, T.TEMP t2, t_label, f_label)) =
          emit(A.OPER{
                    assem="bne `s0, `s1, "^(Symbol.name t_label),
                    src=[t1, t2],
                    dst=[],
                    jump = SOME [t_label, f_label]
              })
        | munchStm (T.CJUMP (T.NE, exp1, exp2, t_label, f_label)) =
          emit(A.OPER{
                    assem="bne `s0, `s1, "^(Symbol.name t_label),
                    src=[munchExp exp1, munchExp exp2],
                    dst=[],
                    jump = SOME [t_label, f_label]
              })
        | munchStm (T.CJUMP (T.LT, T.TEMP t1, T.TEMP t2, t_label, f_label)) =
          emit(A.OPER{
                    assem="blt `s0, `s1, "^(Symbol.name t_label),
                    src=[t1, t2],
                    dst=[],
                    jump = SOME [t_label, f_label]
              })
        | munchStm (T.CJUMP (T.LT, exp1, exp2, t_label, f_label)) =
          emit(A.OPER{
                    assem="blt `s0, `s1, "^(Symbol.name t_label),
                    src=[munchExp exp1, munchExp exp2],
                    dst=[],
                    jump = SOME [t_label, f_label]
              })
        | munchStm (T.CJUMP (T.GT, T.TEMP t1, T.TEMP t2, t_label, f_label)) =
          emit(A.OPER{
                    assem="bgt `s0, `s1, "^(Symbol.name t_label),
                    src=[t1, t2],
                    dst=[],
                    jump = SOME [t_label, f_label]
              })
        | munchStm (T.CJUMP (T.GT, exp1, exp2, t_label, f_label)) =
          emit(A.OPER{
                    assem="bgt `s0, `s1, "^(Symbol.name t_label),
                    src=[munchExp exp1, munchExp exp2],
                    dst=[],
                    jump = SOME [t_label, f_label]
              })
        | munchStm (T.CJUMP (T.LE, T.TEMP t1, T.TEMP t2, t_label, f_label)) =
          emit(A.OPER{
                    assem="ble `s0, `s1, "^(Symbol.name t_label),
                    src=[t1, t2],
                    dst=[],
                    jump = SOME [t_label, f_label]
              })
        | munchStm (T.CJUMP (T.LE, exp1, exp2, t_label, f_label)) =
          emit(A.OPER{
                    assem="ble `s0, `s1, "^(Symbol.name t_label),
                    src=[munchExp exp1, munchExp exp2],
                    dst=[],
                    jump = SOME [t_label, f_label]
              })
        | munchStm (T.CJUMP (T.GE, T.TEMP t1, T.TEMP t2, t_label, f_label)) =
          emit(A.OPER{
                    assem="bge `s0, `s1, "^(Symbol.name t_label),
                    src=[t1, t2],
                    dst=[],
                    jump = SOME [t_label, f_label]
              })
        | munchStm (T.CJUMP (T.GE, exp1, exp2, t_label, f_label)) =
          emit(A.OPER{
                    assem="bge `s0, `s1, "^(Symbol.name t_label),
                    src=[munchExp exp1, munchExp exp2],
                    dst=[],
                    jump = SOME [t_label, f_label]
              })

        | munchStm (T.EXP exp) = (munchExp exp; ())
        | munchStm (e) = (
            print("uncatched stmt:\n");
            Printtree.printtree(TextIO.stdOut, e);
            raise Unmatched
        )
      and result(gen) =
          let
              val t = Temp.newtemp()
          in
              gen t;
              t
          end
      and munchArgs (_, []) = []
        | munchArgs (n, arg_exp::l) =
          if n < 4
          then (
              emit(A.OPER{
                        assem="move $a"^(Int.toString n) ^", `s0",
                        src=[munchExp arg_exp],
                        dst=[List.nth (Frame.ARGS, n)],
                        jump=NONE
                  });
              (List.nth (Frame.ARGS, n))::munchArgs(n+1, l)
          ) else (
              emit(A.OPER{
                        assem="sw `s0, " ^(Int.toString (Frame.wordSize * n)) ^"($sp)",
                        src=[munchExp arg_exp, Frame.SP],
                        dst=[],
                        jump=NONE
                  });
              munchArgs(n+1, l)
          )
      and munchExp (T.BINOP (T.PLUS, T.TEMP src1, T.TEMP src2)) =
          result(fn (r)=>
                    emit(A.OPER{
                              assem="add `d0, `s0, `s1",
                              src=[src1, src2],
                              dst=[r],
                              jump=NONE
                        })
                )
        | munchExp (T.BINOP (T.PLUS, T.TEMP src, T.CONST const)) =
          result(fn (r)=> 
                    emit(A.OPER{
                              assem="addi `d0, `s0, "^ (Int.toString const),
                              src=[src],
                              dst=[r],
                              jump=NONE
                        })
                )
        | munchExp (T.BINOP (T.PLUS, T.CONST const, T.TEMP src)) =
          result(fn (r)=> 
                    emit(A.OPER{
                              assem="addi `d0, `s0, "^ (Int.toString const),
                              src=[src],
                              dst=[r],
                              jump=NONE
                        })
                )
        | munchExp (T.BINOP (T.PLUS, exp1, exp2)) =
          result(fn (r)=> 
                    emit(A.OPER{
                              assem="add `d0, `s0, `s1",
                              src=[munchExp exp1, munchExp exp2],
                              dst=[r],
                              jump=NONE
                        })
                )
        | munchExp (T.BINOP (T.MINUS, T.TEMP src1, T.TEMP src2)) =
          result(fn (r)=>
                    emit(A.OPER{
                              assem="sub `d0, `s0, `s1",
                              src=[src1, src2],
                              dst=[r],
                              jump=NONE
                        })
                )
        | munchExp (T.BINOP (T.MINUS, exp1, exp2)) =
          result(fn (r)=> 
                    emit(A.OPER{
                              assem="sub `d0, `s0, `s1",
                              src=[munchExp exp1, munchExp exp2],
                              dst=[r],
                              jump=NONE
                        })
                )

        | munchExp (T.BINOP (T.MUL, T.TEMP src1, T.TEMP src2)) =
          result(fn (r)=>
                    emit(A.OPER{
                              assem="mul `d0, `s0, `s1",
                              src=[src1, src2],
                              dst=[r],
                              jump=NONE
                        })
                )
        | munchExp (T.BINOP (T.MUL, exp1, exp2)) =
          result(fn (r)=> 
                    emit(A.OPER{
                              assem="mul `d0, `s0, `s1",
                              src=[munchExp exp1, munchExp exp2],
                              dst=[r],
                              jump=NONE
                        })
                )

        | munchExp (T.BINOP (T.DIV, T.TEMP src1, T.TEMP src2)) =
          result(fn (r)=>
                    emit(A.OPER{
                              assem="div `d0, `s0, `s1",
                              src=[src1, src2],
                              dst=[r],
                              jump=NONE
                        })
                )
        | munchExp (T.BINOP (T.DIV, exp1, exp2)) =
          result(fn (r)=> 
                    emit(A.OPER{
                              assem="div `d0, `s0, `s1",
                              src=[munchExp exp1, munchExp exp2],
                              dst=[r],
                              jump=NONE
                        })
                )
        | munchExp (T.MEM (T.TEMP addr)) =
          result (fn (r)=>
                     emit(A.OPER{
                               assem="lw `d0, 0(`s0)",
                               src=[addr],
                               dst=[r],
                               jump=NONE
                         })
                 )
        | munchExp (T.MEM addr_exp) =
          result (fn (r)=>
                     emit(A.OPER{
                               assem="lw `d0, 0(`s0)",
                               src=[munchExp addr_exp],
                               dst=[r],
                               jump=NONE
                         })
                 )
        | munchExp (T.TEMP t) = t
        | munchExp (T.CONST c) =
          result (fn (r) =>
                     emit(A.OPER{
                               assem="li `d0, "^ (Int.toString c),
                               src=[],
                               dst=[r],
                               jump=NONE
                         })
                 )
        | munchExp (T.CALL(T.NAME func_label, params)) =
          result ( fn (r) => (
                       emit(A.OPER{
                                 assem="sub $sp, $sp, " ^
                                       (Int.toString (Frame.wordSize * (List.length params))),
                                 src=[Frame.SP],
                                 dst=[Frame.SP],
                                 jump=NONE
                           });
                       emit(A.OPER{
                                 assem="jal "^(Symbol.name func_label),
                                 src= munchArgs (0, params),
                                 dst = calldefs,
                                 jump=NONE
                           });
                       emit(A.OPER{
                                 assem="add $sp, $sp, " ^
                                       (Int.toString (Frame.wordSize * (List.length params))),
                                 src=[Frame.SP],
                                 dst=[Frame.SP],
                                 jump=NONE
                           });
                       emit(A.MOVE{
                                 assem="move `d0, $v0",
                                 src=Frame.RV,
                                 dst=r
                           })

                   )
                 )
        | munchExp (T.NAME lab) =
          result ( fn(r) => emit(
                               A.OPER({
                                         assem="la `d0, "^ (Symbol.name lab),
                                         src = [],
                                         dst = [r],
                                         jump=NONE
                                     })
                           )
                 )
        | munchExp (e) = (
            print("uncatched exp:\n");
            Printtree.printtree(TextIO.stdOut, T.EXP(e));
            raise Unmatched
        )
  in
      munchStm stm;
      rev (!assem_list)
  end
end
