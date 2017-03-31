signature CODEGEN =
sig
    structure Frame : FRAME
    val codegen : Frame.frame -> Tree.stm -> Assem.instr list
end

structure MipsGen : CODEGEN =
struct
structure Frame = MispFrame
structure A = Assem
structure T = Tree
fun codegen frame stm =
  let
      val assem_list : A.instr list ref = ref nil
      fun emit instr = assem_list := (instr :: !assem_list)
      fun munchStm (T.LABEL lab) = emit(
            A.LABEL {assem=(Symbol.name lab) ^ "\n", lab = lab}
        )
        | munchStm (T.MOVE (T.TEMP dst, T.TEMP src)) = emit(A.MOVE {
                                                                 assem="move `d0, `s0",
                                                                 dst=dst,
                                                                 src=src
                                                           })
        | munchStm (T.MOVE(T.TEMP dst, T.MEM src_exp)) = emit(A.OPER {
                                                                   assem="lw `d0, 0(`s0)",
                                                                   dst=dst,
                                                                   src=(munchExp src_exp),
                                                                   jump=NONE
                                                             })
        | munchStm (T.MOVE (T.TEMP dst, src_exp)) = emit(A.MOVE {
                                                              assem="move `d0, `s0",
                                                              dst=dst,
                                                              src=(munchExp src_exp)
                                                        })
        | munchStm (T.MOVE (T.MEM addr_exp, val_exp)) = emit(A.OPER{
                                                                  assem="sw `s0, 0(`s1)",
                                                                  dst=[],
                                                                  src=[munchExp val_exp, munchExp addr_exp],
                                                                  jump = NONE
                                                            })
        | munchStm (T.JUMP ((T.NAME lab), label_list)) = emit(A.OPER{
                                                     assem="j "^(Symbol.name lab),
                                                     dst=[],
                                                     src=[],
                                                     jump =SOME label_list
                                               })
        | munchStm (T.JUMP (label_exp, label_list)) emit(A.OPER{
                                                              assem="jr `s0",
                                                              dst=[],
                                                              src=(munchExp label_exp),
                                                              jump = SOME label_list
                                                        })
        | munchStm (T.CJUMP (T.EQ, exp1, exp2, t_label, f_label)) emit(A.OPER{
                                                                            assem="beq `s0, `s1, "^(Symbol.name t_label),
                                                                            src=[munchExp exp1, munchExp exp2],
                                                                            dst=[],
                                                                            jump = SOME [t_label, f_label]
                                                                      })
      and result(gen) =
          let
              val t = Temp.newtemp()
          in
              gen t;
              t
          end
      and munchExp (T.BINOP (T.PLUS, T.TEMP src1, T.TEMP src2)) = result(fn (r)=>
                                                                             emit(A.OPER{
                                                                                       assem="add `d0, `s0, `s1",
                                                                                       src=[src1, src2],
                                                                                       dst=[r],
                                                                                       jump=NONE
                                                                                 })
                                                                        )
        | munchExp (T.BINOP (T.PLUS, T.TEMP src, T.CONST const)) = result(fn (r)=> 
                                                                              emit(A.OPER{
                                                                                        assem="addi `d0, `s0, "^ (Int.toString const),
                                                                                        src=[src],
                                                                                        dst=[r],
                                                                                        jump=NONE
                                                                                  })
                                                                         )
        | munchExp (T.BINOP (T.PLUS, T.CONST const, T.TEMP src)) = result(fn (r)=> 
                                                                              emit(A.OPER{
                                                                                        assem="addi `d0, `s0, "^ (Int.toString const),
                                                                                        src=[src],
                                                                                        dst=[r],
                                                                                        jump=NONE
                                                                                  })
                                                                           )
      | munchExp (T.BINOP (T.PLUS, exp1, exp2)) = result(fn (r)=> 
                                                               emit(A.OPER{
                                                                         assem="add `d0, `s0, `s1",
                                                                         src=[munchExp exp1, munchExp exp2],
                                                                         dst=[r],
                                                                         jump=NONE
                                                                   })
                                                          )
      | munchExp (T.BINOP (T.MINUS, T.TEMP src1, T.TEMP src2)) = result(fn (r)=>
                                                                              emit(A.OPER{
                                                                                        assem="sub `d0, `s0, `s1",
                                                                                        src=[src1, src2],
                                                                                        dst=[r],
                                                                                        jump=NONE
                                                                                  })
                                                                         )
      | munchExp (T.BINOP (T.MINUS, exp1, exp2)) = result(fn (r)=> 
                                                               emit(A.OPER{
                                                                         assem="sub `d0, `s0, `s1",
                                                                         src=[munchExp exp1, munchExp exp2],
                                                                         dst=[r],
                                                                         jump=NONE
                                                                   })
                                                          )

      | munchExp (T.BINOP (T.MUL, T.TEMP src1, T.TEMP src2)) = result(fn (r)=>
                                                                             emit(A.OPER{
                                                                                       assem="mul `d0, `s0, `s1",
                                                                                       src=[src1, src2],
                                                                                       dst=[r],
                                                                                       jump=NONE
                                                                                 })
                                                                        )
      | munchExp (T.BINOP (T.MUL, exp1, exp2)) = result(fn (r)=> 
                                                               emit(A.OPER{
                                                                         assem="mul `d0, `s0, `s1",
                                                                         src=[munchExp exp1, munchExp exp2],
                                                                         dst=[r],
                                                                         jump=NONE
                                                                   })
                                                          )

      | munchExp (T.BINOP (T.DIV, T.TEMP src1, T.TEMP src2)) = result(fn (r)=>
                                                                             emit(A.OPER{
                                                                                       assem="div `d0, `s0, `s1",
                                                                                       src=[src1, src2],
                                                                                       dst=[r],
                                                                                       jump=NONE
                                                                                 })
                                                                        )
      | munchExp (T.BINOP (T.DIV, exp1, exp2)) = result(fn (r)=> 
                                                               emit(A.OPER{
                                                                         assem="div `d0, `s0, `s1",
                                                                         src=[munchExp exp1, munchExp exp2],
                                                                         dst=[r],
                                                                         jump=NONE
                                                                   })
                                                         )
      | munchExp (T.MEM (T.TEMP addr)) = result (fn (r)=>
                                                       emit(A.OPER{
                                                                 assem="lw `d0, 0(`s0)",
                                                                 src=[addr],
                                                                 dst=[r],
                                                                 jump=NONE
                                                           })
                                                  )
      | munchExp (T.MEM addr_exp) = result (fn (r)=>
                                                  emit(A.OPER{
                                                            assem="lw `d0, 0(`s0)",
                                                            src=[munchExp addr_exp],
                                                            dst=[r],
                                                            jump=NONE
                                                      })
                                             )
      | munchExp (T.TEMP t) = t
      | munchExp (T.CONST c) = result (fn (r) =>
                                             emit(A.OPER{
                                                       assem="li `d0, "^ (Int.toString c),
                                                       src=[],
                                                       dst=[r],
                                                       jump=NONE
                                                 })
                                         )
      | munchExp (T.CALL(T.NAME func_label, params)) =
        let
            
        in
            result ( fn (r) => (
                     )
                   )
        end



  in
      munchStm stm;
      rev (!assem_list)
  end
end
