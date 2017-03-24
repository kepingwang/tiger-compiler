structure FindEscape:
          sig
              val findEscape: Absyn.exp -> unit
          end =
struct
(* fun say s = TextIO.output (TextIO.stdOut, s ^"\n") *)
type depth = int
type escEnv = (depth * bool ref) Symbol.table
structure A = Absyn
structure S = Symbol
fun traverseVar(env, d, A.SimpleVar (name, _)) =
  let
      val (dec_depth, escape) = case S.look (env, name) of
                                    SOME(e) => e
                                  | NONE  => (0, ref false)
  in
      if dec_depth <> d
      then escape := true
      else ()
  end
  | traverseVar (env, d, _) =  ()
and traverseExp (env, d) =
    let
        fun trexp (A.VarExp var) = traverseVar(env, d, var)
          | trexp (A.CallExp {args, ...}) = ( map trexp args; () )
          | trexp (A.OpExp {left, right, ...}) = (trexp left; trexp right)
          | trexp (A.RecordExp {fields, ...}) =
            ( map (fn (_, exp, _) => trexp exp) fields; ())
          | trexp (A.SeqExp exp_pos_list ) =
            ( map (fn (exp, _) => trexp exp) exp_pos_list; ())
          | trexp (A.AssignExp {var, exp, ...}) = (traverseVar (env, d, var); trexp exp)
          | trexp (A.IfExp {test, then', else', ...}) =
            (
              trexp test;
              trexp then';
              case else' of
                  SOME(exp) => trexp exp
                | NONE => ()
            )
          | trexp (A.WhileExp {test, body, ...}) = (trexp test; trexp body)
          | trexp (A.ForExp {var, escape, lo, hi, body, ...})  =
            (
              trexp lo;
              trexp hi;
              escape := false;
              let
                  val env' = S.enter (env, var, (d, escape))
              in
                  traverseExp (env', d) body
              end
            )
          | trexp (A.LetExp {decs, body, ...})  =
            let
              fun acc_env (dec, env) = traverseDecs (env, d, dec)
              val env' = foldl acc_env env decs
            in
                traverseExp (env', d) body
            end
          | trexp (A.ArrayExp {size, init, ...})  = (trexp size; trexp init)
          | trexp _ = ()

    in
        trexp
    end
and traverseDecs(env, d, A.FunctionDec({params, body, ...}::dec_tail)): escEnv =
    let
        fun addFunParam ({name, escape, typ, pos
}, env) =
          ( escape := false;
          S.enter (env, name, (d+1, escape)))
        val env' = foldl addFunParam env params
    in
        traverseExp (env', d+1) body;
        traverseDecs(env, d, A.FunctionDec(dec_tail));
        env
    end
  | traverseDecs (env, d, A.VarDec{name, escape, init, ...}) =
    (
      traverseExp (env, d) init;
      escape := false;
      S.enter (env, name, (d, escape))
    )
  | traverseDecs (env, d, _) = env
fun findEscape(prog) = traverseExp (S.empty, 0) prog
end
