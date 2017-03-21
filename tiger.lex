type svalue = Tokens.svalue
type pos = int
type ('a, 'b) token = ('a, 'b) Tokens.token
type lexresult = (svalue, pos) token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
val err = ErrorMsg.error
val bug = ErrorMsg.impossible

val working_string = ref ""
val string_start_pos = ref 0
val comment_level = ref 0

fun linenum_keep (text, start_pos) =
  let val charlist = String.explode text
      fun look(a::l, n) =
	if a = #"\n" then (
	    lineNum := !lineNum + 1;
	    linePos := (start_pos + n) :: !linePos;
	    look(l, n+1)
	) else look(l, n+1)
        | look ([], _) = ()
  in
      look(charlist, 0)
  end

datatype State = MYP | MYS | MYC
val state = ref MYP
fun eof() = (case !state of
                 MYC => err 0 "Comment not closing at file end."
               | MYS => err 0 "String not closing at file end."
               | _ => (); Tokens.EOF(0,0))
%%
%header (functor TigerLexFun(structure Tokens : Tiger_TOKENS));
%s COMMENT STR;
space=[\ \t];
superspace=[\n\ \t];
%%
<INITIAL> {space}+ => (
    continue()
);
<INITIAL> \n => (
	  linenum_keep (yytext, yypos);
	  continue()
);
<INITIAL> ":=" => (Tokens.ASSIGN(yypos, yypos+2));
<INITIAL> "|" => (Tokens.OR(yypos, yypos+1));
<INITIAL> "&" => (Tokens.AND(yypos, yypos+1));
<INITIAL> ">=" => (Tokens.GE(yypos, yypos+2));
<INITIAL> ">" => (Tokens.GT(yypos, yypos+1));
<INITIAL> "<=" => (Tokens.LE(yypos, yypos+2));
<INITIAL> "<" => (Tokens.LT(yypos, yypos+1));
<INITIAL> "<>" => (Tokens.NEQ(yypos, yypos+2));
<INITIAL> "=" => (Tokens.EQ(yypos, yypos+1));
<INITIAL> "/" => (Tokens.DIVIDE(yypos, yypos+1));
<INITIAL> "*" => (Tokens.TIMES(yypos, yypos+1));
<INITIAL> "-" => (Tokens.MINUS(yypos, yypos+1));
<INITIAL> "+" => (Tokens.PLUS(yypos, yypos+1));
<INITIAL> "." => (Tokens.DOT(yypos, yypos+1));
<INITIAL> "}" => (Tokens.RBRACE(yypos, yypos+1));
<INITIAL> "{" => (Tokens.LBRACE(yypos, yypos+1));
<INITIAL> "]" => (Tokens.RBRACK(yypos, yypos+1));
<INITIAL> "[" => (Tokens.LBRACK(yypos, yypos+1));
<INITIAL> ")" => (Tokens.RPAREN(yypos, yypos+1));
<INITIAL> "(" => (Tokens.LPAREN(yypos, yypos+1));
<INITIAL> ";" => (Tokens.SEMICOLON(yypos, yypos+1));
<INITIAL> ":" => (Tokens.COLON(yypos, yypos+1));
<INITIAL> "," => (Tokens.COMMA(yypos, yypos+1));

<INITIAL> [0-9]+ => ( (* int literal, no + -. Size limit (32 bit)? *)
	  case Int.fromString yytext of
	       SOME(n) => Tokens.INT(n, yypos, yypos+(String.size yytext))
             | NONE => bug "Integer literal cannot be converted."
);


<INITIAL> "while" => ( Tokens.WHILE(yypos, yypos+(String.size yytext)));
<INITIAL> "for" => ( Tokens.FOR(yypos, yypos+(String.size yytext)));
<INITIAL> "to" => ( Tokens.TO(yypos, yypos+(String.size yytext)));
<INITIAL> "break" => ( Tokens.BREAK(yypos, yypos+(String.size yytext)));
<INITIAL> "let" => ( Tokens.LET(yypos, yypos+(String.size yytext)));
<INITIAL> "in" => ( Tokens.IN(yypos, yypos+(String.size yytext)));
<INITIAL> "end" => ( Tokens.END(yypos, yypos+(String.size yytext)));
<INITIAL> "function" => ( Tokens.FUNCTION(yypos, yypos+(String.size yytext)));
<INITIAL> "var" => ( Tokens.VAR(yypos, yypos+(String.size yytext)));
<INITIAL> "type" => ( Tokens.TYPE(yypos, yypos+(String.size yytext)));
<INITIAL> "array" => ( Tokens.ARRAY(yypos, yypos+(String.size yytext)));
<INITIAL> "if" => ( Tokens.IF(yypos, yypos+(String.size yytext)));
<INITIAL> "then" => ( Tokens.THEN(yypos, yypos+(String.size yytext)));
<INITIAL> "else" => ( Tokens.ELSE(yypos, yypos+(String.size yytext)));
<INITIAL> "do" => ( Tokens.DO(yypos, yypos+(String.size yytext)));
<INITIAL> "of" => ( Tokens.OF(yypos, yypos+(String.size yytext)));
<INITIAL> "nil" => ( Tokens.NIL(yypos, yypos+(String.size yytext)));

<INITIAL> [a-zA-Z][0-9a-zA-Z_]* => ( Tokens.ID(yytext, yypos, yypos + (String.size yytext)) );

<INITIAL> \" => (
	  YYBEGIN STR;
	  state := MYS;
	  string_start_pos := yypos;
	  working_string := "";
	  continue()
);

<INITIAL> "/*" => (
	  YYBEGIN COMMENT;
	  state := MYC;
	  comment_level := 1;
	  continue()
);

<STR> [^\000-\031"\\]+ => (
      working_string := !working_string ^ yytext;
      continue()
);
<STR> \" => (YYBEGIN INITIAL;
      state := MYP;
      Tokens.STRING (!working_string, !string_start_pos, yypos)
);
<STR> \\n => (
      working_string := !working_string ^ "\n";
      continue()
);
<STR> \\t => (
      working_string := !working_string ^ "\t";
      continue()
);
<STR> \\\^[@-_] => (
      working_string := !working_string ^ (
          String.str (Char.chr ((Char.ord (String.sub (yytext, 2))) - 64))
      );
      continue()
);
<STR> \\[0-9][0-9][0-9] => (
      case Int.fromString (String.extract (yytext, 1, NONE)) of
      	   SOME(n) => (
	   	   if n < 128
		   then working_string := !working_string ^ (
		       Char.toString (Char.chr n)
		   ) else err yypos (
		       "ascii code should be smaller than 128: "^ yytext
		   )
	   )
	 | NONE => bug "ASCII code cannot be converted into integer";
	 continue()
);
<STR> \\\" => (
      working_string := !working_string ^ "\"";
      continue()
);
<STR> \\\\ => (
      working_string := !working_string ^ "\\";
      continue()
);
<STR> \\{superspace}+\\ => (
      linenum_keep(yytext, yypos);
      continue()
);
<STR> \t => (
      linenum_keep(yytext, yypos);
      err yypos ("Tab not allowed in string.");
      continue()
);
<STR> \n => (
      linenum_keep(yytext, yypos);
      err yypos ("String is not allowed to span multiple lines unless with \\f..f\\");
      continue()
);
<STR> [\000-\031] => (
      err yypos ("use \\^c to escape control character.");
      continue()
);
<STR> . => (
      err yypos ("illegal character in string " ^ yytext);
      continue()
);


<COMMENT> "/*" => (
	  comment_level := !comment_level +1;
	  continue()
);
<COMMENT> "*/" => (
	  comment_level := !comment_level -1;
	  if !comment_level = 0 then (YYBEGIN INITIAL; state := MYP) else ();
	  continue()
);
<COMMENT> \n => (
	  linenum_keep (yytext, yypos);
	  continue()
);
<COMMENT> . => (continue());



. => (
  err yypos ("illegal character " ^ yytext);
  continue()
);

