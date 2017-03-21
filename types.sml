structure Types =
struct

  type unique = unit ref

  datatype ty =
            RECORD of (Symbol.symbol * ty) list * unique
          | NIL
          | INT
          | WINT
          | STRING
          | ARRAY of ty * unique
	      | NAME of Symbol.symbol * ty option ref
	      | UNIT
          | BOTTOM

  fun toString t =
    case t of
        RECORD _ => "Record"
      | NIL => "Nil"
      | INT => "Int"
      | WINT => "WInt"
      | STRING => "String"
      | ARRAY _ => "Array"
      | NAME _ =>  "Name"
      | UNIT => "Unit"
      | BOTTOM => "Bottom"
end

