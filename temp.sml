(* make this an abstraction sometime *)
(* TEMP is used to represent a value temporarily held in a register. *)
(* Temps are abstract names for label variables. *)
(* Labels are abstract names for static memory addresses. *)
structure Temp : TEMP =
struct
    type temp = int
    val temps = ref 100
    fun newtemp() = let val t = !temps in temps := t+1; t end

    structure Table = IntMapTable(type key = int
				  fun getInt n = n)

    fun makestring t = "t" ^ Int.toString t

  type label = Symbol.symbol

local structure F = Format
      fun postinc x = let val i = !x in x := i+1; i end
      val labs = ref 0
 in
    fun newlabel() = Symbol.symbol(F.format "L%d" [F.INT(postinc labs)])
    val namedlabel = Symbol.symbol
end


end
