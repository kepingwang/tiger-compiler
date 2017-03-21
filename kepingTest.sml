print "Hello";

signature SYM =
sig
    type 'a table
    val find : 'a table * int -> int
end


structure Sym : SYM =
struct
type 'a table = 'a list
fun find (x, y) = y + 2
end


val a = Sym.find ([], 3)


signature TEST0 =
sig
  datatype dtype = EMP
		 | HELL of int
end

structure Test0 : TEST0 =
struct
datatype dtype = EMP
	       | HELL of int
end


structure T0 = Test0  
val b = T0.EMP
	  


val r = {x=10, y=3, z=4}
fun fa {x,z,y=3} = x + z
  | fa {x,y=_,z} = x + z

		
val h = fa r		    


(* unique: unit ref? *)	   
type unique = unit ref

datatype ty = RECORD of int * unique
       | STRING


val tyvar1 = RECORD (3, ref ())
val tyvar2 = RECORD (3, ref ())
val tyvar3 = STRING
	       
val haha = case tyvar1 of
	       RECORD (x1, y1) => (case tyvar2 of
				      RECORD (x2, y2) => y1 = y2 (* two unit ref aren't equal *)
				    | STRING => y1 = y1
						       )
	    | STRING => false


val l1 = []

val hahb =
    case l1 of
	x::y => x
     | _ => 9

val (a, b) = (3, 4)	      

(* check equality for tuple (type) *)
type symbol = string * int
val s1 = ("hello", 2)
val s2 = ("hello", 2)
val hahc = s1 = s2	   
		  
(* check equality for datatype *)
val tyvar4 = STRING		  
val hahd = tyvar3 = tyvar4		  
