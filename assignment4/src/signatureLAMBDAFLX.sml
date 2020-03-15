use "structureFLX.sml";

signature LAMBDAFLX =
sig
    datatype lterm = term (* term from FLX *)
                   | VAR of string      (* variables *)
                   | Z                  (* zero *)
                   | T                  (* true *)
                   | F                  (* false *)
                   | P of lterm         (* Predecessor *)
                   | S of lterm         (* Successor *)
                   | ITE of lterm * lterm * lterm       (* If then else *)
                   | IZ of lterm        (* is zero *)
                   | GTZ of lterm       (* is greater than zero *)
                   | LAMBDA of lterm * lterm    (* lambda x [lterm] *)
                   | APP of lterm * lterm       (* application of lambda terms, i.e. (L M) *)
                                        
    exception Not_wellformed
    exception Not_nf
    exception Not_int
    exception Not_welltyped
                  
    val fromString: string -> lterm
    val toString: lterm -> string
    val fromInt: int -> lterm
    val toInt: lterm -> int
    val isWellTyped: lterm -> bool
    val betanf: lterm -> lterm
end (* sig *)
