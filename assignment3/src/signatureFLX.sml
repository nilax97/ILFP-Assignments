signature FLX =
sig
    datatype term = VAR of string (* variable *)
                  | Z           (* zero *)
                  | T           (* true *)
                  | F           (* false *)
                  | P of term   (* Predecessor *)
                  | S of term   (* Successor *)
                  | ITE of term * term * term   (* If then else *)
                  | IZ of term  (* is zero *)
                  | GTZ of term (* is greater than zero *)
    
    exception Not_wellformed
    exception Not_nf
    exception Not_int

    val fromString: string -> term
    val toString: term -> string
    val fromInt: int -> term
    val toInt: term -> int
    val normalize: term -> term
end (* sig *)
