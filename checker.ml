open Types

exception Error of string

(*  Checks if the file respects the number of variables and the number of clauses. *)
let check (nbvars, nbclauses, expr) = 
    if nbclauses <> List.length expr then
        raise (Error "The number of clauses doesn't match.");
    List.iter (
        fun clause -> 
            List.iter (
                fun literal -> 
                    let (x, y) = literal.vars in
                    if x = 0 || x > nbvars || y = 0 || y > nbvars then 
                        raise (Error "Variable number is illegal."))
                clause)
        expr

