open Ast

exception Error of string

let check (nbvars, nbclauses, expr) = 
    if nbclauses <> List.length expr then
        raise (Error "The number of clauses doesn't match.");
    List.iter (
        fun clause -> 
            List.iter (
                fun literal -> 
                    match literal with
                    | Equal (x, y, _) | NotEqual (x, y, _) -> 
                        if x = 0 || x > nbvars || y = 0 || y > nbvars then 
                            raise (Error "Variable number is illegal."))
                clause)
        expr

