open Ast

(*let union (f : expr) (c : clause) = f @ c

let not = function
    | Equal(v1, v2) -> Notequal(v1, v2)
    | NotEqual(v1, v2) -> Notequal(v1, v2)*)

exception SAT
exception UNSAT

let is_undefined l m = not (List.exists (fun l' -> l' = l ) m)

let  rec clause_satified_by c m = match c with
    | [] -> true
    | l::ls -> if (is_undefined l m) then false else clause_satified_by ls m

let rec formula_satisfied_by f m = match f with
    | [] -> true
    | c::cs -> if (clause_satified_by c m) then formula_satisfied_by cs m else false

let success f m = if (formula_satisfied_by f m) then raise SAT

let rec unit f m = match f with
    | [] -> m
    | c::cs ->
        try let l = List.find (
            fun l' ->
                let c' = List.filter (fun x -> x <> l') c in
                (clause_satified_by c' m) && (is_undefined l' m)
        ) c in l :: m
        with Not_found -> unit cs m

let infer = function
    | Equal(v1, v2, _) -> Equal(v1, v2, true)
    | NotEqual(v1, v2, _)-> NotEqual(v1, v2, true)

let rec decide f m = match f with
    | [] -> m
    | c::cs ->
