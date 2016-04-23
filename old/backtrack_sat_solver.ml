open Ast
open Format

exception SAT
exception UNSAT

let print_literal l =
    let str = if l.inferred then " inf" else "" in
    if l.equal then
        printf "%d %d%s" (fst l.vars) (snd l.vars) str
    else
        printf "not %d %d%s" (fst l.vars) (snd l.vars) str 

let rec print_model m =
    match m with
    | [] -> printf "\n"
    | [c] -> print_literal c; printf "\n"
    | c :: cs' -> print_literal c; print_string ", "; print_model cs'

let neg l = 
    { l with equal = not l.equal }

let is_defined l m = List.exists (fun l' -> l'.vars = l.vars) m

let get_value l m =
    let l' = List.find (fun l' -> l'.vars = l.vars) m in
    if l'.equal = l.equal then
        true
    else
        false

let rec clause_satified_by c m = 
    match c with
    | [] -> false
    | l :: ls -> 
        try
            (get_value l m) || (clause_satified_by ls m)
        with
        | Not_found -> false

let rec formula_satisfied_by f m = 
    match f with
    | [] -> true
    | c :: cs -> (clause_satified_by c m) && (formula_satisfied_by cs m)

let success f m = 
    if (formula_satisfied_by f m) then 
        raise SAT

let rec unit f m = 
    match f with
    | [] -> m
    | c :: cs ->
        try 
            let l = List.find (
                fun l' ->
                    let c' = List.map (fun x -> [neg x]) (List.filter (fun x -> x <> l') c) in
                    not (is_defined l' m) && (formula_satisfied_by c' m)
            ) c in l :: m
        with 
        | Not_found -> unit cs m

let infer l = 
    { l with inferred = true }

let rec decide f m = 
    let rec find_literal c = (
        match c with
        | [] -> None
        | l :: ls ->
            if not (is_defined l m) then
                Some l
            else
                find_literal ls
    ) in
    match f with
    | [] -> m
    | c :: cs -> (
        match find_literal c with
        | None -> decide cs m 
        | Some l -> infer l :: m
    )

let rec change_first_decision_literal m =
    match m with
    | [] -> []
    | l :: ls -> 
        if l.inferred then
            { (neg l) with inferred = false } :: ls
        else
            change_first_decision_literal ls

let rec backtrack_or_fail f m =
    match f with
    | [] -> m
    | c :: cs ->
        let c' = List.map (fun x -> [neg x]) c in
        if formula_satisfied_by c' m then 
            let newm = change_first_decision_literal m in
            match newm with
            | [] -> raise UNSAT
            | _ -> newm
        else
            backtrack_or_fail cs m

let rec try_solve f m =
    try
        success f m;
        let m1 = unit f m in
        let m2 = decide f m1 in
        let m3 = backtrack_or_fail f m2 in
        try_solve f m3
    with
    | SAT -> printf "SAT\n"
    | UNSAT -> printf "UNSAT\n"

let solve f = try_solve f []

let () = 
    let l1 = { vars = (1, 1); equal = true; inferred = false } in
    let nl1 = { vars = (1, 1); equal = false; inferred = false } in
    let l2 = { vars = (2, 2); equal = true; inferred = false } in
    let nl2 = { vars = (2, 2); equal = false; inferred = false } in
    let l3 = { vars = (3, 3); equal = true; inferred = false } in
    let nl3 = { vars = (3, 3); equal = false; inferred = false } in
    let l4 = { vars = (4, 4); equal = true; inferred = false } in
    let nl4 = { vars = (4, 4); equal = false; inferred = false } in
    let f1 = [[l1; nl2; nl3]; [l2; nl1; nl3]; [l3; nl1; nl2]] in
    let f2 = [[l1]; [nl1]] in
    let f3 = [[l1; l2]; [l3; l4]; [l1; nl3]; [l2; nl4]] in
        solve f1;
        solve f2;
        solve f3
