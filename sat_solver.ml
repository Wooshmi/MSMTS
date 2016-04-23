open Ast
open Format

type iliteral = {
    lit : literal;
    inferred : clause option }

exception SAT
exception UNSAT
exception Not_possible

(* Printing function *)
let print_literal l =
    if l.equal then
        printf "(%d = %d)" (fst l.vars) (snd l.vars)
    else
        printf "(%d <> %d)" (fst l.vars) (snd l.vars)

let print_m m =
    print_endline "M:";
    List.iter (fun il -> print_literal il.lit) m;
    print_endline ""

let print_r r = 
    print_endline "R:";
    List.iter print_literal r;
    print_endline ""

(* Compare function *)
let lit_compare l1 l2 =
    match Pervasives.compare l1.vars l2.vars with
    | 0 -> Pervasives.compare l1.equal l2.equal
    | c -> c

(* VSIDS heuristic *)
let score = Hashtbl.create 1000

let heuristic_init f =
    List.iter (fun c -> List.iter (fun l -> Hashtbl.replace score l.vars 0) c) f

let heuristic_incr key =
    Hashtbl.replace score key (Hashtbl.find score key + 1)

let heuristic_incr_list l =
    List.iter heuristic_incr l

let heuristic_get_value key =
    Hashtbl.find score key

let iter = ref 0
let period = 500
let ct = 16

let next_iteration () =
    incr iter;
    if !iter > 500 then (
        let l = Hashtbl.fold (fun key value l -> (key, value) :: l) score [] in
        List.iter (fun (key, value) -> Hashtbl.replace score key (value / ct)) l;
        iter := 1
    )

(* Techniques *)
let neg l = 
    { l with equal = not l.equal }

let is_defined l m = List.exists (fun l' -> l'.lit.vars = l.vars) m

let get_value l m =
    let l' = List.find (fun l' -> l'.lit.vars = l.vars) m in
    if l'.lit.equal = l.equal then
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
    formula_satisfied_by (List.map fst f) m

let infer l cl =
    { lit = l; inferred = cl }

let rec unit f m = 
    match f with
    | [] -> raise Not_possible
    | (c, _) :: cs ->
        try 
            let l = List.find (
                fun l' ->
                    let c' = List.map (fun x -> [neg x]) (List.filter (fun x -> x <> l') c) in
                    not (is_defined l' m) && (formula_satisfied_by c' m)
            ) c in (infer l (Some c)) :: m
        with 
        | Not_found -> unit cs m

let rec decide f m =
    let ans = Hashtbl.fold 
        (fun key value ans -> 
            match ans with
            | None -> if not (is_defined { vars = key; equal = true } m) then Some (key, value) else None
            | Some (kans, vans) -> if not (is_defined { vars = key; equal = true } m) && value > vans then Some (key, value) else Some (kans, vans)) score None in
    match ans with
    | None -> raise Not_possible
    | Some (vars, _) -> (infer { vars = vars; equal = true } None) :: m

let rec conflict f m =
    match f with
    | [] -> raise Not_possible
    | (c, _) :: cs -> 
        let c' = List.map (fun x -> [neg x]) c in
        if formula_satisfied_by c' m then
            c
        else
            conflict cs m

let fail f m r = 
    match r with
    | [] -> true
    | _ -> false

let rec resolve f m r =
    match r with
    | [] -> raise Not_possible
    | l :: ls -> 
        let aux = List.filter (fun l' -> l'.lit = neg l) m in
        let rec find a = (
            match a with
            | x :: a' -> (
                match x.inferred with
                | None -> find a'
                | Some cl -> 
                    heuristic_incr x.lit.vars;
                    List.filter (fun lit -> lit.vars <> l.vars) cl
            )
            | [] -> raise Not_found 
        ) in
        try
            let d = find aux in
            ls @ d
        with
        | Not_found -> l :: (resolve f m ls)

let backjump f m r = 
    let rec find_m2 l r' m = (
        match m with
        | [] -> raise Not_found
        | il :: ils ->
            if (il.inferred = None) && not (is_defined l ils) && formula_satisfied_by r' ils then
                ils
            else
                find_m2 l r' ils
    ) in
    let rec backjump_literal_processing rc = (
        match rc with
        | [] -> raise Not_found
        | l :: ls -> 
            let r' = List.map (fun x -> [neg x]) (List.filter (fun x -> x <> l) r) in
            try 
                (infer l (Some r)) :: (find_m2 l r' m)
            with
            | Not_found -> backjump_literal_processing ls
    ) in
    try
        let ans = backjump_literal_processing r in
        heuristic_incr_list (List.map (fun x -> x.vars) r);
        ans
    with
    | Not_found -> raise Not_possible

let rec learn f m r =
    if List.exists (fun c -> fst c = r) f then
        raise Not_possible
    else
        (r, true) :: f

let rec forget f m =
    match f with
    | [] -> raise Not_possible
    | c :: cs -> 
        if snd c then
            cs
        else
            c :: (forget cs m)

let restart f m = []

(* Solve *)
let rec resolution f m r =
    try
        (* Debugging *)
        (*print_endline "Resolution";
        print_m m;
        print_r r; *)
        next_iteration ();
        if fail f m r then
            raise UNSAT;
        try
            let m' = backjump f m r in
            search (learn f m r) m'
        with Not_possible ->
        try
            resolution f m (List.sort_uniq lit_compare (resolve f m r))
        with Not_possible -> raise UNSAT (* ? *)
    with
    | UNSAT -> false

and search f m =
    try
        (* Debugging *)
        (* print_endline "Search";
        print_m m; *)
        next_iteration ();
        if success f m then
            raise SAT;
        try
            search f (unit f m)
        with Not_possible ->
        try
            search f (decide f m)
        with Not_possible ->
        try
            resolution f m (conflict f m)
        with Not_possible -> 
        try
            search (forget f m) m
        with Not_possible -> search f (restart f m)
    with
    | SAT -> true

let solve f = heuristic_init f; search (List.map (fun x -> (x, false)) f) []
