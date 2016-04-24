open Ast
open Format

type iliteral = {
    lit : literal;
    inferred : clause option }

exception SAT
exception UNSAT
exception Not_possible
exception Unexpected_behaviour

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
module Literal = 
    struct
        type t = int * (int * int)
        let compare = Pervasives.compare
    end

module LSet = Set.Make(Literal)

let score = Hashtbl.create 1000

let heuristic_init f =
    List.iter (fun c -> List.iter (fun l -> Hashtbl.replace score l.vars 0) c) f;
    Hashtbl.fold (fun key value set -> LSet.add (value, key) set) score LSet.empty

let heuristic_incr undef key =
    let v = Hashtbl.find score key in
    Hashtbl.replace score key (v + 1);
    if LSet.mem (v, key) undef then
        LSet.add (v + 1, key) (LSet.remove (v, key) undef)
    else
        undef

let heuristic_incr_list undef l =
    List.fold_left (fun undef key -> heuristic_incr undef key) undef l

let heuristic_get_value key =
    Hashtbl.find score key

let iter = ref 0
let period = 10000
let ct = 16

let next_iteration undef =
    incr iter;
    if !iter > period then (
        let l = Hashtbl.fold (fun key value l -> (key, value) :: l) score [] in
        List.iter (fun (key, value) -> Hashtbl.replace score key (value / ct)) l;
        iter := 1;
        LSet.fold (fun (value, key) set -> LSet.add (value / ct, key) set) undef LSet.empty
    )
    else
        undef

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

let success undef f m = 
    formula_satisfied_by (List.map fst f) m

let infer l cl =
    { lit = l; inferred = cl }

let rec unit undef f m = 
    match f with
    | [] -> raise Not_possible
    | (c, _) :: cs ->
        try 
            let l = List.find (
                fun l' ->
                    let c' = List.map (fun x -> [neg x]) (List.filter (fun x -> x <> l') c) in
                    (LSet.mem (Hashtbl.find score l'.vars, l'.vars) undef) && (formula_satisfied_by c' m)
            ) c in 
            LSet.remove (Hashtbl.find score l.vars, l.vars) undef, (infer l (Some c)) :: m
        with 
        | Not_found -> unit undef cs m

let rec decide undef f m =
    try
        let (s, vars) = LSet.max_elt undef in
        LSet.remove (s, vars) undef, (infer { vars = vars; equal = Random.bool () } None) :: m;
    with
    | Not_found -> raise Not_possible

let rec conflict undef f m =
    match f with
    | [] -> raise Not_possible
    | (c, _) :: cs -> 
        let c' = List.map (fun x -> [neg x]) c in
        if formula_satisfied_by c' m then
            undef, c
        else
            conflict undef cs m

let fail undef f m r = 
    match r with
    | [] -> true
    | _ -> false

let rec resolve undef f m r =
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
                    heuristic_incr undef x.lit.vars, List.filter (fun lit -> lit.vars <> l.vars) cl
            )
            | [] -> raise Not_found 
        ) in
        try
            let undef', d = find aux in
            undef', ls @ d
        with
        | Not_found -> 
            let undef', ls' = resolve undef f m ls in
            undef', l :: ls'

let backjump undef f m r = 
    let rec find_m2 l r' m m1 = (
        match m with
        | [] -> raise Not_found
        | il :: ils ->
            if (il.inferred = None) && not (is_defined l ils) && formula_satisfied_by r' ils then
                il :: m1, ils
            else
                find_m2 l r' ils (il :: m1)
    ) in
    let rec backjump_literal_processing rc = (
        match rc with
        | [] -> raise Not_found
        | l :: ls -> 
            let r' = List.map (fun x -> [neg x]) (List.filter (fun x -> x <> l) r) in
            try
                let m1, m2 = find_m2 l r' m [] in
                let new_undef = List.fold_left (fun set x -> LSet.add (Hashtbl.find score x.lit.vars, x.lit.vars) set) undef m1 in
                LSet.remove (Hashtbl.find score l.vars, l.vars) new_undef, (infer l (Some r)) :: m2
            with
            | Not_found -> backjump_literal_processing ls
    ) in
    try
        let undef', m' = backjump_literal_processing r in
        heuristic_incr_list undef' (List.map (fun x -> x.vars) r), m'
    with
    | Not_found -> raise Not_possible

let rec learn f m r =
    if List.exists (fun c -> fst c = r) f then
        raise Not_possible
    else
        (r, true) :: f

let rec forget undef f m =
    match f with
    | [] -> raise Not_possible
    | c :: cs -> 
        if snd c then
            undef, cs
        else
            let undef', cs' = forget undef cs m in
            undef', c :: cs'

let restart undef f m = 
    Hashtbl.fold (fun key value set -> LSet.add (value, key) set) score LSet.empty, []

(* Solve *)
let rval = ref 10000

let rec resolution undef f m r =
    try
        (* Debugging *)
        (*print_endline "Resolution";
        print_m m;
        print_r r; *)
        let undef = next_iteration undef in
        if fail undef f m r then
            raise UNSAT;
        try
            let undef', m' = backjump undef f m r in
            search undef' (learn f m r) m'
        with Not_possible ->
        try
            let undef', r' = resolve undef f m r in
            resolution undef' f m (List.sort_uniq lit_compare r')
        with Not_possible -> raise Unexpected_behaviour
    with
    | UNSAT -> false

and search undef f m =
    try
        (* Debugging *)
        (* print_endline "Search";
        print_m m; *)
        let undef = next_iteration undef in 
        if success undef f m then
            raise SAT;
        if Random.int (!rval) = 42 then (
            let undef', m' = restart undef f m in 
            rval := !rval + !rval / 2;
            search undef' f m'
        ) else (
            try
                let undef', m' = unit undef f m in
                search undef' f m'
            with Not_possible ->
            try
                let undef', m' = decide undef f m in
                search undef' f m'
            with Not_possible ->
            try
                let undef', r = conflict undef f m in 
                resolution undef' f m r
            with Not_possible -> 
            try
                let undef', f' = forget undef f m in
                search undef' f' m
            with Not_possible -> raise Unexpected_behaviour
        )
    with
    | SAT -> true

let solve f =  
    Random.self_init ();
    search (heuristic_init f) (List.map (fun x -> (x, false)) f) []
