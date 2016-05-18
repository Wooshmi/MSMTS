open Ast
open Format
open Equality_theory 

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

let print_model m =
    List.iter (fun il -> print_literal il.lit) m;
    print_newline ()

let print_jumpclause r =
    List.iter print_literal r;
    print_newline ()

(* Compare function *)
let lit_compare l1 l2 =
    match Pervasives.compare l1.vars l2.vars with
    | 0 -> Pervasives.compare l1.equal l2.equal
    | c -> c

(* VSIDS heuristic *)
module ILiteral =
    struct
        type t = int * (int * int)
        let compare = Pervasives.compare
    end

module ILSet = Set.Make(ILiteral)

let score = Hashtbl.create 1000

let heuristic_init f =
    Hashtbl.clear score;
    List.iter (fun c -> List.iter (fun l -> Hashtbl.replace score l.vars 0) c) f;
    Hashtbl.fold (fun key value set -> ILSet.add (value, key) set) score ILSet.empty

let heuristic_incr undef key =
    let v = Hashtbl.find score key in
    Hashtbl.replace score key (v + 1);
    if ILSet.mem (v, key) undef then
        ILSet.add (v + 1, key) (ILSet.remove (v, key) undef)
    else
        undef

let heuristic_incr_list undef l =
    List.fold_left (fun undef key -> heuristic_incr undef key) undef l

let heuristic_get_value key =
    Hashtbl.find score key

let period = 10000
let ct = 16

let next_iteration iter undef =
    if iter > period then (
        let l = Hashtbl.fold (fun key value l -> (key, value) :: l) score [] in
        List.iter (fun (key, value) -> Hashtbl.replace score key (value / ct)) l;
        1, ILSet.fold (fun (value, key) set -> ILSet.add (value / ct, key) set) undef ILSet.empty
    )
    else
        (iter + 1), undef

(* Techniques *)
module Literal = 
    struct
        type t = int * int
        let compare = Pervasives.compare
    end

module LMap = Map.Make(Literal)

let neg l =
    { l with equal = not l.equal }

let is_defined l m = List.exists (fun l' -> l'.lit.vars = l.vars) m

let get_value l m =
    let v = LMap.find l.vars m in
    if v = l.equal then
        true
    else
        false

let rec clause_satisfied_by' c m =
    match c with
    | [] -> false
    | l :: ls ->
        try
            (get_value l m) || (clause_satisfied_by' ls m)
        with
        | Not_found -> (clause_satisfied_by' ls m)


let formula_satisfied_by f m =
    let model = List.fold_left (fun m il -> LMap.add il.lit.vars il.lit.equal m) LMap.empty m in
    let rec aux f = begin
        match f with
        | [] -> true
        | c :: cs -> (clause_satisfied_by' c model) && (aux cs)
    end in aux f

let rec formula_satisfied_by' f m =
    match f with
    | [] -> true
    | c :: cs -> (clause_satisfied_by' c m) && (formula_satisfied_by' cs m)

let success undef f m =
    let model = List.fold_left (fun m il -> LMap.add il.lit.vars il.lit.equal m) LMap.empty m in
    formula_satisfied_by' (List.map fst f) model

let extend l cl uf =
    { lit = l; inferred = cl; olduf = uf }

let rec unit undef f m uf =
    match f with
    | [] -> raise Not_possible
    | (c, _) :: cs ->
        try
            let l = List.find (
                fun l ->
                    let c' = List.map (fun x -> [neg x]) (List.filter (fun x -> x <> l) c) in
                    (ILSet.mem (Hashtbl.find score l.vars, l.vars) undef) && (formula_satisfied_by c' m) && (is_possible_mod_theory uf l)
            ) c in
            ILSet.remove (Hashtbl.find score l.vars, l.vars) undef, (extend l (Some c) uf) :: m, update_unionfind uf l
        with
        | Not_found -> unit undef cs m uf

let rec decide undef f m uf =
    try
        let (s, vars) = ILSet.max_elt undef in
        let l = { vars = vars; equal = Random.bool () } in
        if is_possible_mod_theory uf l then
            ILSet.remove (s, vars) undef, (extend l None uf) :: m, update_unionfind uf l
        else
            ILSet.remove (s, vars) undef, (extend (neg l) None uf) :: m, update_unionfind uf (neg l) 
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
                il.olduf, il :: m1, ils
            else
                find_m2 l r' ils (il :: m1)
    ) in
    let rec backjump_literal_processing rc = (
        match rc with
        | [] -> raise Not_found
        | l :: ls ->
            let r' = List.map (fun x -> [neg x]) (List.filter (fun x -> x <> l) r) in
            try
                let uf, m1, m2 = find_m2 l r' m [] in
                let new_undef = List.fold_left (fun set x -> ILSet.add (Hashtbl.find score x.lit.vars, x.lit.vars) set) undef m1 in
                ILSet.remove (Hashtbl.find score l.vars, l.vars) new_undef, (extend l (Some r) uf) :: m2, update_unionfind uf l
            with
            | Not_found -> backjump_literal_processing ls
    ) in
    try
        let undef', m', uf = backjump_literal_processing r in
        heuristic_incr_list undef' (List.map (fun x -> x.vars) r), m', uf
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

let restart n =
    Hashtbl.fold (fun key value set -> ILSet.add (value, key) set) score ILSet.empty, [], PUF.create n

(* Solve *)
let rec resolution rval iter undef n f m uf r =
    try
        (* Debugging *)
        (*print_endline "Resolution";
        print_model m;
        print_jumpclause r; *)
        let iter', undef = next_iteration iter undef in
        if fail undef f m r then
            raise UNSAT;
        try
            let undef', m', uf' = backjump undef f m r in
            search rval iter' undef' n (learn f m r) m' uf'
        with Not_possible ->
        try
            let undef', r' = resolve undef f m r in
            resolution rval iter' undef' n f m uf (List.sort_uniq lit_compare r')
        with Not_possible -> begin
            let undef', m', uf' = restart n in
            search rval iter' undef' n f m' uf'
        end
    with
    | UNSAT -> (print_endline ":("; exit 0)

and search rval iter undef n f m uf =
    try
        (* Debugging *)
        (* print_endline "Search";
        print_model m; *)
        let iter', undef = next_iteration iter undef in
        if success undef f m then (
            match verify m uf with
            | [] -> raise SAT
            | ls -> let f' = f @ [(ls, false)]  in resolution rval iter undef n f' m uf ls
        ) else (
            if Random.int rval = 42 then (
                let undef', m', uf' = restart n in
                search (rval + rval / 2) iter' undef' n f m' uf'
            ) else (
                try
                    let undef', m', uf' = unit undef f m uf in
                    search rval iter' undef' n f m' uf'
                with Not_possible ->
                try
                    let undef', m', uf' = decide undef f m uf in
                    search rval iter' undef' n f m' uf'
                with Not_possible ->
                try
                    let undef', r = conflict undef f m in
                    resolution rval iter' undef' n f m uf r
                with Not_possible ->
                try
                    let undef', f' = forget undef f m in
                    search rval iter' undef' n f' m uf
                with Not_possible -> assert false
            )
        )
    with
    | SAT -> (print_model m; exit 1)

let solve_th undef n f =
    Random.self_init ();
    search 10000 0 undef n f [] (PUF.create n)

let solve (n, _, f) =
    let new_f = List.map (fun x -> (x, false)) f in
    let undef = heuristic_init f in
    solve_th undef n new_f
