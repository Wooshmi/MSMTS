open Types
open Format
open Equality_theory 

exception SAT
exception UNSAT
exception Not_possible

(* Printing function *)
(*===================*)
(*  Prints a literal. *)
let print_literal l =
    if l.equal then
        printf "(%d = %d)" (fst l.vars) (snd l.vars)
    else
        printf "(%d <> %d)" (fst l.vars) (snd l.vars)

(*  Prints the model. *)
let print_model m =
    List.iter (fun il -> print_literal il.lit; printf " ") m;
    printf "\n"
(*==================*)

(* Literal compare function *)
(*==========================*)
let lit_compare l1 l2 =
    match Pervasives.compare l1.vars l2.vars with
    | 0 -> Pervasives.compare l1.equal l2.equal
    | c -> c
(*==========================*)

(* VSIDS heuristic *)
(*=================*)
(*  The key is int * int (the same as the vars parameter of a literal).
    Structure: hashtable that associates to each key its score. *)
let score = Hashtbl.create 1000

(*  Initialises the heuristic. 
    Also creates a Set that contains the undefined keys ordered by their score. *)
let heuristic_init f =
    Hashtbl.clear score;
    List.iter (fun c -> List.iter (fun l -> Hashtbl.replace score l.vars 0) c) f;
    Hashtbl.fold (fun key value set -> ILSet.add (value, key) set) score ILSet.empty

(*  Increases the heuristic score of key. *)
let heuristic_incr undef key =
    let v = Hashtbl.find score key in
    Hashtbl.replace score key (v + 1);
    if ILSet.mem (v, key) undef then
        ILSet.add (v + 1, key) (ILSet.remove (v, key) undef)
    else
        undef

(*  Increases the heuristic score of all the elements of a key list. *)
let heuristic_incr_list undef l =
    List.fold_left (fun undef key -> heuristic_incr undef key) undef l

(*  Recovers the score of a key. *)
let heuristic_get_value key =
    Hashtbl.find score key

(*  Each period iterations, the heuristic scores are divided by ct. *) 
let period = 10000
let ct = 16

(*  Passes to the next iteration and updates the scores if need be. *)
let next_iteration iter undef =
    if iter > period then (
        let l = Hashtbl.fold (fun key value l -> (key, value) :: l) score [] in
        List.iter (fun (key, value) -> Hashtbl.replace score key (value / ct)) l;
        1, ILSet.fold (fun (value, key) set -> ILSet.add (value / ct, key) set) undef ILSet.empty
    )
    else
        (iter + 1), undef
(*=================*)

(* Techniques *)
(*============*)
(*  Returns the negation of the literal l. *)
let neg l =
    { l with equal = not l.equal }

(*  In the following 5 functions the model is treated as either a List or a Map, depending on the situation. 
    The model is transformed into a Map when we have lots of queries - notably for the succes technique. 
    Notation: function' if the model is of type List.t, function otherwise.*)

(*  Tests if a literal l is defined in the model m (List). *)
let is_defined l m = List.exists (fun l' -> l'.lit.vars = l.vars) m

(*  Returns the value of a literal l in a model m (Map). *)
let get_value' l m =
    let v = LMap.find l.vars m in
    if v = l.equal then
        true
    else
        false

(*  Tests whether a clause c is satisfied by a model m (List) or not. *)
let rec clause_satisfied_by' c m =
    match c with
    | [] -> false
    | l :: ls ->
        try
            (get_value' l m) || (clause_satisfied_by' ls m)
        with
        | Not_found -> (clause_satisfied_by' ls m)

(*  Tests whether a formula f is satisfied by a model m (List) or not. *)
let formula_satisfied_by f m =
    let model = List.fold_left (fun m il -> LMap.add il.lit.vars il.lit.equal m) LMap.empty m in
    let rec aux f = begin
        match f with
        | [] -> true
        | c :: cs -> (clause_satisfied_by' c model) && (aux cs)
    end in aux f

(*  Tests whether a formula f is satisfied by a model m (Map) or not. *)
let rec formula_satisfied_by' f m =
    match f with
    | [] -> true
    | c :: cs -> (clause_satisfied_by' c m) && (formula_satisfied_by' cs m)

(*  Extends a literal by adding the clause from which it was inferred and the old value of the theory structure. *)
let extend l cl th =
    { lit = l; inferred = cl; oldth = th }
    
(*  The SUCCESS technique. *)
let success undef f m =
    let model = List.fold_left (fun m il -> LMap.add il.lit.vars il.lit.equal m) LMap.empty m in
    formula_satisfied_by' (List.map (fun { cl = c } -> c) f) model

(*  The T-PROPAGATE technique. *)
let rec t_propagate undef m th = 
    try
        let il = ILSet.max_elt undef in
        let hval, vars = il in 
        let x, y = fst vars - 1, snd vars - 1 in
        if try_deduce_eq th x y then (
            let lit = { vars = vars; equal = true } in
            ILSet.remove il undef, (extend lit None th) :: m, update_theory th lit
        ) else if try_deduce_neq th x y then (
            let lit = { vars = vars; equal = false } in
            ILSet.remove il undef, (extend lit None th) :: m, update_theory th lit
        ) else (
            let undef', m', th' = t_propagate (ILSet.remove il undef) m th in
            ILSet.add il undef', m', th'
        )
    with
    | Not_found -> raise Not_possible

(*  The UNIT technique. *)
let rec unit undef f m th =
    match f with
    | [] -> raise Not_possible
    | { cl = c } :: cs ->
        try
            let l = List.find (
                fun l ->
                    let c' = List.map (fun x -> [neg x]) (List.filter (fun x -> x <> l) c) in
                    (ILSet.mem (Hashtbl.find score l.vars, l.vars) undef) && (formula_satisfied_by c' m) && (is_possible_modulo_theory th l)
            ) c in
            ILSet.remove (Hashtbl.find score l.vars, l.vars) undef, (extend l (Some c) th) :: m, update_theory th l
        with
        | Not_found -> unit undef cs m th

(*  The DECIDE technique. *)
let rec decide undef f m th =
    try
        let il = ILSet.max_elt undef in
        let (s, vars) = il in
        let l = { vars = vars; equal = Random.bool () } in
        if is_possible_modulo_theory th l then
            ILSet.remove (s, vars) undef, (extend l None th) :: m, update_theory th l
        else if is_possible_modulo_theory th (neg l) then
            ILSet.remove (s, vars) undef, (extend (neg l) None th) :: m, update_theory th (neg l) 
        else (
            let undef', m', th' = decide (ILSet.remove il undef) f m th in
            ILSet.add il undef', m', th'
        )
    with
    | Not_found -> raise Not_possible

(*  The CONFLICT technique. *)
let rec conflict undef f m =
    match f with
    | [] -> raise Not_possible
    | { cl = c } :: cs ->
        let c' = List.map (fun x -> [neg x]) c in
        if formula_satisfied_by c' m then
            undef, c
        else
            conflict undef cs m

(*  The FAIL technique. *)
let fail undef f m r =
    match r with
    | [] -> true
    | _ -> false

(*  The RESOLVE technique. *)
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

(*  The BACKJUMP technique. *)
let backjump undef f m r =
    let rec find_m2 l r' m m1 = (
        match m with
        | [] -> raise Not_found
        | il :: ils ->
            if (il.inferred = None) && not (is_defined l ils) && formula_satisfied_by r' ils then
                il.oldth, il :: m1, ils
            else
                find_m2 l r' ils (il :: m1)
    ) in
    let rec backjump_literal_processing rc = (
        match rc with
        | [] -> raise Not_found
        | l :: ls ->
            let r' = List.map (fun x -> [neg x]) (List.filter (fun x -> x <> l) r) in
            try
                let th, m1, m2 = find_m2 l r' m [] in
                let new_undef = List.fold_left (fun set x -> ILSet.add (Hashtbl.find score x.lit.vars, x.lit.vars) set) undef m1 in
                ILSet.remove (Hashtbl.find score l.vars, l.vars) new_undef, (extend l (Some r) th) :: m2, update_theory th l
            with
            | Not_found -> backjump_literal_processing ls
    ) in
    try
        let undef', m', th = backjump_literal_processing r in
        heuristic_incr_list undef' (List.map (fun x -> x.vars) r), m', th
    with
    | Not_found -> raise Not_possible

(*  The LEARN technique. *)
let rec learn f m r =
    if List.exists (fun { cl = c } -> c = r) f then
        raise Not_possible
    else
        { cl = r; learned = true } :: f

(*  The FORGET technique. *)
let rec forget undef f m =
    match f with
    | [] -> raise Not_possible
    | { cl = c; learned = b } :: cs ->
        if b then
            undef, cs
        else
            let undef', cs' = forget undef cs m in
            undef', { cl = c; learned = b } :: cs'

(*  The RESTART technique. *)
let restart n =
    Hashtbl.fold (fun key value set -> ILSet.add (value, key) set) score ILSet.empty, [], new_theory n
(*============*)

(* Solve *)
(*=======*)
(*  Variables' description:
    - rval: The probability of a restart. It starts at 1/10000 and is divided by 1.5 after each succesful restart.
            This value isn't fixed in order to preserve the completeness of the algorithm.
    - iter: The number of the current iteration. Useful for the VSIDS heuristic.
    - undef: A Set with the undefined literals in increasing order of the VSIDS heuristic score.
    - n: The number of variables.
    - f: The formula that we want to satisfy. Clauses might be added by the afore-implemented techniques.
    - m: The model.
    - th: The theory structure.
    - r: The conflict clause.*)

(*  Mode = resolution *)
let rec resolution rval iter undef n f m th r =
    try
        let iter', undef = next_iteration iter undef in
        if fail undef f m r then
            raise UNSAT;
        try
            let undef', m', th' = backjump undef f m r in
            search rval iter' undef' n (learn f m r) m' th'
        with Not_possible ->
        try
            let undef', r' = resolve undef f m r in
            resolution rval iter' undef' n f m th (List.sort_uniq lit_compare r')
        with Not_possible -> begin
            let undef', m', th' = restart n in
            search rval iter' undef' n f m' th'
        end
    with
    | UNSAT -> (print_endline ":("; exit 0)

(* Mode = search *)
and search rval iter undef n f m th =
    try
        let iter', undef = next_iteration iter undef in
        if success undef f m then
            raise SAT
        else (
            if Random.int rval = 42 then (
                let undef', m', th' = restart n in
                search (rval + rval / 2) iter' undef' n f m' th'
            ) else (
                try
                    let undef', m', th' = t_propagate undef m th in
                    search rval iter' undef' n f m' th'
                with Not_possible ->
                try
                    let undef', m', th' = unit undef f m th in
                    search rval iter' undef' n f m' th'
                with Not_possible ->
                try
                    let undef', m', th' = decide undef f m th in
                    search rval iter' undef' n f m' th'
                with Not_possible ->
                try
                    let undef', r = conflict undef f m in
                    resolution rval iter' undef' n f m th r
                with Not_possible ->
                try
                    let undef', f' = forget undef f m in
                    search rval iter' undef' n f' m th
                with Not_possible -> assert false
            )
        )
    with
    | SAT -> (print_model m; exit 1)

(* Main function. *)
let solve (n, _, f) =
    let new_f = List.map (fun x -> { cl = x; learned = false }) f in
    let undef = heuristic_init f in
    Random.self_init ();
    search 10000 0 undef n new_f [] (new_theory n)
(*=======*)
