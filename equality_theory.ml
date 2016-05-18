open Ast

exception ET_exception of (int * int)

let update_unionfind uf l =
    if l.equal then
        PUF.union uf (fst l.vars - 1) (snd l.vars - 1)
    else
        uf

let is_possible_mod_theory uf l =
    if l.equal then
        true
    else
        let rx, ry = PUF.find uf (fst l.vars - 1), PUF.find uf (snd l.vars - 1) in rx != ry

let verify m uf =
    try
        List.iter (fun l ->
            if not (l.lit.equal) then (
                let rx, ry = PUF.find uf (fst l.lit.vars - 1), PUF.find uf (snd l.lit.vars - 1) in
                if rx = ry then raise (ET_exception l.lit.vars);
            ) else ()) m;
        []
    with ET_exception vars ->
        let rx, ry = PUF.find uf (fst vars - 1), PUF.find uf (snd vars - 1) in
        List.fold_left (fun ls l ->
            if l.lit.equal then (
                let rx', ry' = PUF.find uf (fst l.lit.vars - 1), PUF.find uf (snd l.lit.vars - 1) in
                if rx' = rx || ry' = ry  || rx' = ry || ry' = rx then
                    { l.lit with equal = false } :: ls
                else
                    ls
            ) else
                ls)  [{ vars = vars; equal = true }] m
