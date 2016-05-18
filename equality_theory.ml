open Unionfind
open Ast

module P = Make(Th)

exception ET_exception of (int*int)

let verify m n =
    let m = List.map (fun il -> il.lit) m in
    let uf = List.fold_left (fun uf l -> if l.equal then P.union uf (fst l.vars - 1) (snd l.vars - 1) else uf) (P.create n) m in
    try
        List.iter (fun l ->
            if not (l.equal) then (
                let rx, ry = P.find uf (fst l.vars - 1), P.find uf (snd l.vars - 1) in
                if rx = ry then raise (ET_exception l.vars);
            ) else ()) m;
        []
    with ET_exception vars ->
        let rx, ry = P.find uf (fst vars - 1), P.find uf (snd vars - 1) in
        List.fold_left (fun ls l ->
            if l.equal then (
                let rx', ry' = P.find uf (fst l.vars - 1), P.find uf (snd l.vars - 1) in
                if rx' = rx || ry' = ry  || rx' = ry || ry' = rx then
                    { l with equal = false } :: ls
                else
                    ls
            ) else
                ls)  [{ vars = vars; equal = true }] m
