open Types
open Format

(*  A new empty equality theory. *)
let new_theory n =
    { eq = PUF.create n; neq = PArr.init n (fun _ -> ISet.empty) }

(*  Updates the theory with the hypothesis l. *)
let update_theory th l =
    if l.equal then ( (* x = y *)
        let x, y = fst l.vars - 1, snd l.vars - 1 in
        let rx, ry = PUF.find th.eq x, PUF.find th.eq y in
        let neweq = PUF.union th.eq rx ry in
        let newrx = PUF.find neweq x in
        let folder oldvar newvar var neq = (
            let neqvar = PArr.get neq var in
            let newneqvar = ISet.add newvar (ISet.remove oldvar neqvar) in
            PArr.set neq var newneqvar
        ) in
        if newrx = rx then ( (* rx is the new root *)
            let neqrx, neqry = PArr.get th.neq rx, PArr.get th.neq ry in
            let newneqrx, newneqry = ISet.union neqrx neqry, ISet.empty in
            let newneq' = ISet.fold (folder ry rx) neqry th.neq in
            let newneq = PArr.set (PArr.set newneq' rx newneqrx) ry newneqry in
            { eq = neweq; neq = newneq }
        ) else ( (* ry is the new root *)
            let neqrx, neqry = PArr.get th.neq rx, PArr.get th.neq ry in
            let newneqrx, newneqry = ISet.empty, ISet.union neqrx neqry in
            let newneq' = ISet.fold (folder rx ry) neqry th.neq in
            let newneq = PArr.set (PArr.set newneq' rx newneqrx) ry newneqry in
            { eq = neweq; neq = newneq }
        )
    ) else ( (* x <> y *)
        let x, y = fst l.vars - 1, snd l.vars - 1 in
        let rx, ry = PUF.find th.eq x, PUF.find th.eq y in
        let neqrx, neqry = PArr.get th.neq rx, PArr.get th.neq ry in
        let newneqrx, newneqry = ISet.add ry neqrx, ISet.add rx neqry in
        let newneq = PArr.set (PArr.set th.neq rx newneqrx) ry newneqry in
        { eq = th.eq; neq = newneq }
    )

(*  Tests if a literal can be added to the model without contradicting the theory. *)
let is_possible_modulo_theory th l =
    if l.equal then (
        let x, y = fst l.vars - 1, snd l.vars - 1 in
        let rx, ry = PUF.find th.eq x, PUF.find th.eq y in
        not (ISet.mem ry (PArr.get th.neq rx))
    ) else (
        let x, y = fst l.vars - 1, snd l.vars - 1 in
        let rx, ry = PUF.find th.eq x, PUF.find th.eq y in 
        rx != ry
    )

(*  Tests if it is possible to deduce x = y. *)
let try_deduce_eq th x y =
    let rx, ry = PUF.find th.eq x, PUF.find th.eq y in
    rx = ry

(*  Tests if it is possible to deduce x <> y. *)
let try_deduce_neq th x y =
    let rx, ry = PUF.find th.eq x, PUF.find th.eq y in
    ISet.mem ry (PArr.get th.neq rx)
