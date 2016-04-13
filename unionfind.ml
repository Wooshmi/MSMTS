module type PersistentArray = sig
    type 'a t
    val init : int -> (int -> 'a) -> 'a t
    val get : 'a t -> int -> 'a
    val set : 'a t -> int -> 'a -> 'a t
end

module Th : PersistentArray = struct
    type 'a t = 'a data ref
    and 'a data =
        | Arr of 'a array
        | Diff of int * 'a * 'a t
        | Invalid

    let init n f = ref (Arr (Array.init n f))
    
    let rec reroot t =
        match !t with
        | Arr _ -> 
            ()
        | Diff (i, v, t') ->
            reroot t';
            begin
                match !t' with
                | Arr a as n -> 
                    a.(i) <- v;
                    t := n;
                    t' := Invalid
                | Diff _ | Invalid -> 
                    assert false
            end
        | Invalid -> 
            assert false

    let rec get t i =
        match !t with
        | Arr a -> a.(i)
        | Diff _ ->
            reroot t;
            begin
                match !t with
                | Arr a -> 
                    a.(i)
                | _ -> 
                    assert false
            end
        | Invalid -> assert false

    let set t i v =
        reroot t;
        match !t with
        | Arr a as n ->
            let old = a.(i) in
            a.(i) <- v;
            let res = ref n in
            t := Diff (i, old, res);
            res
        | Diff _ | Invalid ->
            assert false
end

module type PersistentUnionFind = sig
    type t
    val create : int -> t
    val find : t -> int -> int
    val union : t -> int -> int -> t
end

module Make(A : PersistentArray) : PersistentUnionFind = struct
    type t = {
        rank : int A.t;
        mutable parent : int A.t
    }

    let create n = {
        rank = A.init n (fun _ -> 0);
        parent = A.init n (fun i -> i)
    }

    let rec find_aux f i =
        let fi = A.get f i in
        if fi = i then
            f, i
        else
            let f, r = find_aux f fi in
            let f = A.set f i r in
            f, r

    let find h x =
        let f, cx = find_aux h.parent x in
        h.parent <- f;
        cx

    let union h x y =
        let cx = find h x in
        let cy = find h y in
        if cx <> cy then
            let rx = A.get h.rank cx in
            let ry = A.get h.rank cy in
            if rx >= ry then { 
                rank = A.set h.rank cx (rx + ry);
                parent = A.set h.parent cy cx }
            else {
                rank = A.set h.rank cy (rx + ry);
                parent = A.set h.parent cx cy }
        else
            h
end
