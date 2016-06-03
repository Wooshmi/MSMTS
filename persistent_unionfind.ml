open Persistent_array

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
            if rx > ry then 
                { h with parent = A.set h.parent cy cx }
            else if ry > rx then
                { h with parent = A.set h.parent cx cy }
            else 
                { rank = A.set h.rank cy (rx + 1);
                parent = A.set h.parent cx cy }
        else
            h
end
