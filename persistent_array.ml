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