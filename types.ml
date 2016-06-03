open Persistent_array
open Persistent_unionfind

(* Types for the equality theory *)
module PUF = Make(Th)
module PArr = Th

module Int =
    struct
        type t = int
        let compare = Pervasives.compare
    end

module ISet = Set.Make(Int)

type theory = {
  eq : PUF.t;
  neq : ISet.t PArr.t
}

(* Abstract syntax tree *)
type literal = {
    vars : int * int;
    equal : bool
}

type clause = literal list

type expr = clause list

type formula = int * int * expr (* (number of variables, number of clauses, expression) *)

(* Types used in the solver *)
type iliteral = {
    lit : literal;
    inferred : clause option;
    oldth : theory
}

type iclause = {
  cl : clause;
  learned : bool
}

module IntLiteralPair =
    struct
        type t = int * (int * int)
        let compare = Pervasives.compare
    end

module ILSet = Set.Make(IntLiteralPair)

module Literal = 
    struct
        type t = int * int
        let compare = Pervasives.compare
    end

module LMap = Map.Make(Literal)
