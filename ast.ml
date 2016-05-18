open Unionfind

module PUF = Make(Th)

type literal = {
    vars : int * int;
    equal : bool }

type clause = literal list

type iliteral = {
    lit : literal;
    inferred : clause option;
    olduf : PUF.t}

type expr = clause list

type formula = int * int * expr (* nb vars, ...*)
