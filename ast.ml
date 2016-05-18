type literal = {
    vars : int * int;
    equal : bool }

type clause = literal list

type iliteral = {
    lit : literal;
    inferred : clause option }

type expr = clause list

type formula = int * int * expr (* nb vars, ...*)
