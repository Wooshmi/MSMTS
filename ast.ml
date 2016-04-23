type literal = {
    vars : int * int;
    equal : bool }

type clause = literal list

type expr = clause list

type formula = int * int * expr
