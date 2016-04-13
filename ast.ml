type literal =
    | Equal of int * int * bool
    | NotEqual of int * int * bool 

type clause = literal list

type expr = clause list

type formula = int * int * expr
