type literal = 
    | Equal of int * int
    | Notequal of int * int

type clause = literal list

type expr = clause list

type formula = int * int * expr
