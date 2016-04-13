{
    open Parser
    open Lexing

    exception Lexing_error of string

    let newline lexbuf =
        let pos = lexbuf.lex_curr_p in
        lexbuf.lex_curr_p <- { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum } 
}

let digit = ['0'-'9']
let nzdigit = ['1'-'9']
let nznumber = nzdigit digit*

rule token = parse 
| [' ' '\t']+                                                   { token lexbuf }
| '\n'                                                          { newline lexbuf; Newline }
| 'c'                                                           { comment lexbuf }
| "p cnf " (nznumber as nbvars) ' ' (nznumber as nbclauses)     { Intro (int_of_string nbvars, int_of_string nbclauses) }
| nznumber as s                                                 { Variable (int_of_string s) }
| '='                                                           { Tequal }
| "<>"                                                          { Tnotequal }
| eof                                                           { Eof }
| _ as c                                                        { raise (Lexing_error ("Illegal character: " ^ String.make 1 c)) }

and comment = parse
| '\n'                                                          { newline lexbuf; token lexbuf }
| _                                                             { comment lexbuf }

