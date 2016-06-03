%{
    open Types
    open Lexing
%}
%token Newline Tequal Tnotequal Eof
%token <int> Variable
%token <int * int> Intro

%start formula
%type <Types.formula> formula

%%
formula:
| info = Intro Newline expr = clause* Eof                       { (fst info, snd info, expr) }

clause:
| l = literal* Newline                                          { l }

literal:
| x = Variable Tequal y = Variable                              { { vars = (x, y); equal = true } }
| x = Variable Tnotequal y = Variable                           { { vars = (x, y); equal = false } }


