open Lexing
open Format
open Parser

let usage = "Usage: ./msmts file.cnfuf"

let spec = []

let file =
    let file = ref None in
    let set_file s = (
        if not (Filename.check_suffix s ".cnfuf") then
            raise (Arg.Bad "no .cnfuf extension");
        file := Some s) in
    Arg.parse spec set_file usage;
    match !file with
    | Some f -> f
    | None -> Arg.usage spec usage; exit 1

let report (b, e) =
    let l = b.pos_lnum in
    let fc = b.pos_cnum - b.pos_bol + 1 in
    let lc = e.pos_cnum - b.pos_bol + 1 in
    eprintf "File \"%s\", line %d, characters %d-%d:\n" file l fc lc

let () =
    let c = open_in file in
    let lb = Lexing.from_channel c in
    try
        let f = Parser.formula Lexer.token lb in
        close_in c;
        Checker.check f;
        Sat_solver.solve f
    with
    | Lexer.Lexing_error s ->
        report (lexeme_start_p lb, lexeme_end_p lb);
        eprintf "Lexical error: %s@." s;
        exit 1
    | Parser.Error ->
        report (lexeme_start_p lb, lexeme_end_p lb);
        eprintf "Syntax error@.";
        exit 1
    | Checker.Error s ->
        eprintf "Checking error: %s@." s;
        exit 1
    | e ->
        eprintf "Anomaly: %s\n@." (Printexc.to_string e);
        exit 2
