open Ast
open Sat_solver
open Printf
open Scanf

let read_SAT str =
    let ci = open_in str in
    let header = ref (input_line ci) in
    while (!header).[0] = 'c' do
        header := input_line ci
    done;
    let nb_var, nb_cl = sscanf (!header) "p cnf %d %d " (fun x y -> x, y) in
    let out = ref [] in
    for i = 1 to nb_cl do
        let cl = ref [] in
        let l = ref (fscanf ci " %d " (fun x -> x)) in
        while !l <> 0 do
            cl := ({vars = (abs !l, abs !l); equal = !l > 0})::(!cl);
            l := fscanf ci " %d " (fun x -> x)
        done;
        out := (!cl)::(!out)
    done;
    close_in ci;
    !out

let rec test str answer i fin out =
    if i > fin then
        out
    else
        let f = read_SAT (str ^ (string_of_int i) ^ ".cnf") in
        printf "Test %d: " i; flush stdout;
        let tinit = Unix.gettimeofday () in
        if solve f = answer then begin
            printf "OK in %f sec\n" (Unix.gettimeofday () -. tinit); flush stdout;
            test str answer (i+1) fin (out+1)
        end else begin
            printf "FAIL in %f sec\n" (Unix.gettimeofday () -. tinit); flush stdout;
            test str answer (i+1) fin out
        end

let () =
    printf "SAT 50 variables: \n"; flush stdout;
    let tmp = test "test_sat/50_yes_" true 1 16 0 in
    printf "%d/16\n" tmp; flush stdout;
    printf "UNSAT 50 variables: \n"; flush stdout;
    let tmp = test "test_sat/50_no_" false 1 8 0 in
    printf "%d/8\n" tmp; flush stdout;
    printf "SAT 100 variables: \n"; flush stdout;
    let tmp = test "test_sat/100_yes_" true 1 16 0 in
    printf "%d/16\n" tmp; flush stdout;
    printf "UNSAT 100 variables: \n"; flush stdout;
    let tmp = test "test_sat/100_no_" false 1 8 0 in
    printf "%d/8\n" tmp; flush stdout;
    printf "SAT 200 variables: \n"; flush stdout;
    let tmp = test "test_sat/200_yes_" true 1 16 0 in
    printf "%d/16\n" tmp; flush stdout;
    printf "UNSAT 200 variables : \n"; flush stdout;
    let tmp = test "test_sat/200_no_" false 1 8 0 in
    printf "%d/8\n" tmp; flush stdout
