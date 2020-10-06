open Batteries
open Z3
open Z3.Symbol
open Z3.Sort
open Z3.Expr
open Z3.Boolean
open Z3.FuncDecl
open Z3.Goal
open Z3.Tactic
open Z3.Tactic.ApplyResult
open Z3.Probe
open Z3.Solver
open Z3.Arithmetic
open Z3.Arithmetic.Integer
open Z3.Arithmetic.Real
open Z3.BitVector

let dog_cat_mouse_test ctx =
    let dog = Integer.mk_const ctx (mk_string ctx "dog") in
    let cat = Integer.mk_const ctx (mk_string ctx "cat") in
    let mouse = Integer.mk_const ctx (mk_string ctx "mouse") in
    let constraints =
        [
          Arithmetic.mk_ge ctx dog (Integer.mk_numeral_i ctx 1);
          Arithmetic.mk_ge ctx cat (Integer.mk_numeral_i ctx 1);
          Arithmetic.mk_ge ctx mouse (Integer.mk_numeral_i ctx 1);
          Boolean.mk_eq ctx
            (Arithmetic.mk_add ctx [ dog; cat; mouse ])
            (Integer.mk_numeral_i ctx 100);
          Boolean.mk_eq ctx
            (Arithmetic.mk_add ctx
               [
                 Arithmetic.mk_mul ctx [ dog; Integer.mk_numeral_i ctx 1500 ];
                 Arithmetic.mk_mul ctx [ cat; Integer.mk_numeral_i ctx 100 ];
                 Arithmetic.mk_mul ctx [ mouse; Integer.mk_numeral_i ctx 25 ];
               ])
            (Integer.mk_numeral_i ctx 10000);
        ]
    in

    let solver = mk_solver ctx None in
    Solver.add solver constraints;
    (* check: solver -> (assumptions:expr list) -> status *)
    (* whats assumptions? *)
    match check solver [] with
    | UNSATISFIABLE -> Printf.printf "not possible to solve the constriants\n"
    | SATISFIABLE -> (
        match get_model solver with
        | Some model ->
            Printf.printf "solved model for `dog_cat_mouse`: %s\n"
              (Model.to_string model)
        | None -> failwith "unexpected error" )
    | UNKNOWN -> Printf.printf "unable to solve the constriants\n"

let run_examples () =
    let cfg = [ ("model", "true"); ("proof", "false") ] in
    let ctx = mk_context cfg in
    dog_cat_mouse_test ctx
