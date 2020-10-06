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

let kinematic_test ctx =
    let initial_velocity =
        Arithmetic.Real.mk_const ctx (mk_string ctx "initial_velocity")
    in
    let final_velocity =
        Arithmetic.Real.mk_const ctx (mk_string ctx "final_velocity")
    in
    let distance = Arithmetic.Real.mk_const ctx (mk_string ctx "distance") in
    let acceleration =
        Arithmetic.Real.mk_const ctx (mk_string ctx "acceleration")
    in
    let time = Arithmetic.Real.mk_const ctx (mk_string ctx "time") in
    (* the kinematic equations: *)
    (* d == (v_i * t) + (a * (t ** 2) / 2) *)
    (* v_f == v_i + (a * t) *)
    let constraints =
        [
          mk_eq ctx
            (Arithmetic.mk_add ctx
               [
                 initial_velocity; Arithmetic.mk_mul ctx [ acceleration; time ];
               ])
            final_velocity;
          mk_eq ctx
            (Arithmetic.mk_add ctx
               [
                 Arithmetic.mk_mul ctx [ initial_velocity; time ];
                 Arithmetic.mk_div ctx
                   (Arithmetic.mk_mul ctx
                      [
                        acceleration;
                        Arithmetic.mk_power ctx time
                          (Arithmetic.Real.mk_numeral_s ctx "2.0");
                      ])
                   (Arithmetic.Real.mk_numeral_s ctx "2.0");
               ])
            distance;
        ]
    in
    let problem =
        [
          mk_eq ctx initial_velocity (Arithmetic.Real.mk_numeral_s ctx "30.0");
          mk_eq ctx final_velocity (Arithmetic.Real.mk_numeral_s ctx "0.0");
          mk_eq ctx acceleration (Arithmetic.Real.mk_numeral_s ctx "-8.0");
        ]
    in

    let solver = mk_solver ctx None in
    Solver.add solver (constraints @ problem);
    (* check: solver -> (assumptions:expr list) -> status *)
    (* whats assumptions? *)
    match check solver [] with
    | UNSATISFIABLE -> Printf.printf "not possible to solve the constriants\n"
    | SATISFIABLE -> (
        match get_model solver with
        | Some model ->
            Printf.printf "solved model: %s\n" (Model.to_string model)
        | None -> failwith "unexpected error" )
    | UNKNOWN -> Printf.printf "unable to solve the constriants\n"

let run_example () =
    let cfg = [ ("model", "true"); ("proof", "false") ] in
    let ctx = mk_context cfg in
    kinematic_test ctx
