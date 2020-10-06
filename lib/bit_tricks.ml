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

let power_of_two_test ctx =
    let x = BitVector.mk_const ctx (mk_string ctx "x") 32 in

    (* fast = And(x != 0, x & (x - 1) == 0) *)
    let fast =
        Boolean.mk_and ctx
          [
            Boolean.mk_not ctx
              (Boolean.mk_eq ctx x (BitVector.mk_numeral ctx "0" 32));
            Boolean.mk_eq ctx
              (BitVector.mk_and ctx x
                 (BitVector.mk_sub ctx x (BitVector.mk_numeral ctx "1" 32)))
              (BitVector.mk_numeral ctx "0" 32);
          ]
    in
    let powers = List.map (fun i -> 1 lsl i) (List.range 0 `To 31) in
    (* slow = Or([ x == p for p in powers ]) *)
    let slow =
        Boolean.mk_or ctx
          (List.map
             (fun p ->
               Boolean.mk_eq ctx x
                 (BitVector.mk_numeral ctx (string_of_int p) 32))
             powers)
    in

    let solver = mk_solver ctx None in
    (* tries to prove `claim` by showing the negation is unsatisfiable. *)
    Solver.add solver [ Boolean.mk_not ctx (Boolean.mk_eq ctx fast slow) ];
    match check solver [] with
    | UNSATISFIABLE -> Printf.printf "the claim `power_of_two` always holds\n"
    | SATISFIABLE -> Printf.printf "the claim `power_of_two` not always holds\n"
    | UNKNOWN -> Printf.printf "unable to solve the constriants\n"

(* The following simple hack can be used to test whether two machine integers have opposite signs. *)
let opposite_sings_test ctx =
    let x = BitVector.mk_const ctx (mk_string ctx "x") 32 in
    let y = BitVector.mk_const ctx (mk_string ctx "y") 32 in
    let zero = BitVector.mk_numeral ctx "0" 32 in

    let trick = BitVector.mk_slt ctx (BitVector.mk_xor ctx x y) zero in
    let opposite =
        Boolean.mk_or ctx
          [
            Boolean.mk_and ctx
              [ BitVector.mk_slt ctx x zero; BitVector.mk_sge ctx y zero ];
            Boolean.mk_and ctx
              [ BitVector.mk_slt ctx y zero; BitVector.mk_sge ctx x zero ];
          ]
    in

    let solver = mk_solver ctx None in
    (* tries to prove `claim` by showing the negation is unsatisfiable. *)
    Solver.add solver [ Boolean.mk_not ctx (Boolean.mk_eq ctx trick opposite) ];
    match check solver [] with
    | UNSATISFIABLE -> Printf.printf "the claim `opposite_sings` always holds\n"
    | SATISFIABLE ->
        Printf.printf "the claim `opposite_sings` not always holds\n"
    | UNKNOWN -> Printf.printf "unable to solve the constriants\n"

let run_examples () =
    let cfg = [ ("model", "true"); ("proof", "false") ] in
    let ctx = mk_context cfg in
    power_of_two_test ctx;
    opposite_sings_test ctx
