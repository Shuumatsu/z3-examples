open Official_exampl
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

let _ =
    try
      if not (Log.open_ "z3.log") then
        raise (TestFailedException "Log couldn't be opened.")
      else (
        Printf.printf "Running Z3 version %s\n" Version.to_string;
        Printf.printf "Z3 full version string: %s\n" Version.full_version;
        let cfg = [ ("model", "true"); ("proof", "false") ] in
        let ctx = mk_context cfg in
        let is = Symbol.mk_int ctx 42 in
        let ss = Symbol.mk_string ctx "mySymbol" in
        let bs = Boolean.mk_sort ctx in
        let ints = Integer.mk_sort ctx in
        let rs = Real.mk_sort ctx in
        let v = Arithmetic.Integer.mk_numeral_i ctx 8000000000 in
        Printf.printf "int symbol: %s\n" (Symbol.to_string is);
        Printf.printf "string symbol: %s\n" (Symbol.to_string ss);
        Printf.printf "bool sort: %s\n" (Sort.to_string bs);
        Printf.printf "int sort: %s\n" (Sort.to_string ints);
        Printf.printf "real sort: %s\n" (Sort.to_string rs);
        Printf.printf "integer: %s\n" (Expr.to_string v);
        basic_tests ctx;
        quantifier_example1 ctx;
        fpa_example ctx;
        Printf.printf "Disposing...\n";
        Gc.full_major () );
      Printf.printf "Exiting.\n";
      exit 0
    with Error msg ->
      Printf.printf "Z3 EXCEPTION: %s\n" msg;
      exit 1
