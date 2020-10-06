open Batteries
open Z3
module Integer = Arithmetic.Integer

let dog_cat_mouse_test ctx =
    let dog = Integer.mk_const ctx (Symbol.mk_string ctx "dog") in
    let cat = Integer.mk_const ctx (Symbol.mk_string ctx "cat") in
    let mouse = Integer.mk_const ctx (Symbol.mk_string ctx "mouse") in
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

    let open Solver in
    let solver = mk_solver ctx None in
    add solver constraints;
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

let sudoku_test ctx =
    let checkerboard =
        Array.init 9 (fun i ->
            Array.init 9 (fun j ->
                let pos =
                    Symbol.mk_string ctx (Printf.sprintf "(%d, %d)" i j)
                in
                Integer.mk_const ctx pos))
    in
    (* each cell contains a value in {1, ..., 9} *)
    let cells_c =
        let mk cell =
            Boolean.mk_and ctx
              [
                Arithmetic.mk_ge ctx cell (Integer.mk_numeral_i ctx 1);
                Arithmetic.mk_le ctx cell (Integer.mk_numeral_i ctx 9);
              ]
        in
        Array.fold_left
          (fun accu row ->
            Array.fold_left (fun accu cell -> mk cell :: accu) [] row @ accu)
          [] checkerboard
    in

    let rows_c =
        Array.to_list
        @@ Array.map (Boolean.mk_distinct ctx % Array.to_list) checkerboard
    in

    let squres_c =
        let squares =
            let ret = ref [] in
            for i = 0 to 2 do
              for j = 0 to 2 do
                let square = ref [] in
                for i' = 0 to 2 do
                  for j' = 0 to 2 do
                    square :=
                      checkerboard.((3 * i) + i').((3 * j) + j') :: !square
                  done
                done;
                ret := !square :: !ret
              done
            done;
            !ret
        in
        List.map (Boolean.mk_distinct ctx) squares
    in

    let cols_c =
        List.map (Boolean.mk_distinct ctx)
          (List.map
             (fun j ->
               List.fold_left
                 (fun accu i -> checkerboard.(i).(j) :: accu)
                 []
                 (List.range 0 `To 8))
             (List.range 0 `To 8))
    in

    let instance =
        [
          [ 0; 0; 0; 0; 9; 4; 0; 3; 0 ];
          [ 0; 0; 0; 5; 1; 0; 0; 0; 7 ];
          [ 0; 8; 9; 0; 0; 0; 0; 4; 0 ];
          [ 0; 0; 0; 0; 0; 0; 2; 0; 8 ];
          [ 0; 6; 0; 2; 0; 1; 0; 5; 0 ];
          [ 1; 0; 2; 0; 0; 0; 0; 0; 0 ];
          [ 0; 7; 0; 0; 0; 0; 5; 2; 0 ];
          [ 9; 0; 0; 0; 6; 5; 0; 0; 0 ];
          [ 0; 4; 0; 9; 7; 0; 0; 0; 0 ];
        ]
    in
    let instance_c =
        List.fold_lefti
          (fun accu i row ->
            List.fold_lefti
              (fun accu j x ->
                if x = 0 then accu
                else
                  Boolean.mk_eq ctx
                    checkerboard.(i).(j)
                    (Integer.mk_numeral_i ctx x)
                  :: accu)
              [] row
            @ accu)
          [] instance
    in

    let open Solver in
    let solver = mk_solver ctx None in
    add solver (cells_c @ rows_c @ cols_c @ squres_c @ instance_c);
    (* check: solver -> (assumptions:expr list) -> status *)
    (* whats assumptions? *)
    match check solver [] with
    | UNSATISFIABLE -> Printf.printf "not possible to solve the constriants\n"
    | SATISFIABLE -> (
        match get_model solver with
        | Some model ->
            Printf.printf "solved model for `sudoku`: %s\n"
              (Model.to_string model)
        | None -> failwith "unexpected error" )
    | UNKNOWN -> Printf.printf "unable to solve the constriants\n"

let eight_queens ctx =
    let it = List.range 0 `To 7 in
    (* we know that each queen must be at different row,
       so we use quees.(i) to represent to queen positioned at row i *)
    let queens =
        Array.init 8 (fun i ->
            Integer.mk_const ctx
              (Symbol.mk_string ctx (Printf.sprintf "queue_%d" i)))
    in

    (* must be on board *)
    let val_c =
        Array.to_list
        @@ Array.map
             (fun queen ->
               Boolean.mk_and ctx
                 [
                   Arithmetic.mk_ge ctx queen (Integer.mk_numeral_i ctx 1);
                   Arithmetic.mk_le ctx queen (Integer.mk_numeral_i ctx 8);
                 ])
             queens
    in

    let col_c = Boolean.mk_distinct ctx @@ Array.to_list queens in
    let diagnal_c =
        let cc i j =
            Boolean.mk_and ctx
              [
                Boolean.mk_not ctx
                  (Boolean.mk_eq ctx
                     (Arithmetic.mk_sub ctx [ queens.(i); queens.(j) ])
                     (Integer.mk_numeral_i ctx (i - j)));
                Boolean.mk_not ctx
                  (Boolean.mk_eq ctx
                     (Arithmetic.mk_sub ctx [ queens.(j); queens.(i) ])
                     (Integer.mk_numeral_i ctx (j - i)));
              ]
        in
        List.(
          fold_left
            (fun accu i ->
              fold_left
                (fun accu j -> if i = j then accu else cc i j :: accu)
                [] it
              @ accu)
            [] it)
    in

    let open Solver in
    let solver = mk_solver ctx None in
    add solver (val_c @ diagnal_c @ [ col_c ]);
    (* check: solver -> (assumptions:expr list) -> status *)
    (* whats assumptions? *)
    match check solver [] with
    | UNSATISFIABLE -> Printf.printf "not possible to solve the constriants\n"
    | SATISFIABLE -> (
        match get_model solver with
        | Some model ->
            Printf.printf "solved model for `sudoku`: %s\n"
              (Model.to_string model)
        | None -> failwith "unexpected error" )
    | UNKNOWN -> Printf.printf "unable to solve the constriants\n"

let run_examples () =
    let cfg = [ ("model", "true"); ("proof", "false") ] in
    let ctx = mk_context cfg in
    dog_cat_mouse_test ctx;
    sudoku_test ctx;
    eight_queens ctx
