open Core
open Cmdliner

let execute input = Load.load_file input |> Driver.process_sign

let main input =
  try execute input; 0 with
  | Invalid_argument s -> Printf.eprintf "Internal error (invalid argument): %s\n" s; 1
  | Failure s -> Printf.eprintf "Internal error (Failure): %s\n" s; 1
  | Load.Parse_error s -> Printf.eprintf "Frontend error: %s" s; 1
  | Eval.Eval_failed s -> Printf.eprintf "Internal error (Failed to evaluate): %s\n" s; 1
  | Quote.Quote_failed s -> Printf.eprintf "Internal error (Failed to quote): %s\n" s; 1
  | Check.Type_error e ->
    Printf.eprintf "Type error: ";
    Check.pp_error Format.err_formatter e;
    Format.pp_print_flush Format.err_formatter ();
    1

let input_file =
  let doc = "File containing the program to type-check" in
  Arg.(required & pos ~rev:true 0 (some string) None & info [] ~doc ~docv:"FILE")

let info =
  let doc = "TODO" in
  let err_exit = Term.exit_info ~doc:"on an ill-formed types or terms." 1 in
  Term.info "ptt" ~version:"0.0" ~doc ~exits:(err_exit :: Term.default_exits)

let () =
  let t = Term.(const main $ input_file) in
  Term.exit_status @@ Term.eval (t, info)
