(*
  Copyright 2020 Rajesh Jayaprakash <rajesh.jayaprakash@gmail.com>

  This file is part of fomega.

  fomega is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  fomega is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with fomega.  If not, see <http://www.gnu.org/licenses/>.
*)

(*
 * command to compile: 'ocamlfind ocamlopt -o fomega -linkpkg -package str fomega.ml main.ml'
*)

open Fomega
open String
   
let main () =
  
  let response = ref "" in

  let start_of_exp = ref 0 in
  let start_of_var_name = ref 0 in
  let end_of_var_name = ref 0 in
  let var_name = ref "" in
  let exp = ref "" in
  let dummy = ref false in

  let terms = Hashtbl.create 100 in
  let types = Hashtbl.create 100 in

  let term_env = Hashtbl.create 100 in
  let type_env = Hashtbl.create 100 in
  
  Printf.printf "Welcome to the fomega interpreter. Type 'help' to display the available commands, 'quit' to exit the interpreter.\n";  
  
  while not (!response = "quit") do

    Printf.printf "fomega> ";

    response := (try read_line () with End_of_file -> Printf.printf "\n"; "quit");
                                   
    if not (!response = "quit") then

      if !response = "" then (* to handle empty newlines *)
        Printf.printf ""
      else if (Str.string_match (Str.regexp "defvar[ \t\r\n]+[a-z]+[ \t\r\n]+") !response 0) then
      begin
        start_of_exp := Str.match_end ();

        (* since the first string_match retured true, this will also return true *)
        dummy := Str.string_match (Str.regexp "defvar[ \t\r\n]+") !response 0;
        start_of_var_name := Str.match_end ();

        (* since the first string_match retured true, this will also return true *)        
        dummy := Str.string_match (Str.regexp "defvar[ \t\r\n]+[a-z]+") !response 0;
        end_of_var_name := Str.match_end ();

        var_name := sub !response !start_of_var_name (!end_of_var_name - !start_of_var_name);
        exp := sub !response !start_of_exp ((length !response) - !start_of_exp);
        
        try
          let (index, v1') = (parse_term !exp 0) in
          let v1 = (evaluate (expand v1' terms types) term_env type_env) in
          let t1 = (match (get_type v1 term_env type_env) with
                    | Some t1' -> t1'
                    | None    -> raise (FOmegaException "Unable to get type of term")) in
          
            Hashtbl.add terms !var_name v1;
            Hashtbl.add term_env !var_name t1 
        with
        | FOmegaException s -> Printf.printf "%s\n" s
        | ParseException  s -> Printf.printf "%s\n" s
        | Failure         s -> Printf.printf "%s\n" s  
      end
      else if (Str.string_match (Str.regexp "[a-z]+[ \t\r\n]+:[ \t\r\n]+") !response 0) then
      begin
        start_of_exp := Str.match_end ();

        start_of_var_name := 0;

        (* since the first string_match retured true, this will also return true *)        
        dummy := Str.string_match (Str.regexp "[a-z]+") !response 0;
        end_of_var_name := Str.match_end ();

        var_name := sub !response !start_of_var_name (!end_of_var_name - !start_of_var_name);
        exp := sub !response !start_of_exp ((length !response) - !start_of_exp);
        
        match Hashtbl.find_opt terms !var_name with
        | Some v -> Printf.printf "%s has already been defined, a type judgement cannot be provided for it.\n" !var_name
        | None   -> try
                      let (l1,v1) = (parse_type !exp 0) in
                        Hashtbl.add term_env !var_name v1
                    with
                    | FOmegaException s -> Printf.printf "%s\n" s
                    | ParseException  s -> Printf.printf "%s\n" s
                    | Failure         s -> Printf.printf "%s\n" s  
      end
      else if (Str.string_match (Str.regexp "[A-Z]+[ \t\r\n]+:[ \t\r\n]+") !response 0) then
      begin
        start_of_exp := Str.match_end ();

        start_of_var_name := 0;

        (* since the first string_match retured true, this will also return true *)        
        dummy := Str.string_match (Str.regexp "[A-Z]+") !response 0;
        end_of_var_name := Str.match_end ();

        var_name := sub !response !start_of_var_name (!end_of_var_name - !start_of_var_name);
        exp := sub !response !start_of_exp ((length !response) - !start_of_exp);

        match Hashtbl.find_opt types !var_name with
        | Some v -> Printf.printf "%s has already been defined, a type judgement cannot be provided for it.\n" !var_name
        | None   -> try
                      let (l1,v1) = (parse_kind !exp 0) in
                        Hashtbl.add type_env !var_name v1
                    with
                    | FOmegaException s -> Printf.printf "%s\n" s
                    | ParseException  s -> Printf.printf "%s\n" s
                    | Failure         s -> Printf.printf "%s\n" s  
      end
      else if (Str.string_match (Str.regexp "deftype[ \t\r\n]+[A-Z]+[ \t\r\n]+") !response 0) then
      begin
        start_of_exp := Str.match_end ();

        (* since the first string_match retured true, this will also return true *)
        dummy := Str.string_match (Str.regexp "deftype[ \t\r\n]+") !response 0;
        start_of_var_name := Str.match_end ();

        (* since the first string_match retured true, this will also return true *)        
        dummy := Str.string_match (Str.regexp "deftype[ \t\r\n]+[A-Z]+") !response 0;
        end_of_var_name := Str.match_end ();

        var_name := sub !response !start_of_var_name (!end_of_var_name - !start_of_var_name);
        exp := sub !response !start_of_exp ((length !response) - !start_of_exp);
        
        try
          let (l1, t1) = (parse_type !exp 0) in
          let k1 = (match (get_kind t1 type_env) with
                    | Some k1' -> k1'
                    | None    -> raise (FOmegaException "Unable to get kind of type")) in
            Hashtbl.add types !var_name t1;
            Hashtbl.add type_env !var_name k1
        with
        | FOmegaException s -> Printf.printf "%s\n" s
        | ParseException  s -> Printf.printf "%s\n" s
        | Failure         s -> Printf.printf "%s\n" s  
      end
      else if (Str.string_match (Str.regexp "unbind[ \t\r\n]+[a-z]+") !response 0) then
      begin

        (* since the first string_match retured true, this will also return true *)        
        dummy := Str.string_match (Str.regexp "unbind[ \t\r\n]+") !response 0;        
        start_of_var_name := Str.match_end ();

        var_name := sub !response !start_of_var_name ((length !response) - !start_of_var_name);
        
        Printf.printf "unbinding %s\n" !var_name;

        Hashtbl.remove terms !var_name;
        Hashtbl.remove term_env !var_name
      end
      else if (Str.string_match (Str.regexp "unbind[ \t\r\n]+[A-Z]+") !response 0) then
      begin
        (* since the first string_match retured true, this will also return true *)        
        dummy := Str.string_match (Str.regexp "unbind[ \t\r\n]+") !response 0;        
        start_of_var_name := Str.match_end ();

        var_name := sub !response !start_of_var_name ((length !response) - !start_of_var_name);
        
        Printf.printf "unbinding %s\n" !var_name;

        Hashtbl.remove types !var_name
      end
      else if !response = "listvars" then
        Hashtbl.iter (fun v e -> Printf.printf "%-5s = %s\n" v (string_of_term e)) terms
      else if !response = "listtypes" then
        Hashtbl.iter (fun v e -> Printf.printf "%-5s = %s\n" v (string_of_type e)) types
      else if !response = "clear" then
      begin
        Hashtbl.clear terms;
        Hashtbl.clear types;
        Hashtbl.clear term_env;
        Hashtbl.clear type_env
      end
      else if !response = "help" then
      begin
        Printf.printf "\nIn addition to expressions in valid fomega syntax, the following commands are available:\n";
        Printf.printf "  defvar <var_name> <definition>        - Define a term variable (var_name should be in lowercase)\n";
        Printf.printf "  deftype <var_name> <definition>       - Define a type variable (var_name should be in uppercase)\n";
        Printf.printf "  <var_name> : <type>                   - Create a term judgement\n";
        Printf.printf "  <var_name> : <kind>                   - Create a type judgement\n";
        Printf.printf "  listvars                              - List existing term variable definitions\n";
        Printf.printf "  listtypes                             - List existing type variable definitions\n";
        Printf.printf "  unbind <var_name>                     - Remove the definition of an existing term/type variable\n";
        Printf.printf "  clear                                 - Clear all definitions and judgements\n";
        Printf.printf "  help                                  - Display this text\n";
        Printf.printf "  quit                                  - Exit the interpreter\n\n";
      end
      else    
        try
          match parse !response with
          | TermEntity term1 -> let term1 = (evaluate (expand term1 terms types) term_env type_env) in
                                  Printf.printf "%s : %s\n" (string_of_term term1) (match (get_type term1 term_env type_env) with
                                                                                    | Some type1 -> (string_of_type type1)
                                                                                    | None       -> raise (ParseException "Unable to get type"))
          (* Printf.printf "%s => %s\n" !response (string_of_term term1) *)
          | _                -> raise (ParseException "Type encountered when expecting term")
        with 
        | FOmegaException s -> Printf.printf "%s\n" s
        | ParseException  s -> Printf.printf "%s\n" s
        | Failure         s -> Printf.printf "%s\n" s
    else                         
      Printf.printf "Bye\n"
  done

let _ = main ()
