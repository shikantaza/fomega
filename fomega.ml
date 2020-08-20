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

open String
open Str
   
exception FOmegaException of string
exception ParseException of string

type term_variable = string

type type_variable = string

type term_binding = term_variable * type_

and

     type_binding = type_variable * kind

and

     type_ = TypeVariable of type_variable
           | ArrowType of type_ * type_
           | Forall of type_binding * type_
           | TAbs of type_binding * type_
           | TApp of type_ * type_

and

     term = TermVariable of term_variable
          | Abs of term_binding * term
          | App of term * term
          | PAbs of type_binding * term
          | PApp of term * type_

and

     kind = TypeKind | ArrowKind of kind * kind

type term_env = Option of (term_variable -> type_)

type type_env = Option of (type_variable -> kind)

type parsed_entity = TermEntity of term
                   | TypeEntity of type_

let empty_env () = Hashtbl.create 100                                
                                 
let get env term1 =
  Hashtbl.find_opt env term1

let update_term_env env term1 (type1 : type_) =
  let new_env = Hashtbl.copy env in
    Hashtbl.add new_env term1 type1; new_env

let update_type_env env type1 (kind1 : kind) =
  let new_env = Hashtbl.copy env in
    Hashtbl.add new_env type1 kind1; new_env
  
let rec equiv_kinds k1 k2 =
  match (k1, k2) with
  | (Some TypeKind, Some TypeKind)                       -> true
  | (Some ArrowKind (k1, k2), Some ArrowKind (k1', k2')) -> equiv_kinds (Some k1) (Some k1') && equiv_kinds (Some k2) (Some k2')
  | _                                                    -> false

let rec string_of_type type1 =
  match type1 with
  | TypeVariable x    -> x
  | ArrowType(t1, t2) -> "(" ^ (string_of_type t1) ^ "->" ^ (string_of_type t2) ^ ")"
  | Forall((t1,k), t2) -> "\\/" ^ t1 ^ ":" ^ (string_of_kind k) ^ "." ^ (string_of_type t2)
  | TAbs((t1,k), t2)    -> "\\" ^ t1 ^ ":" ^ (string_of_kind k) ^ "." ^ (string_of_type t2)
  | TApp(t1, t2)       -> "(" ^ (string_of_type t1) ^ " " ^ (string_of_type t2) ^ ")"

and string_of_kind kind1 =
  match kind1 with
  | TypeKind          -> "*"
  | ArrowKind(k1, k2) -> "(" ^ (string_of_kind k1) ^ "->" ^ (string_of_kind k2) ^ ")"
                                                          
let rec get_kind type1 type_env =
  match type1 with
  | TypeVariable name            -> get type_env name
  | ArrowType (t1, t2)           -> if get_kind t1 type_env = Some TypeKind &&
                                       get_kind t2 type_env = Some TypeKind then
                                      Some TypeKind
                                    else
                                      raise (FOmegaException ("Unable to get kind of ArrowType" ^ " - " ^ (string_of_type type1)))
  | Forall ((var, kind1), type1) -> if get_kind type1 (update_type_env type_env var kind1) = Some TypeKind then
                                      Some TypeKind
                                    else
                                      raise (FOmegaException ("Unable to get kind of Forall" ^ " - " ^ (string_of_type type1)))
  | TAbs ((var, kind1), type1)   -> (match get_kind type1 (update_type_env type_env var kind1) with
                                     | Some k ->  Some (ArrowKind (kind1, k))
                                     | None   ->  raise (FOmegaException ("Unable to get kind of TAbs" ^ " - " ^ (string_of_type type1))))
  | TApp (type1', type2')        -> let k1 = get_kind type1' type_env in
                                    let k2 = get_kind type2' type_env in
                                      (match k1 with
                                       | Some ArrowKind(k2', k) -> if (equiv_kinds k2 (Some k2')) then Some k
                                                                   else raise (FOmegaException ("Kind mismatch in type application" ^ " - " ^ (string_of_type type1)))
                                       | _                      -> raise (FOmegaException ("Type application of non-ArrowType" ^ " - " ^ (string_of_type type1))))

let rec replace_type_var type1 var1 type2 =
  match type1 with
  | TypeVariable v                -> if v = var1 then type2 else type1
  | ArrowType (t1, t2)            -> ArrowType (replace_type_var t1 var1 type2, replace_type_var t2 var1 type2)
  | Forall ((var, kind1), type1') -> if (not (var = var1)) then Forall ((var, kind1), replace_type_var type1' var1 type2) else Forall ((var, kind1), type1')
  | TAbs ((var, kind1), type1')   -> if (not (var = var1)) then TAbs ((var, kind1), replace_type_var type1' var1 type2) else TAbs ((var, kind1), type1')
  | TApp (t1, t2)                 -> TApp (replace_type_var t1 var1 type2, replace_type_var t2 var1 type2)


let rec equiv_types t1 t2 =
  match (t1, t2) with
  | (TypeVariable v1, TypeVariable v2)                 -> v1 = v2
  | (ArrowType (t1', t2'), ArrowType (s1, s2))         -> equiv_types t1' s1 && equiv_types t2' s2
  | (Forall ((a, k1), t1'), Forall((b, k2), t2'))      -> equiv_types t1' (replace_type_var t2' b (TypeVariable a)) && equiv_kinds (Some k1) (Some k2)
  | (TAbs ((a, k1), t1'), TAbs((b, k2), t2'))          -> equiv_types t1' (replace_type_var t2' b (TypeVariable a)) && equiv_kinds (Some k1) (Some k2)
  | (TApp (TAbs ((a, k1), t1'), s1), t2')              -> equiv_types t2' (replace_type_var t1' a s1)
  | (TApp (t1', t2'), TApp (s1, s2))                   -> equiv_types t1' s1 && equiv_types t2' s2
  | (_, _)                                             -> false

let rec replace_term_var term1 var1 term2 =
  match term1 with
  | TermVariable v                -> if v = var1 then term2 else term1
  | Abs ((var, type1), term1')    -> if (not (var = var1)) then Abs((var, type1), replace_term_var term1' var1 term2) else Abs ((var, type1), term1')
  | App (e1, e2)                  -> App (replace_term_var e1 var1 term2, replace_term_var e2 var1 term2)
  | PAbs ((var, kind1), term1')   -> PAbs ((var, kind1), replace_term_var term1' var1 term2)
  | PApp (e1, t2)                 -> PApp (replace_term_var e1 var1 term2, t2)

let rec replace_type_var_in_term term1 var1 type2 =
  match term1 with
  | TermVariable v                -> term1
  | Abs ((var, type1), term1')    -> Abs ((var, replace_type_var type1 var1 type2), replace_type_var_in_term term1' var1 type2)
  | App (e1, e2)                  -> App (replace_type_var_in_term e1 var1 type2, replace_type_var_in_term e2 var1 type2)
  | PAbs ((var, kind1), term1')   -> if (not (var = var1)) then PAbs ((var, kind1), replace_type_var_in_term term1' var1 type2) else PAbs ((var, kind1), term1')
  | PApp (e1, t2)                 -> PApp (replace_type_var_in_term e1 var1 type2, replace_type_var t2 var1 type2)

let rec reduce term1 term_env type_env =
  match term1 with
  | TermVariable v                   -> term1
  | Abs((var, typ), e)               -> Abs((var, (fully_reduce_type typ type_env)), reduce e (update_term_env term_env var (fully_reduce_type typ type_env)) type_env)
  | App(Abs((var, typ), e), e1)      -> (match (get_type e1 term_env type_env) with
                                         | Some type1 -> if not (equiv_types (fully_reduce_type typ type_env) type1) then
                                                           raise (FOmegaException ("Typing error in application" ^ " - " ^ (string_of_term term1)))
                                                         else
                                                           replace_term_var e var e1
                                         | None       -> raise (FOmegaException ("Unable to get type of operand for application" ^ " - " ^ (string_of_term term1))))
  | App(e1, e2)                      -> App(reduce e1 term_env type_env, reduce e2 term_env type_env)
  | PAbs((var, kind), e)             -> PAbs((var, kind), reduce e term_env (update_type_env type_env var kind))
  | PApp(PAbs((var, kind1), e), tau) -> (match (get_kind tau type_env) with
                                         | Some kind1' -> if not (equiv_kinds (Some kind1) (Some kind1')) then
                                                            raise (FOmegaException ("Kinding error in polymorphic application" ^ " - " ^ (string_of_term term1)))
                                                          else    
                                                            replace_type_var_in_term e var tau
                                         | None        -> raise (FOmegaException ("Unable to get kind of operand for polymorphic application" ^ " - " ^ (string_of_term term1))))
  | PApp(e1, t1)                     -> PApp(reduce e1 term_env type_env, t1)

and string_of_term term1 =
  match term1 with
  | TermVariable x    -> x
  | App(e1, e2) -> "(" ^ (string_of_term e1) ^ " " ^ (string_of_term e2) ^ ")"
  | Abs((v, t), e)    -> "\\" ^ v ^ ":" ^ (string_of_type t) ^ "." ^ (string_of_term e)
  | PAbs((t, k), e)   -> "/\\"  ^ t ^ ":" ^ (string_of_kind k) ^ "." ^ (string_of_term e)
  | PApp(e, t)        -> "(" ^ (string_of_term e) ^ " " ^ (string_of_type t) ^ ")"

and get_type_internal term1 term_env type_env =
  match term1 with
  | TermVariable var             -> get term_env var
  | Abs((v1,type1), term2)       -> if (get_kind type1 type_env) = (Some TypeKind) then
                                       match get_type term2 (update_term_env term_env v1 type1) type_env with
                                       | Some typ -> Some (ArrowType(type1, typ))
                                       | None     -> raise (FOmegaException ("Unable to get type of operand of application" ^ " - " ^ (string_of_term term1)))
                                    else
                                      raise (FOmegaException ("Type of binding of abstraction should be of kind '*' (maybe the binding variable's type is unkinded?)" ^ " - " ^ (string_of_term term1)))
  | App(e1, e2)                  -> (match (get_type e2 term_env type_env) with
                                     | Some type2 -> (match (get_type e1 term_env type_env) with
                                                      | Some ArrowType(type1', type2') -> if (equiv_types type1' type2) then
                                                                                            Some type2'
                                                                                          else
                                                                                            raise (FOmegaException ("Type mismatch in application" ^ " - " ^ (string_of_term term1)))
                                                      | _                              -> raise (FOmegaException ("Application of a non-ArrowType" ^ " - " ^ (string_of_term term1))))
                                     | None       -> raise (FOmegaException ("Operand of application is not typed" ^ " - " ^ (string_of_term term1))))
  | PAbs((t1, kind1), term2)     -> (match (get_type term2 term_env (update_type_env type_env t1 kind1)) with
                                     | Some type1 -> Some (Forall((t1, kind1), type1))
                                     | None       -> raise (FOmegaException ("Unable to get type of body of polymorphic abstraction" ^ " - " ^ (string_of_term term1))))
  | PApp(e, sigma)               -> (match (get_type e term_env type_env) with
                                     | Some Forall((alpha, kappa), tau) -> if (get_kind sigma type_env) = Some kappa then
                                                                             Some (replace_type_var tau alpha sigma)
                                                                           else
                                                                             raise (FOmegaException ("Type mismatch in polymorphic application" ^ " - " ^ (string_of_term term1)))
                                     | _                                -> raise (FOmegaException ("Polymorphic application of a non-Forall or untyped term" ^ " - " ^ (string_of_term term1))))

and fully_reduce_type type1 type_env =
  let reduced_type = reduce_type type1 type_env in
    if not (reduced_type = type1) then
      fully_reduce_type reduced_type type_env
    else
      reduced_type
                                  
and get_type term1 term_env type_env =
  match (get_type_internal term1 term_env type_env) with
  | Some typ -> Some (fully_reduce_type typ type_env)
  | _        -> raise (FOmegaException ("Unable to get type of term" ^ " - " ^ (string_of_term term1)))

and reduce_type type1' type_env =
  match type1' with
  | TypeVariable v                         -> TypeVariable v
  | ArrowType (t1, t2)                     -> ArrowType(reduce_type t1 type_env, reduce_type t2 type_env)
  | Forall ((var, kind1), type1)           -> Forall((var, kind1), reduce_type type1 (update_type_env type_env var kind1))
  | TAbs ((var, kind1), type1)             -> TAbs((var, kind1), reduce_type type1 (update_type_env type_env var kind1))
  | TApp(TAbs((var, kind1), type1), type2) -> (match (get_kind type2 type_env) with
                                               | Some kind1' -> if not (equiv_kinds (Some kind1) (Some kind1')) then
                                                                  raise (FOmegaException ("Kinding error while applying type function" ^ " - " ^ (string_of_type type1')))
                                                                else    
                                                                  replace_type_var type1 var type2
                                               | None        -> raise (FOmegaException ("Unable to get kind of operand for applying type function" ^ " - " ^ (string_of_type type1'))))                               
  | TApp (type1, type2)                    -> TApp(reduce_type type1 type_env, reduce_type type2 type_env)
                                    
let is_type e sigma term_env type_env =
  match (get_type e term_env type_env) with
  | Some tau -> ((get_kind tau type_env) = (Some TypeKind)) && (equiv_types tau sigma)
  | None     -> raise (FOmegaException "is_type: unable to get type of argument")
                       
let rec evaluate term1 term_env type_env =
  let reduced_term = reduce term1 term_env type_env in
    if not (reduced_term = term1) then
      evaluate reduced_term term_env type_env
    else
      reduced_term
                       
(*
 * parser functions begin
*)

let first_non_a_z_index str index =
  let rec internal_fn s index accum =
    if index = length s then
      None
    else if not (s.[index] >= 'a' && s.[index] <= 'z') then
      Some accum
    else
      internal_fn s (index+1) (accum + 1)
  in internal_fn str index 0

let first_non_A_Z_index str index =
  let rec internal_fn s index accum =
    if index = length s then
      None
    else if not (s.[index] >= 'A' && s.[index] <= 'Z') then
      Some accum
    else
      internal_fn s (index+1) (accum + 1)
  in internal_fn str index 0

let find_matching_paren s index =

  let exit = ref false in
  let i = ref index in
  let counter = ref 1 in
  let ret_index = ref (-1) in

    while not !exit do

      if s.[!i] = ')' then
        counter := !counter - 1
      else if s.[!i] = '(' then
        counter := !counter + 1;

      if !counter = 0 then
      begin
        ret_index := !i;
        exit := true
      end;

      i := !i + 1;

      if !i = (length s) then
        exit := true;

    done;

  if !ret_index = -1 then
    None
  else
    Some !ret_index

let is_lowercase c =
  c >= 'a' && c <= 'z'

let is_uppercase c =
  c >= 'A' && c <= 'Z'

let rec convert root_term_type lst =
  match root_term_type with
  | None   -> (match lst with
               | []         -> raise (ParseException "Syntax error: no terms or types to parse")
               | [s]        -> parse_term_or_type s
               | e1::e2::[] -> (match parse_term_or_type e1 with
                                | TermEntity term1 -> (match parse_term_or_type e2 with
                                                       | TermEntity term2 -> TermEntity (App(term1, term2))
                                                       | TypeEntity type2 -> TermEntity (PApp(term1, type2)))
                                | TypeEntity type1 -> (match parse_term_or_type e2 with
                                                       | TermEntity term2 -> raise (ParseException "Syntax error: type application to term")
                                                       | TypeEntity type2 -> TypeEntity (TApp(type1, type2))))
               | hd :: tl -> (match parse_term_or_type hd with
                              | TermEntity term1 -> convert (Some (TermEntity term1)) tl
                              | TypeEntity type1 -> convert (Some (TypeEntity type1)) tl))
  | Some x -> (match lst with
               | []       -> x
               | [s]      -> (match x with
                              | TermEntity term1 -> (match parse_term_or_type s with
                                                     | TermEntity term2 -> TermEntity (App(term1, term2))
                                                     | TypeEntity type2 -> TermEntity (PApp(term1, type2)))
                              | TypeEntity type1 -> (match parse_term_or_type s with
                                                     | TermEntity term2 -> raise (ParseException "Syntax error: type application to term")
                                                     | TypeEntity type2 -> TypeEntity (TApp(type1, type2))))
              | hd :: tl -> (match x with
                             | TermEntity term1 -> (match parse_term_or_type hd with
                                                    | TermEntity term2 -> convert (Some (TermEntity (App(term1, term2)))) tl
                                                    | TypeEntity type2 -> convert (Some (TermEntity (PApp(term1, type2)))) tl)
                             | TypeEntity type1 -> (match parse_term_or_type hd with
                                                    | TermEntity term2 -> raise (ParseException "Syntax error: type application to term")
                                                    | TypeEntity type2 -> convert (Some (TypeEntity (TApp(type1, type2)))) tl)))
                
and parse_term s index =

  if s.[index] = '(' then
    match find_matching_paren s (index+1) with               
    | None     -> raise (ParseException "Syntax error: unmatched parens while parsing term")
    | Some pos -> match convert None (split (sub s (index+1) (pos-index-1))) with
                  | TermEntity term1 -> (pos+1, term1)
                  | _                -> raise (ParseException "Syntax error: type encountered when expecting a term")
  else if (s.[index] >= 'a' && s.[index] <= 'z') then
    match first_non_a_z_index s (index+1) with
    | Some pos -> (index + pos + 1, TermVariable (sub s index (pos+1)))
    | None     -> (length s, TermVariable (sub s index ((length s) - index)))
  else if s.[index] = '\\' then
    let (l1, v1) = parse_term s (index+1) in
      if not (s.[l1] = ':') then
        raise (ParseException "Syntax error: colon expected")
      else
       let (l2, v2) = parse_type s (l1+1) in
         if not (s.[l2] = '.') then
           raise (ParseException "Syntax error: period expected")
         else
           let (l3, v3) = parse_term s (l2+1) in
           match v1 with
           | TermVariable var_name -> (l3, Abs((var_name, v2), v3))
           | _                     -> raise (ParseException "Syntax error: binding entity for abstraction should be a term variable")
  else if s.[index] = '/' && s.[index+1] = '\\' then
    let (l1, v1) = parse_type s (index+2) in
      if not (s.[l1] = ':') then
        raise (ParseException "Syntax error: colon expected")
      else
       let (l2, v2) = parse_kind s (l1+1) in
         if not (s.[l2] = '.') then
           raise (ParseException "Syntax error: period expected")
         else
           let (l3, v3) = parse_term s (l2+1) in
           match v1 with
           | TypeVariable var_name -> (l3, PAbs((var_name, v2), v3))
           | _                     -> raise (ParseException "Syntax error: binding entity for polymorphic abstraction should be a type variable")
  else
    raise (ParseException "Syntax error while parsing term")

and parse_type s index =

  if s.[index] = '(' then
    match find_matching_paren s (index+1) with               
    | None     -> raise (ParseException "Syntax error: unmatched parens while parsing type")
    | Some pos -> match convert None (split (sub s (index+1) (pos-index-1))) with
                  | TypeEntity type1 -> if (pos + 1 < (length s)) && (s.[pos+1] = ':' || s.[pos+1] = '.') then
                                          (pos+1, type1)
                                        else if (pos + 2 < (length s)) && s.[pos+1] = '-' && s.[pos+2] = '>' then
                                          let (l1, type2) = parse_type s (pos+3) in
                                            (l1, ArrowType(type1, type2))
                                        else if pos = ((length s) - 1) then
                                          (pos+1, type1)
                                        else
                                          raise (ParseException "Syntax error: invalid character encountered when parsing type")
                  | _                -> raise (ParseException "Syntax error: term encountered when expecting a type")
  else if (s.[index] >= 'A' && s.[index] <= 'Z') then
    match first_non_A_Z_index s (index+1) with
    | Some pos -> if (index+pos+2 < (length s)) && s.[index+pos+1] = '-' && s.[index+pos+2] = '>' then
                    let (l1, type2) = parse_type s (index+pos+3) in
                      (l1, ArrowType(TypeVariable (sub s index (pos+1)), type2))
                  else if (index+pos+1 < (length s)) && (s.[index+pos+1] = ':' || s.[index+pos+1] = '.') then
                    (index+pos+1, TypeVariable (sub s index (pos+1)))
                  else
                    raise (ParseException "Syntax error: invalid character while parsing type")
    | None     -> (length s, TypeVariable (sub s index ((length s) - index)))
  else if s.[index] = '\\' && s.[index+1] = '/' then
    let (l1, v1) = parse_type s (index+2) in
      if not (s.[l1] = ':') then
        raise (ParseException "Syntax error: colon expected")
      else
       let (l2, v2) = parse_kind s (l1+1) in
         if not (s.[l2] = '.') then
           raise (ParseException "Syntax error: period expected")
         else
           let (l3, v3) = parse_type s (l2+1) in
           match v1 with
           | TypeVariable var_name -> (l3, Forall((var_name, v2), v3))
           | _                     -> raise (ParseException "Syntax error: binding entity for forall type should be a type variable")
  else if s.[index] = '\\' then
    let (l1, v1) = parse_type s (index+1) in
      if not (s.[l1] = ':') then
        raise (ParseException "Syntax error: colon expected")
      else
       let (l2, v2) = parse_kind s (l1+1) in
         if not (s.[l2] = '.') then
           raise (ParseException "Syntax error: period expected")
         else
           let (l3, v3) = parse_type s (l2+1) in
           match v1 with
           | TypeVariable var_name -> (l3, TAbs((var_name, v2), v3))
           | _                     -> raise (ParseException "Syntax error: binding entity for type abstraction should be a type variable")
  else
    raise (ParseException "Syntax error: invalid character encountered while parsing type")

and parse_term_or_type str =
  try let (l1,v1) = (parse_term str 0) in
        (TermEntity v1)
  with ParseException s -> try let (l2, v2) = (parse_type str 0) in
                                 (TypeEntity v2)
                           with ParseException s -> raise (ParseException ("Syntax error while parsing term/type: " ^ s))

and parse_kind s index =
  if s.[index] = '(' then
    match find_matching_paren s (index+1) with               
    | None     -> raise (ParseException "Syntax error: unmatched parens while parsing kind")
    | Some pos -> let (l1, kind1) = parse_kind (sub s (index+1) (pos-index-1)) 0 in
                    if (pos + 2 < (length s)) && s.[pos+1] = '-' && s.[pos+2] = '>' then
                      let (l1, kind2) = parse_kind s (pos+3) in
                        (l1, ArrowKind(kind1, kind2))
                    else if pos = ((length s) - 1) then
                      (pos+1, kind1)
                    else
                      raise (ParseException "Syntax error: invalid character encountered when parsing type")
  else if s.[index] = '*' then 
    if (length s) > (index + 2) then (* at least two characters are remaining *)
      if s.[index+1] = '-' && s.[index+2] = '>' then
        let (l1, kind2) = parse_kind s (index+3) in
          (l1, ArrowKind(TypeKind, kind2))
      else if s.[index+1] = '.' then
        (index+1, TypeKind)
      else
        raise (ParseException "Syntax error: period expected after kind")
    else if (length s) > (index + 1) then (* at least one character is remaining *)
      if s.[index+1] = '.' then
        (index+1, TypeKind)
      else
        raise (ParseException "Syntax error: period expected after kind")
    else
      (index+1, TypeKind)
  else 
    raise (ParseException "Syntax error: invalid character encountered while parsing kind")

and split str =

  let is_space c =
    c = ' ' || c = '\r' || c = '\n' || c = '\t' in
  let s = trim str in
  let lst = ref [] in
  let counter = ref 0 in
  let start = ref  0 in
  let i = ref 0 in

    while !i < (length s) do

      if s.[!i] = '(' then counter := !counter + 1
      else if s.[!i] = ')' then counter := !counter - 1
      else if (is_space s.[!i])  && !counter = 0 then
        begin
          lst := (sub s !start (!i - !start)) :: !lst;

          (* to skip multiple spaces *)
          while (is_space s.[!i+1]) do
            i := !i + 1
          done;

          start := !i + 1;

        end;

      i := !i + 1;

    done;

    lst := (sub s !start ((length s) - !start)) :: !lst;

    List.rev !lst

let parse str =
  try convert None (split str) with exn -> raise (ParseException "Exception while parsing (unexpected end of expression?)")

let parse_and_evaluate str term_env type_env =
  match (parse str) with
  | TermEntity term1 -> evaluate term1 term_env type_env
  | _                -> raise (FOmegaException "Attempt to evaluate a type expression")

let rec get_free_term_variables term1 =
  List.sort_uniq compare (match term1 with
                          | TermVariable v    -> [v]
                          | App(e1,e2)        -> (get_free_term_variables e1) @ (get_free_term_variables e2)
                          | Abs((v1,t1), e1)  -> let (l1, l2) = List.partition (fun x -> x = v1) (get_free_term_variables e1) in
                                                   l2
                          | PAbs((v1,t1), e1) -> get_free_term_variables e1
                          | PApp(e1, t1)      -> get_free_term_variables e1)

let rec get_free_type_variables_in_type type1 =
  List.sort_uniq compare (match type1 with
                          | TypeVariable v      -> [v]
                          | TApp(t1,t2)         -> (get_free_type_variables_in_type t1) @ (get_free_type_variables_in_type t2)
                          | TAbs((v1,k1), t1)   -> let (l1, l2) = List.partition (fun x -> x = v1) (get_free_type_variables_in_type t1) in
                                                     l2
                          | Forall((v1,k1), t1) -> let (l1, l2) = List.partition (fun x -> x = v1) (get_free_type_variables_in_type t1) in
                                                     l2
                          | ArrowType(t1, t2)   -> (get_free_type_variables_in_type t1) @ (get_free_type_variables_in_type t2)) (* is this correct? *)

and get_free_type_variables term1 =
  List.sort_uniq compare (match term1 with
                          | TermVariable v    -> []
                          | App(e1,e2)        -> (get_free_type_variables e1) @ (get_free_type_variables e2)
                          | Abs((v1,t1), e1)  -> (get_free_type_variables_in_type t1) @ (get_free_type_variables e1)
                          | PAbs((v1,t1), e1) -> let (l1, l2) = List.partition (fun x -> x = v1) (get_free_type_variables e1) in
                                                   l2
                          | PApp(e1, t1)      -> (get_free_type_variables e1) @ (get_free_type_variables_in_type t1))
                         
let replace_free_vars term1 terms =
  let rec f term1' lst =
    match lst with
    | [] -> term1'
    | hd :: tl -> f (match Hashtbl.find_opt terms hd with
                     | Some v -> replace_term_var term1' hd v
                     | None   -> term1')
                    tl in
  f term1 (get_free_term_variables term1)

let replace_free_types term1 types =
  let rec f term1' lst =
    match lst with
    | [] -> term1'
    | hd :: tl -> f (match Hashtbl.find_opt types hd with
                     | Some v -> replace_type_var_in_term term1' hd v
                     | None   -> term1')
                    tl in
  f term1 (get_free_type_variables term1)

let rec expand term1 terms types =
  let expanded_term = (replace_free_types (replace_free_vars term1 terms) types) in
    if not (expanded_term = term1) then
      expand expanded_term terms types
    else
      expanded_term
  
