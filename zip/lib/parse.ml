open! O
module Parser = Sexp_lang.Parser.Make (Sexp_lang.Parser.Sexp_error_kind)
module Cst = Sexp_lang.Cst
module Span = Sexp_lang.Span
module List_state = Parser.List_state

let parse_literal lit s =
  let@ s = Parser.string s in
  if String.(s = lit)
  then ()
  else Parser.parse_error [%message "expected " (lit : string)]
;;

let parse_ident_atom (atom : Cst.Atom.t) =
  let s = atom.value in
  Surface.Var.create s
;;

let parse_ty_var_atom (atom : Cst.Atom.t) =
  let s = atom.value in
  Surface.Ty_var.create s
;;

let parse_var s =
  let@ s = Parser.string s in
  Surface.Var.create s
;;

let parse_ty_var s =
  let@ s = Parser.string s in
  Surface.Ty_var.create s
;;

let parse_mod_var s =
  let@ s = Parser.string s in
  if Char.is_uppercase s.[0]
  then Surface.Mod_var.create s
  else Parser.parse_error [%message "expected module ident" ~got:(s : string)]
;;

let parse_mod_ty_var s =
  let@ s = Parser.string s in
  if Char.is_uppercase s.[0]
  then Surface.Mod_ty_var.create s
  else Parser.parse_error [%message "expected module ident" ~got:(s : string)]
;;

let parse_mod_ty_var_atom (atom : Cst.Atom.t) =
  let s = atom.value in
  if Char.is_uppercase s.[0]
  then Surface.Mod_ty_var.create s
  else Parser.parse_error [%message "expected module ident" ~got:(s : string)]
;;

let parse_mod_var_atom (atom : Cst.Atom.t) =
  let s = atom.value in
  if Char.is_uppercase s.[0]
  then Surface.Mod_var.create s
  else Parser.parse_error [%message "expected module ident" ~got:(s : string)]
;;

let optional_ann xs f =
  match List_state.peek xs with
  | None -> None
  | Some (Cst.Atom { value = ":"; _ }) ->
    List_state.next xs |> ignore;
    let next = List_state.next xs in
    let ty = f next in
    Some ty
  | Some _ -> None
;;

let name_or_func s =
  let@ () = Parser.with_s s in
  match s with
  | Cst.Atom { value; _ } -> Either.First value
  | Cst.List list ->
    let@ xs = List_state.with_list list in
    let first = List_state.next xs |> Parser.expect_atom in
    Either.Second (first, List_state.take xs)
  | _ -> Parser.parse_error [%message "expected name or list" ~name:(s : Cst.t)]
;;

let split_functor_sexp xs parse_arg parse_body =
  let rest = List_state.take xs in
  let args, reses =
    List.split_while
      ~f:(fun s ->
        match s with
        | Cst.Atom { value = "->"; _ } -> false
        | _ -> true)
      rest
  in
  let args = List.map ~f:parse_arg args in
  let res =
    let@ xs = List_state.with_list' reses in
    List_state.next xs |> Parser.expect_literal "->";
    let res = List_state.next xs |> parse_body in
    res
  in
  args, res
;;

let rec parse_mod_path s =
  let@ () = Parser.with_s s in
  match s with
  | Cst.List list ->
    let@ xs = List_state.with_list list in
    let funct = List_state.next xs |> parse_mod_path in
    let args = List.map ~f:parse_mod_path (List_state.take xs) in
    Surface.create_path_app funct args
  | Atom atom ->
    let name = parse_mod_var_atom atom in
    PathName name
  | Dot { lhs; rhs; _ } ->
    let path = parse_mod_path lhs in
    let name = parse_mod_var rhs in
    PathAccess { path; name }
  | _ -> Parser.parse_error [%message "expected module path" ~path:(s : Cst.t)]

and optional_ty_ann xs = optional_ann xs parse_ty
and optional_sig_ann xs = optional_ann xs parse_mod_ty

and parse_funct_param s =
  let@ xs = List_state.with_s s in
  match List_state.peek xs with
  | None -> Surface.GenParam
  | Some _ ->
    let name = List_state.next xs |> parse_mod_var in
    List_state.next xs |> Parser.expect_literal ":";
    let ty = List_state.next xs |> parse_mod_ty in
    AppParam { name; ty }

and parse_funct_arg s =
  let@ () = Parser.with_s s in
  match s with
  | Cst.List list ->
    (match list.items with
     | [] -> Surface.GenArg
     | _ :: _ ->
       let arg = parse_mod_expr s in
       Surface.AppArg arg)
  | _ ->
    let arg = parse_mod_expr s in
    Surface.AppArg arg
(* match List_state.peek xs with
  | None -> Surface.GenArg
  | Some _ ->
    let arg = List_state.next xs |> parse_mod_expr in
    List_state.next xs |> Parser.expect_literal ":";
    let ty = List_state.next xs |> parse_mod_ty in
    Surface.AppArg { arg; ty }*)

and parse_mod_name_or_func s =
  let@ () = Parser.with_s s in
  match s with
  | Cst.Atom atom -> Either.First (parse_mod_var_atom atom)
  | Cst.List list ->
    let@ xs = List_state.with_list list in
    let name = List_state.next xs |> parse_mod_var in
    let params = List.map ~f:parse_funct_param (List_state.take xs) in
    Either.Second (name, params)
  | _ -> Parser.parse_error [%message "expected name or list" ~name:(s : Cst.t)]

and parse_mod_bind s =
  let@ xs = List_state.with_s s in
  let first = List_state.next xs |> Parser.expect_atom in
  let res =
    match first.value with
    | "val" ->
      let name = List_state.next xs |> parse_var in
      let ty = optional_ty_ann xs in
      let expr = List_state.next xs |> parse_expr in
      Surface.BindVal { name; ty; expr }
    | "type" ->
      let name = List_state.next xs |> parse_ty_var in
      let ty = List_state.next xs |> parse_ty in
      BindType { name; ty }
    | "module" ->
      (match List_state.peek xs with
       | Some (Cst.Atom { value = "type"; _ }) ->
         List_state.next xs |> ignore;
         let name = List_state.next xs |> parse_mod_ty_var in
         let ty = List_state.next xs |> parse_mod_ty in
         Surface.BindSig { name; ty }
       | _ ->
         let either = List_state.next xs |> parse_mod_name_or_func in
         let expr =
           match List_state.peek xs with
           | Some (Atom { value = ":"; _ }) ->
             List_state.next xs |> ignore;
             let ty = parse_mod_ty @@ List_state.next xs in
             Surface.ModAnn { ty; expr = List_state.next xs |> parse_mod_expr }
           | _ -> List_state.next xs |> parse_mod_expr
         in
         (match either with
          | First name -> Surface.BindMod { name; expr }
          | Second (name, params) ->
            Surface.BindMod { name; expr = Surface.create_funct params expr }))
    | _ -> Parser.parse_error [%message "expected bind" ~bind:(s : Cst.t)]
  in
  res

and parse_mod_decl s : Surface.mod_decl =
  let@ xs = List_state.with_s s in
  let first = List_state.next xs |> Parser.expect_atom in
  match first.value with
  | "val" ->
    let name = List_state.next xs |> parse_var in
    List_state.next xs |> Parser.expect_literal ":";
    let ty = List_state.next xs |> parse_ty in
    Surface.DeclVal { name; ty }
  | "type" ->
    let name = List_state.next xs |> parse_ty_var in
    let ty = List_state.next_opt xs |> Option.map ~f:parse_ty in
    Surface.DeclType { name; ty }
  | "module" ->
    (match List_state.peek xs with
     | Some (Cst.Atom { value = "type"; _ }) ->
       List_state.skip xs;
       let name = List_state.next xs |> parse_mod_ty_var in
       let ty = List_state.next xs |> parse_mod_ty in
       DeclSig { name; ty }
     | _ ->
       let name = List_state.next xs |> parse_mod_var in
       List_state.next xs |> Parser.expect_literal ":";
       let ty = List_state.next xs |> parse_mod_ty in
       Surface.DeclMod { name; ty })
  | _ -> Parser.parse_error [%message "expected mod decl" ~decl:(s : Cst.t)]

and parse_mod_ty s : Surface.mod_sig =
  match s with
  | Cst.List list ->
    let@ xs = List_state.with_list list in
    let first = List_state.next xs |> Parser.expect_atom in
    (match first.value with
     | "sig" -> List.map (List_state.take xs) ~f:parse_mod_decl |> Surface.SigStruct
     | "functor" ->
       let params, res = split_functor_sexp xs parse_funct_param parse_mod_ty in
       Surface.create_funct_ty params res
     | "=" ->
       let path = List_state.next xs |> parse_mod_path in
       List_state.next xs |> Parser.expect_literal "<";
       let ty = List_state.next xs |> parse_mod_ty in
       Surface.SigTransparent { path; ty }
     | _ ->
       Parser.parse_error [%message "expected module type" ~sig_or_functor:(s : Cst.t)])
  | Cst.Atom atom ->
    let name = parse_mod_ty_var_atom atom in
    Surface.SigVar name
  | Cst.Dot { lhs; rhs; _ } ->
    let path = parse_mod_path lhs in
    let name = parse_mod_ty_var rhs in
    Surface.SigAccess { path; name }
  | _ -> Parser.parse_error [%message "Expected module type"]

and parse_mod_expr s =
  let@ () = Parser.with_s s in
  match s with
  | Cst.List list ->
    let@ xs = List_state.with_list list in
    let first = List_state.next xs in
    (match first with
     | Atom { value = "struct"; _ } ->
       let binds = List.map ~f:parse_mod_bind (List_state.take xs) in
       Surface.ModStruct binds
     | Atom { value = "functor"; _ } ->
       let params, res = split_functor_sexp xs parse_funct_param parse_mod_expr in
       Surface.create_funct params res
     | Atom { value = ":"; _ } ->
       let expr = parse_mod_expr (List_state.next xs) in
       let ty = parse_mod_ty (List_state.next xs) in
       Surface.ModAnn { expr; ty }
     | _ ->
       let funct = parse_mod_expr first in
       let args = List.map ~f:parse_funct_arg (List_state.take xs) in
       Surface.create_mod_expr_app funct args)
  | Cst.Dot { lhs; rhs; _ } ->
    let expr = parse_mod_expr lhs in
    let name = parse_mod_var rhs in
    Surface.ModProj { expr; name }
  | _ -> ModPath (parse_mod_path s)

and parse_ty s : Surface.ty =
  match s with
  | Cst.Atom { value = "unit"; _ } -> Surface.TyUnit
  | Cst.Atom atom -> parse_ty_var_atom atom |> Surface.TyVar
  | Cst.Dot { lhs; rhs; _ } ->
    let path = parse_mod_path lhs in
    let name = parse_ty_var rhs in
    Surface.TyAccess { path; name }
  | _ -> Parser.parse_error [%message "invalid type" ~ty:(s : Cst.t)]

and parse_expr s : Surface.expr =
  match s with
  | Cst.List list ->
    let@ xs = List_state.with_list list in
    let first = List_state.next xs |> parse_expr in
    let arg = List_state.next xs |> parse_expr in
    let args = arg :: List.map ~f:parse_expr (List_state.take xs) in
    Surface.create_expr_app first args
  | Cst.Atom { value = "mkunit"; _ } -> Surface.ExprUnit
  | Cst.Atom atom -> parse_ident_atom atom |> ExprVar
  | Cst.Dot { lhs; rhs; _ } ->
    let path = parse_mod_path lhs in
    let name = parse_var rhs in
    Surface.ExprAccess { path; name }
  | _ -> Parser.parse_error [%message "invalid expression" ~expr:(s : Cst.t)]

and parse_program xs =
  let binds = List.map ~f:parse_mod_bind xs in
  Surface.ModStruct binds
;;

let run p s =
  let open Result.Let_syntax in
  let%bind xs = Cst.parse s in
  let%bind expr =
    Parser.run (fun () -> p xs) |> Result.map_error ~f:(fun e -> Error.t_of_sexp e.kind)
  in
  Ok expr
;;

let parse = run parse_program
