open! O

module Elem = struct
  type t =
    | ParamVar of Syntax.Param_var.t * Syntax.Transparent.mod_unzip_sig
    | Zipper of Syntax.Transparent.zipper
  [@@deriving sexp_of]
end

type t = { cx : Elem.t Bwd.t } [@@deriving sexp_of]

let empty = { cx = Bwd.Emp }
let add_elem (elem : Elem.t) cx = { cx with cx = Bwd.Infix.(cx.cx <: elem) }

let find_param cx param =
  Bwd.find_map cx.cx ~f:(function
    | Elem.ParamVar (param', ty) when [%equal: Syntax.Param_var.t] param param' -> Some ty
    | _ -> None)
;;

let find_var cx var =
  Bwd.find_map cx.cx ~f:(function
    | Elem.Zipper { self; decls } ->
      Bwd.find_map decls ~f:(function
        | Syntax.DeclVal { name; ty } ->
          if [%equal: Syntax.Var.t Syntax.self_prefixed]
               (Syntax.{ prefix = self; var = name } : _ Syntax.self_prefixed)
               var
          then Some ty
          else None
        | _ -> None)
    | _ -> None)
;;

let find_ty_var cx ty_var =
  Bwd.find_map cx.cx ~f:(function
    | Elem.Zipper { self; decls } ->
      Bwd.find_map decls ~f:(function
        | Syntax.DeclType { name; ty } ->
          if [%equal: Syntax.Ty_var.t Syntax.self_prefixed]
               { prefix = self; var = name }
               ty_var
          then Some ty
          else None
        | _ -> None)
    | _ -> None)
;;

let find_mod_var cx mod_var =
  Bwd.find_map cx.cx ~f:(function
    | Elem.Zipper { self; decls } ->
      Bwd.find_map decls ~f:(function
        | Syntax.DeclMod { name; ty } ->
          if [%equal: Syntax.Mod_var.t Syntax.self_prefixed]
               { prefix = self; var = name }
               mod_var
          then Some ty
          else None
        | _ -> None)
    | _ -> None)
;;

let find_mod_ty_var cx mod_ty_var =
  Bwd.find_map cx.cx ~f:(function
    | Elem.Zipper { self; decls } ->
      Bwd.find_map decls ~f:(function
        | Syntax.DeclSig { name; ty } ->
          if [%equal: Syntax.Mod_ty_var.t Syntax.self_prefixed]
               { prefix = self; var = name }
               mod_ty_var
          then Some ty
          else None
        | _ -> None)
    | _ -> None)
;;

let add_to_last_zipper_exn self_var decl cx =
  match cx.cx with
  | Bwd.Snoc (rest, Zipper zipper) when Syntax.Self_var.equal zipper.self self_var ->
    { cx with
      cx = Bwd.snoc rest (Zipper { zipper with decls = Bwd.Infix.(zipper.decls <: decl) })
    }
  | Bwd.Snoc (_, Zipper zipper) ->
    raise_s
      [%message
        "last zipper self var did not match"
          (zipper.self : Syntax.Self_var.t)
          (self_var : Syntax.Self_var.t)]
  | Bwd.Snoc (_, ParamVar (param, _)) ->
    raise_s
      [%message
        "could not find last zipper, found parameter" (param : Syntax.Param_var.t)]
  | Bwd.Emp -> raise_s [%message "context was empty"]
;;

let find_self_var_index_exn self cx =
  let rec go i = function
    | Bwd.Snoc (_, Elem.Zipper { self = self'; _ }) when Syntax.Self_var.equal self self'
      -> i
    | Bwd.Snoc (rest, Elem.Zipper _) -> go (i + 1) rest
    | Bwd.Snoc (rest, Elem.ParamVar _) -> go i rest
    | Bwd.Emp ->
      raise_s
        [%message "could not find self var index" (self : Syntax.Self_var.t) (cx : t)]
  in
  go 0 cx.cx
;;

let current_self_var_exn cx =
  match cx.cx with
  | Bwd.Snoc (_, Zipper zipper) -> zipper.self
  | Bwd.Snoc (_, ParamVar (param, _)) ->
    raise_s
      [%message
        "could not find last zipper, found parameter" (param : Syntax.Param_var.t)]
  | Bwd.Emp -> raise_s [%message "context was empty"]
;;
