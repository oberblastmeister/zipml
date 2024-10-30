open! O
module P = Sexp_lang.Pretty

module type Context = sig
  type t

  val of_context : Context.t -> t
  val add_self_var : Syntax.Self_var.t -> t -> t
  val find_self_var_index_exn : Syntax.Self_var.t -> t -> int
  (* val current_self_var_exn : t -> Syntax.Self_var.t*)
end

module Context : Context = struct
  type t = Context.t

  let of_context = Fn.id

  let add_self_var self cx =
    Context.add_elem (Context.Elem.Zipper (Syntax.empty_sig_struct self)) cx
  ;;

  let find_self_var_index_exn = Context.find_self_var_index_exn
end

type st = { u : unit }

let rec pretty_mod_path st (path : Syntax.mod_path) =
  match path with
  | Syntax.PathAccess { prefix; var } ->
    let prefix = pretty_prefix st prefix in
    P.Dot (prefix, P.Atom (Syntax.Mod_var.name var))
  | Syntax.PathParam param -> P.Atom (Syntax.Param_var.name param)
  | Syntax.PathZipperAccess { path; zipper } ->
    let path = pretty_mod_path st path in
    P.(path @.@ Atom "Hidden" @.@ pretty_self_ref st zipper)
  | Syntax.PathApp { funct; arg } ->
    P.list [ pretty_mod_path st funct; pretty_mod_path st arg ]

and pretty_self_ref st (self_ref : Syntax.Self_ref.t) =
  let index =
    self_ref.index
    |> Option.value_exn
         ~message:"Internal error: should have annotated self_refs before calling pretty"
  in
  match index with
  | 0 -> P.Atom "Self"
  | _ ->
    List.range 0 (index - 1)
    |> List.fold_left ~init:(P.Atom "Super") ~f:(fun acc _ -> P.Dot (acc, P.Atom "Super"))

and pretty_prefix st (prefix : Syntax.prefix) =
  match prefix with
  | Syntax.PrefixSelf self -> pretty_self_ref st self
  | Syntax.PrefixPath path -> pretty_mod_path st path
;;

let rec pretty_ty st (ty : Syntax.ty) =
  match ty with
  | Syntax.TyUnit -> P.Atom "unit"
  | Syntax.TyVar { prefix; var } ->
    let prefix = pretty_prefix st prefix in
    P.Dot (prefix, P.Atom (Syntax.Ty_var.name var))
;;

let rec pretty_expr st (expr : Syntax.expr) =
  match expr with
  | Syntax.ExprUnit -> P.Atom "mkunit"
  | Syntax.ExprVar { prefix; var } ->
    let prefix = pretty_prefix st prefix in
    P.Dot (prefix, P.Atom (Syntax.Var.name var))
;;

let rec pretty_mod_bind st (bind : Syntax.mod_bind) =
  match bind with
  | Syntax.BindVal { name; ty; expr } ->
    let items =
      [ P.Atom "val"; P.Atom (Syntax.Var.name name) ]
      @ (match ty with
         | None -> []
         | Some ty -> [ P.Atom ":"; pretty_ty st ty ])
      @ [ pretty_expr st expr ]
    in
    P.list items
  | Syntax.BindType { name; ty } ->
    P.list [ P.Atom "type"; P.Atom (Syntax.Ty_var.name name); pretty_ty st ty ]
  | Syntax.BindMod { name; expr } ->
    P.list
      [ P.Atom "module"
      ; P.Atom (Syntax.Mod_var.name name)
      ; P.Ann P.Ann.IndentLine
      ; pretty_mod_expr st expr
      ]
  | Syntax.BindSig { name; ty } ->
    P.list
      [ P.Atom "module"
      ; P.Atom "type"
      ; P.Atom (Syntax.Mod_ty_var.name name)
      ; P.Ann P.Ann.IndentLine
      ; pretty_mod_unzip_sig st ty
      ]

and pretty_mod_decl st (decl : Syntax.mod_decl) =
  match decl with
  | Syntax.DeclVal { name; ty } ->
    P.list [ P.Atom "val"; P.Atom (Syntax.Var.name name); P.Atom ":"; pretty_ty st ty ]
  | Syntax.DeclType { name; ty } ->
    P.list [ P.Atom "type"; P.Atom (Syntax.Ty_var.name name); pretty_ty st ty ]
  | Syntax.DeclMod { name; ty } ->
    P.list
      [ P.Atom "module"
      ; P.Atom (Syntax.Mod_var.name name)
      ; P.Atom ":"
      ; P.Ann P.Ann.IndentLine
      ; pretty_zip_sig st ty
      ]
  | Syntax.DeclSig { name; ty } ->
    P.list
      [ P.Atom "module"
      ; P.Atom "type"
      ; P.Atom (Syntax.Mod_ty_var.name name)
      ; P.Ann P.Ann.IndentLine
      ; pretty_mod_unzip_sig st ty
      ]

and pretty_zipper st zipper =
  let sig_struct = Syntax.zipper_to_sig_struct zipper in
  pretty_mod_sig_struct st sig_struct

and pretty_mod_sig_struct st ({ self = _; decls } : Syntax.mod_sig_struct) =
  P.list
    ([ P.Atom "sig"; P.Ann P.Ann.IndentLine ]
     @ List.intercalate
         ~sep:[ P.Ann P.Ann.Line ]
         (List.map (Bwd.to_list decls) ~f:(fun d -> pretty_mod_decl st d)))

and pretty_mod_unzip_sig st (ty : Syntax.mod_unzip_sig) =
  match ty with
  | Syntax.SigVar { prefix; var } ->
    let prefix = pretty_prefix st prefix in
    P.Dot (prefix, P.Atom (Syntax.Mod_ty_var.name var))
  | Syntax.SigFunct { param; body_ty } ->
    P.list
      [ P.Atom "functor"
      ; pretty_funct_param st param
      ; P.Ann P.Ann.IndentLine
      ; pretty_zip_sig st body_ty
      ]
  | Syntax.SigStruct sig_struct -> pretty_mod_sig_struct st sig_struct
  | Syntax.SigTransparent { path; ty } ->
    P.list [ P.Atom "="; pretty_mod_path st path; P.Atom "<"; pretty_mod_unzip_sig st ty ]

and pretty_zip_sig st (ty : Syntax.mod_zip_sig) =
  match ty with
  | { zippers = Bwd.Emp; ty } -> pretty_mod_unzip_sig st ty
  | { zippers; ty } ->
    P.list
      ([ P.Atom "zip"; P.Ann P.Ann.IndentLine ]
       @ [ P.list
           @@ List.intersperse ~sep:(P.Ann P.Ann.Line)
           @@ List.map ~f:(pretty_zipper st)
           @@ Bwd.to_list zippers
         ]
       @ [ P.Ann P.Ann.Line ]
       @ [ pretty_mod_unzip_sig st ty ])

and pretty_funct_param st (param : Syntax.funct_param) =
  match param with
  | Syntax.AppParam { name; ty } ->
    P.list [ P.Atom (Syntax.Param_var.name name); P.Atom ":"; pretty_mod_unzip_sig st ty ]
  | Syntax.GenParam -> P.list []

and pretty_mod_expr st (expr : Syntax.mod_expr) =
  match expr with
  | Syntax.ModPath path -> pretty_mod_path st path
  | Syntax.ModGenApp path -> P.list [ pretty_mod_path st path ]
  | Syntax.ModProj { expr; name } ->
    P.Dot (pretty_mod_expr st expr, P.Atom (Syntax.Mod_var.name name))
  | Syntax.ModAnn { expr; ty } ->
    P.list [ P.Atom ":"; pretty_mod_expr st expr; pretty_mod_unzip_sig st ty ]
  | Syntax.ModFunct { param; body } ->
    P.list
      [ P.Atom "functor"
      ; pretty_funct_param st param
      ; P.Ann P.Ann.IndentLine
      ; pretty_mod_expr st body
      ]
  | Syntax.ModStruct { self = _; binds } ->
    P.list
      ([ P.Atom "struct"; P.Ann P.Ann.IndentLine ]
       @ List.map (Bwd.to_list binds) ~f:(fun b -> pretty_mod_bind st b)
       @ [ P.Ann P.Ann.Line ])
;;

let pretty_zip_sig ty = pretty_zip_sig { u = () } ty |> P.to_string
