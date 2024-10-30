open! O

module E = Effects.Error.Make (struct
    type t = Sexp.t
  end)

module type Context = sig
  type t [@@deriving sexp_of]

  val empty : Syntax.Self_var.t -> t
  val add_elem : Surface.ident -> t -> t
  val find_mod_var_opt : t -> Surface.Mod_var.t -> Syntax.mod_path option
  val find_mod_var : t -> Surface.Mod_var.t -> Syntax.mod_path

  val find_mod_ty_var_opt
    :  t
    -> Surface.Mod_ty_var.t
    -> Syntax.Mod_ty_var.t Syntax.prefixed option

  val find_mod_ty_var : t -> Surface.Mod_ty_var.t -> Syntax.Mod_ty_var.t Syntax.prefixed
  val find_var_opt : t -> Surface.Var.t -> Syntax.Var.t Syntax.prefixed option
  val find_ty_var_opt : t -> Surface.Ty_var.t -> Syntax.Ty_var.t Syntax.prefixed option
  val find_ty_var : t -> Surface.Ty_var.t -> Syntax.Ty_var.t Syntax.prefixed
  val find_ty_var : t -> Surface.Ty_var.t -> Syntax.Ty_var.t Syntax.prefixed
  val set_self : Syntax.Self_var.t -> t -> t
  val get_self : t -> Syntax.Self_var.t
end

module Context : Context = struct
  module Elem_pair = struct
    type t =
      | ModVar of Surface.Mod_var.t * Syntax.Mod_var.t Syntax.prefixed
      | ModTyVar of Surface.Mod_ty_var.t * Syntax.Mod_ty_var.t Syntax.prefixed
      | Param of Surface.Mod_var.t * Syntax.Param_var.t
      | Var of Surface.Var.t * Syntax.Var.t Syntax.prefixed
      | TyVar of Surface.Ty_var.t * Syntax.Ty_var.t Syntax.prefixed
    [@@deriving sexp_of]
  end

  type t =
    { cx : Elem_pair.t list
    ; self : Syntax.Self_var.t
    }
  [@@deriving sexp_of]

  let empty self = { cx = []; self }
  let set_self self cx = { cx with self }
  let get_self cx = cx.self

  let add_elem (elem : Surface.ident) cx =
    match elem with
    | Param var ->
      let exists =
        List.exists cx.cx ~f:(function
          | Elem_pair.Param (var', _) -> Surface.Mod_var.equal var var'
          | _ -> false)
      in
      if exists
      then E.raise [%message "module parameter already defined" (var : Surface.Mod_var.t)]
      else
        { cx with cx = Elem_pair.Param (var, Syntax.Param_var.of_surface var) :: cx.cx }
    | ModVar var ->
      let var' = Syntax.Mod_var.of_surface var in
      let prefixed =
        Syntax.{ prefix = PrefixSelf (Self_ref.create cx.self); var = var' }
      in
      let exists =
        List.exists cx.cx ~f:(function
          | Elem_pair.ModVar (_, prefixed') ->
            [%equal: Syntax.Mod_var.t Syntax.prefixed] prefixed prefixed'
          | _ -> false)
      in
      if exists
      then
        E.raise
          [%message
            "module variable already defined in the same scope" (var : Surface.Mod_var.t)]
      else { cx with cx = Elem_pair.ModVar (var, prefixed) :: cx.cx }
    | ModTyVar var ->
      let var' = Syntax.Mod_ty_var.of_surface var in
      let prefixed =
        Syntax.{ prefix = PrefixSelf (Self_ref.create cx.self); var = var' }
      in
      let exists =
        List.exists cx.cx ~f:(function
          | Elem_pair.ModTyVar (_, prefixed') ->
            [%equal: Syntax.Mod_ty_var.t Syntax.prefixed] prefixed prefixed'
          | _ -> false)
      in
      if exists
      then
        E.raise
          [%message
            "module type variable already defined in the same scope"
              (var : Surface.Mod_ty_var.t)]
      else { cx with cx = Elem_pair.ModTyVar (var, prefixed) :: cx.cx }
    | Var var ->
      let var' = Syntax.Var.of_surface var in
      let prefixed =
        Syntax.{ prefix = PrefixSelf (Self_ref.create cx.self); var = var' }
      in
      let exists =
        List.exists cx.cx ~f:(function
          | Elem_pair.Var (_, prefixed') ->
            [%equal: Syntax.Var.t Syntax.prefixed] prefixed prefixed'
          | _ -> false)
      in
      if exists
      then
        E.raise
          [%message "variable already defined in the same scope" (var : Surface.Var.t)]
      else { cx with cx = Elem_pair.Var (var, prefixed) :: cx.cx }
    | TyVar var ->
      let var' = Syntax.Ty_var.of_surface var in
      let prefixed =
        Syntax.{ prefix = PrefixSelf (Self_ref.create cx.self); var = var' }
      in
      let exists =
        List.exists cx.cx ~f:(function
          | Elem_pair.TyVar (_, prefixed') ->
            [%equal: Syntax.Ty_var.t Syntax.prefixed] prefixed prefixed'
          | _ -> false)
      in
      if exists
      then
        E.raise
          [%message
            "type variable already defined in the same scope" (var : Surface.Ty_var.t)]
      else { cx with cx = Elem_pair.TyVar (var, prefixed) :: cx.cx }
  ;;

  let find_mod_var_opt cx mod_var =
    List.find_map cx.cx ~f:(function
      | Elem_pair.ModVar (var, prefixed) ->
        if [%equal: Surface.Mod_var.t] var mod_var
        then Some (Syntax.PathAccess prefixed)
        else None
      | Elem_pair.Param (var, param_var) ->
        if [%equal: Surface.Mod_var.t] var mod_var
        then Some (Syntax.PathParam param_var)
        else None
      | _ -> None)
  ;;

  let find_mod_var cx mod_var =
    find_mod_var_opt cx mod_var
    |> Option.value_or_thunk ~default:(fun () ->
      E.raise [%message "unbound module variable" ~mod_var:(mod_var : Surface.Mod_var.t)])
  ;;

  let find_var_opt cx var =
    List.find_map cx.cx ~f:(function
      | Elem_pair.Var (var', prefixed) ->
        if Surface.Var.equal var var' then Some prefixed else None
      | _ -> None)
  ;;

  let find_ty_var_opt cx ty_var =
    List.find_map cx.cx ~f:(function
      | Elem_pair.TyVar (var', prefixed) ->
        if Surface.Ty_var.equal ty_var var' then Some prefixed else None
      | _ -> None)
  ;;

  let find_ty_var cx ty_var =
    find_ty_var_opt cx ty_var
    |> Option.value_or_thunk ~default:(fun () ->
      E.raise [%message "unbound type variable" ~ty_var:(ty_var : Surface.Ty_var.t)])
  ;;

  let find_mod_ty_var_opt cx mod_ty_var =
    List.find_map cx.cx ~f:(function
      | Elem_pair.ModTyVar (var, prefixed) ->
        if [%equal: Surface.Mod_ty_var.t] var mod_ty_var then Some prefixed else None
      | _ -> None)
  ;;

  let find_mod_ty_var cx mod_ty_var =
    find_mod_ty_var_opt cx mod_ty_var
    |> Option.value_or_thunk ~default:(fun () ->
      E.raise
        [%message
          "unbound module type variable" ~mod_ty_var:(mod_ty_var : Surface.Mod_ty_var.t)])
  ;;
end

type st =
  { cx : Context.t
  ; next_self_var_id : int ref
  ; next_mod_var_id : int ref
  }
[@@deriving sexp_of]

let create_state () =
  { cx = Context.empty (Syntax.Self_var.create ~id:1 "top")
  ; next_self_var_id = ref 2
  ; next_mod_var_id = ref 0
  }
;;

let fresh_self_var ?(name = "self") st =
  let id = !(st.next_self_var_id) in
  incr st.next_self_var_id;
  Syntax.Self_var.create ~id name
;;

let fresh_mod_var ?(name = "Mod") st =
  let id = !(st.next_mod_var_id) in
  incr st.next_mod_var_id;
  Surface.Mod_var.create ~id name
;;

let rec rename_path st (path : Surface.mod_path) =
  match path with
  | Surface.PathName var ->
    let path = Context.find_mod_var st.cx var in
    path
  | Surface.PathAccess { path; name } ->
    let path = rename_path st path in
    Syntax.PathAccess { prefix = PrefixPath path; var = Syntax.Mod_var.of_surface name }
  | Surface.PathApp { funct; arg } ->
    Syntax.PathApp { funct = rename_path st funct; arg = rename_path st arg }

and rename_funct_param st param =
  match param with
  | Surface.AppParam { name; ty } ->
    let param = Syntax.Param_var.of_surface name in
    Syntax.AppParam { name = param; ty = rename_mod_sig st ty }
  | Surface.GenParam -> Syntax.GenParam

and rename_ty st (ty : Surface.ty) =
  match ty with
  | Surface.TyUnit -> Syntax.TyUnit
  | Surface.TyVar ty_var ->
    let ty_var = Context.find_ty_var st.cx ty_var in
    Syntax.TyVar ty_var
  | Surface.TyAccess { path; name } ->
    let path = rename_path st path in
    let name = Syntax.Ty_var.of_surface name in
    Syntax.TyVar Syntax.{ prefix = PrefixPath path; var = name }

and rename_expr st (expr : Surface.expr) =
  match expr with
  | Surface.ExprUnit -> Syntax.ExprUnit
  | Surface.ExprVar var ->
    let var = Context.find_var_opt st.cx var in
    Syntax.ExprVar (Option.value_exn var)
  | Surface.ExprApp { func; arg } -> todo ~loc:[%here] ()
  | Surface.ExprAccess { path; name } ->
    let path = rename_path st path in
    let name = Syntax.Var.of_surface name in
    Syntax.ExprVar Syntax.{ prefix = PrefixPath path; var = name }

and rename_mod_bind st (bind : Surface.mod_bind) =
  match bind with
  | Surface.BindVal { name; ty; expr } ->
    let name = Syntax.Var.of_surface name in
    let ty = Option.map ty ~f:(rename_ty st) in
    let expr = rename_expr st expr in
    Syntax.BindVal { name; ty; expr }
  | Surface.BindType { name; ty } ->
    let name = Syntax.Ty_var.of_surface name in
    let ty = rename_ty st ty in
    Syntax.BindType { name; ty }
  | Surface.BindMod { name; expr } ->
    let name = Syntax.Mod_var.of_surface name in
    let expr = rename_mod_expr st expr in
    Syntax.BindMod { name; expr }
  | Surface.BindSig { name; ty } ->
    let name = Syntax.Mod_ty_var.of_surface name in
    let ty = rename_mod_sig st ty in
    Syntax.BindSig { name; ty }

and add_bind_cx cx bind =
  match bind with
  | Surface.BindVal { name; _ } -> Context.add_elem (Var name) cx
  | Surface.BindType { name; _ } -> Context.add_elem (TyVar name) cx
  | Surface.BindMod { name; _ } -> Context.add_elem (ModVar name) cx
  | Surface.BindSig { name; _ } -> Context.add_elem (ModTyVar name) cx

and add_decl_cx cx decl =
  match decl with
  | Surface.DeclVal { name; _ } -> Context.add_elem (Var name) cx
  | Surface.DeclType { name; _ } -> Context.add_elem (TyVar name) cx
  | Surface.DeclMod { name; _ } -> Context.add_elem (ModVar name) cx
  | Surface.DeclSig { name; _ } -> Context.add_elem (ModTyVar name) cx

and add_param_cx cx param =
  match param with
  | Surface.AppParam { name; _ } -> Context.add_elem (Param name) cx
  | Surface.GenParam -> cx

and rename_mod_binds st binds =
  match binds with
  | [] -> []
  | bind :: binds ->
    let bind' = rename_mod_bind st bind in
    let binds' = rename_mod_binds { st with cx = add_bind_cx st.cx bind } binds in
    bind' :: binds'

and rename_mod_decls st decls =
  match decls with
  | [] -> []
  | decl :: decls ->
    let decl' = rename_mod_decl st decl in
    let decls' = rename_mod_decls { st with cx = add_decl_cx st.cx decl } decls in
    decl' :: decls'

and expr_to_path expr =
  let open Option.Let_syntax in
  match expr with
  | Surface.ModPath path -> Some path
  | Surface.ModProj { expr; name } ->
    let%bind path = expr_to_path expr in
    Some (Surface.PathAccess { path; name })
  | Surface.ModApp { expr; arg = AppArg arg } ->
    let%bind funct = expr_to_path expr in
    let%bind arg = expr_to_path arg in
    Some (Surface.PathApp { funct; arg })
  | Surface.ModLet _ | Surface.ModAnn _
  | Surface.ModApp { arg = GenArg; _ }
  | Surface.ModFunct _ | Surface.ModStruct _ -> None

and rename_mod_expr st (expr : Surface.mod_expr) =
  match expr with
  | Surface.ModPath path -> Syntax.ModPath (rename_path st path)
  | Surface.ModLet { name; expr; body } ->
    let body_var = fresh_mod_var ~name:"body" st in
    let desugared =
      Surface.ModProj
        { expr =
            Surface.ModStruct
              [ Surface.BindMod { name; expr }
              ; Surface.BindMod { name = body_var; expr = body }
              ]
        ; name = body_var
        }
    in
    rename_mod_expr st desugared
  | Surface.ModProj { expr; name } ->
    let expr = rename_mod_expr st expr in
    Syntax.ModProj { expr; name = Syntax.Mod_var.of_surface name }
  | Surface.ModAnn { expr; ty } ->
    let expr = rename_mod_expr st expr in
    let ty = rename_mod_sig st ty in
    Syntax.ModAnn { expr; ty }
  (* | Surface.ModAnn { expr; ty } ->
    (match expr_to_path expr with
     | Some path ->
       let path = rename_path st path in
       let ty = rename_mod_sig st ty in
       Syntax.ModAnn { path; ty }
     | None ->
       let ann_var = fresh_mod_var ~name:"Ann" st in
       let desugared =
         Surface.ModLet
           { name = ann_var
           ; expr
           ; body =
               Surface.ModAnn { expr = Surface.ModPath (Surface.PathName ann_var); ty }
           }
       in
       rename_mod_expr st desugared)*)
  | Surface.ModApp { expr; arg } ->
    (match arg with
     | Surface.AppArg arg ->
       (match expr_to_path expr, expr_to_path arg with
        | Some funct, Some arg ->
          let funct = rename_path st funct in
          let arg = rename_path st arg in
          Syntax.ModPath (Syntax.PathApp { funct; arg })
        | _, _ ->
          let funct_var = fresh_mod_var ~name:"App_funct" st in
          let arg_var = fresh_mod_var ~name:"App_arg" st in
          let desugared =
            Surface.ModLet
              { name = funct_var
              ; expr
              ; body =
                  Surface.ModLet
                    { name = arg_var
                    ; expr = arg
                    ; body =
                        Surface.ModApp
                          { expr = Surface.ModPath (Surface.PathName funct_var)
                          ; arg = AppArg (Surface.ModPath (Surface.PathName arg_var))
                          }
                    }
              }
          in
          rename_mod_expr st desugared)
     | Surface.GenArg ->
       (match expr_to_path expr with
        | Some path ->
          let path = rename_path st path in
          Syntax.ModGenApp path
        | None ->
          let funct_var = fresh_mod_var ~name:"Gen_app" st in
          let desugared =
            Surface.ModLet
              { name = funct_var
              ; expr
              ; body =
                  Surface.ModApp
                    { expr = Surface.ModPath (Surface.PathName funct_var)
                    ; arg = Surface.GenArg
                    }
              }
          in
          rename_mod_expr st desugared))
  | Surface.ModFunct { param; body } ->
    let param' = rename_funct_param st param in
    let body = rename_mod_expr { st with cx = add_param_cx st.cx param } body in
    Syntax.ModFunct { param = param'; body }
  | Surface.ModStruct binds ->
    let self = fresh_self_var st in
    let binds =
      rename_mod_binds { st with cx = Context.set_self self st.cx } binds |> Bwd.of_list
    in
    Syntax.ModStruct { self; binds }

and rename_mod_decl st (decl : Surface.mod_decl) =
  match decl with
  | Surface.DeclVal { name; ty } ->
    let name = Syntax.Var.of_surface name in
    let ty = rename_ty st ty in
    Syntax.DeclVal { name; ty }
  | Surface.DeclType { name; ty } ->
    let name = Syntax.Ty_var.of_surface name in
    let self = Context.get_self st.cx in
    let ty =
      Option.map ty ~f:(rename_ty st)
      |> Option.value
           ~default:
             (Syntax.TyVar
                { prefix = PrefixSelf (Syntax.Self_ref.create self); var = name })
    in
    Syntax.DeclType { name; ty }
  | Surface.DeclMod { name; ty } ->
    let name = Syntax.Mod_var.of_surface name in
    let ty = rename_mod_sig st ty in
    Syntax.DeclMod { name; ty }
  | Surface.DeclSig { name; ty } ->
    let name = Syntax.Mod_ty_var.of_surface name in
    let ty = rename_mod_sig st ty in
    Syntax.DeclSig { name; ty }

and rename_mod_sig st (ty : Surface.mod_sig) =
  match ty with
  | Surface.SigVar var ->
    let var = Context.find_mod_ty_var st.cx var in
    Syntax.SigVar var
  | Surface.SigAccess { path; name } ->
    let path = rename_path st path in
    let name = Syntax.Mod_ty_var.of_surface name in
    Syntax.SigVar Syntax.{ prefix = PrefixPath path; var = name }
  | Surface.SigFunct { param; body_ty } ->
    let param' = rename_funct_param st param in
    let body_ty =
      rename_mod_sig { st with cx = add_param_cx st.cx param } body_ty |> Syntax.zip_sig
    in
    Syntax.SigFunct { param = param'; body_ty }
  | Surface.SigStruct decls ->
    let self = fresh_self_var st in
    let decls =
      rename_mod_decls { st with cx = Context.set_self self st.cx } decls
      |> List.map ~f:(Syntax.map_gen_mod_decl ~f:Syntax.zip_sig)
      |> Bwd.of_list
    in
    Syntax.SigStruct { self; decls }
  | Surface.SigTransparent { path; ty } ->
    let path = rename_path st path in
    let ty = rename_mod_sig st ty in
    Syntax.SigTransparent { path; ty }
;;

let rename_mod_expr st expr =
  E.catch (fun () -> rename_mod_expr st expr) |> Result.map_error ~f:Error.t_of_sexp
;;
