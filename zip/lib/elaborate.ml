open! O

module E = struct
  include Effects.Error.Make (struct
      type t = Error.t
    end)

  let raise_s s = Error.t_of_sexp s |> raise
end

module Opacity = struct
  type t =
    | Opaque
    | Transparent
  [@@deriving sexp_of, equal, compare]

  let combine (x : t) (y : t) =
    match x, y with
    | Opaque, _ -> Opaque
    | _, Opaque -> Opaque
    | Transparent, Transparent -> Transparent
  ;;
end

module type Subst = sig
  type t [@@deriving sexp_of]

  val empty : t
  val add_self_var_exn : Syntax.Self_var.t -> Syntax.prefix -> t -> t
  val add_param_var_exn : Syntax.Param_var.t -> Syntax.mod_path -> t -> t
  val find_self_var : t -> Syntax.Self_var.t -> Syntax.prefix option
  val find_param_var : t -> Syntax.Param_var.t -> Syntax.mod_path option
end

module Subst : Subst = struct
  type t =
    { self_var : Syntax.prefix Syntax.Self_var.Map.t
    ; param_var : Syntax.mod_path Syntax.Param_var.Map.t
    }
  [@@deriving sexp_of]

  let empty =
    { self_var = Syntax.Self_var.Map.empty; param_var = Syntax.Param_var.Map.empty }
  ;;

  let add_self_var_exn self_var prefix st =
    { st with self_var = Map.add_exn st.self_var ~key:self_var ~data:prefix }
  ;;

  let add_param_var_exn param_var path st =
    { st with param_var = Map.add_exn st.param_var ~key:param_var ~data:path }
  ;;

  let find_self_var st self_var = Map.find st.self_var self_var
  let find_param_var st param_var = Map.find st.param_var param_var
end

module Sub_decls_mode = struct
  type t =
    | WithCode
    | CodeFree
end

type eval_while_config =
  { should_eval_ty_var : Syntax.Ty_var.t Syntax.prefixed -> bool
  ; should_eval_sig_var : Syntax.Mod_ty_var.t Syntax.prefixed -> bool
  }

let unzip_exn (ty : Syntax.mod_zip_sig) =
  assert (Bwd.is_empty ty.zippers);
  ty.ty
;;

let rec subst_gen_zipper
  : 'a 'b.
  ('a -> Subst.t -> 'b) -> 'a Syntax.gen_zipper -> Subst.t -> 'b Syntax.gen_zipper
  =
  fun subst_decl zipper subst ->
  { zipper with decls = Bwd.map ~f:(fun decl -> subst_decl decl subst) zipper.decls }

and subst_gen_decl
  : 'a 'b.
  ('a -> Subst.t -> 'b) -> 'a Syntax.gen_mod_decl -> Subst.t -> 'b Syntax.gen_mod_decl
  =
  fun subst_mod_sig decl subst ->
  match decl with
  | Syntax.DeclVal { name; ty } -> Syntax.DeclVal { name; ty = subst_ty ty subst }
  | Syntax.DeclMod { name; ty } -> Syntax.DeclMod { name; ty = subst_mod_sig ty subst }
  | Syntax.DeclType { name; ty } -> Syntax.DeclType { name; ty = subst_ty ty subst }
  | Syntax.DeclSig { name; ty } -> Syntax.DeclSig { name; ty = subst_unzip_sig ty subst }

and subst_decl decl subst = subst_gen_decl subst_zip_sig decl subst

and subst_zipper (zipper : Syntax.zipper) subst : Syntax.zipper =
  subst_gen_zipper subst_decl zipper subst

and subst_path (path : Syntax.mod_path) subst =
  match path with
  | Syntax.PathAccess { prefix; var } ->
    Syntax.PathAccess { prefix = subst_prefix prefix subst; var }
  | Syntax.PathParam param ->
    Subst.find_param_var subst param |> Option.value ~default:path
  | Syntax.PathZipperAccess { path; zipper } ->
    (*
       IMPORTANT!
       Since substituting is usually done for strengthening,
       we only substitute self references with paths in prefixes,
       not zipper path accesses, because those have already been strengthened.
    *)
    (match Subst.find_self_var subst zipper.var with
     | Some (PrefixSelf new_zipper) ->
       Syntax.PathZipperAccess { path; zipper = new_zipper }
     | Some (PrefixPath _) ->
       (* This case can happen when we re strengthen zippers *)
       Syntax.PathZipperAccess { path; zipper }
     | None -> path)
  | Syntax.PathApp { funct; arg } ->
    let funct = subst_path funct subst in
    let arg = subst_path arg subst in
    Syntax.PathApp { funct; arg }

and subst_prefix (prefix : Syntax.prefix) subst =
  match prefix with
  | Syntax.PrefixSelf self_var' ->
    Subst.find_self_var subst self_var'.var |> Option.value ~default:prefix
  | Syntax.PrefixPath path -> Syntax.PrefixPath (subst_path path subst)

and subst_prefixed : 'a. 'a Syntax.prefixed -> Subst.t -> 'a Syntax.prefixed =
  fun (prefixed : _ Syntax.prefixed) subst ->
  let prefix = prefixed.prefix in
  let prefix' = subst_prefix prefix subst in
  { prefixed with prefix = prefix' }

and subst_ty (ty : Syntax.ty) subst =
  match ty with
  | Syntax.TyUnit -> Syntax.TyUnit
  | Syntax.TyVar var -> Syntax.TyVar (subst_prefixed var subst)

and subst_funct_param (param : Syntax.funct_param) subst =
  match param with
  | Syntax.AppParam { name; ty } ->
    Syntax.AppParam { name; ty = subst_unzip_sig ty subst }
  | Syntax.GenParam -> param

and subst_transparent_ascription ({ path; ty } : Syntax.mod_transparent_ascription) subst
  : Syntax.mod_transparent_ascription
  =
  let path = subst_path path subst in
  let ty = subst_unzip_sig ty subst in
  { path; ty }

and subst_unzip_sig (ty : Syntax.mod_unzip_sig) subst =
  match ty with
  | Syntax.SigVar var -> Syntax.SigVar (subst_prefixed var subst)
  | Syntax.SigFunct { param; body_ty } ->
    (* make sure that parameter is not in the domain of the substitution *)
    (match param with
     | AppParam { name; _ } -> assert (Subst.find_param_var subst name |> Option.is_none)
     | GenParam -> ());
    let param = subst_funct_param param subst in
    let body_ty = subst_zip_sig body_ty subst in
    Syntax.SigFunct { param; body_ty }
  | Syntax.SigStruct { self; decls } ->
    assert (Subst.find_self_var subst self |> Option.is_none);
    let decls = Bwd.map ~f:(fun decl -> subst_decl decl subst) decls in
    Syntax.SigStruct { self; decls }
  | Syntax.SigTransparent ty ->
    subst_transparent_ascription ty subst |> Syntax.SigTransparent

and subst_transparent_zipper (zipper : Syntax.Transparent.zipper) subst
  : Syntax.Transparent.zipper
  =
  subst_gen_zipper subst_transparent_decl zipper subst

and subst_transparent_decl (decl : Syntax.Transparent.mod_decl) subst
  : Syntax.Transparent.mod_decl
  =
  subst_gen_decl subst_transparent_zip_sig decl subst

and subst_transparent_unzip_sig ty subst = subst_transparent_ascription ty subst

and subst_transparent_zip_sig ({ zippers; ty } : Syntax.Transparent.mod_zip_sig) subst
  : Syntax.Transparent.mod_zip_sig
  =
  let zippers =
    Bwd.map ~f:(fun zipper -> subst_transparent_zipper zipper subst) zippers
  in
  let ty = subst_transparent_unzip_sig ty subst in
  Syntax.Transparent.{ zippers; ty }

and subst_zip_sig (ty : Syntax.mod_zip_sig) subst : Syntax.mod_zip_sig =
  match ty with
  | { zippers; ty } ->
    let zippers = Bwd.map ~f:(fun zipper -> subst_zipper zipper subst) zippers in
    let ty = subst_unzip_sig ty subst in
    Syntax.{ zippers; ty }
;;

let rec strengthen_delayed' (ty : Syntax.mod_unzip_sig) path
  : Syntax.Transparent.mod_unzip_sig
  =
  match ty with
  | Syntax.SigTransparent ty -> ty
  | _ -> { path; ty }

and strengthen_decl_delayed_prefix prefix (decl : Syntax.mod_decl)
  : Syntax.Transparent.mod_decl
  =
  match decl with
  | Syntax.DeclVal p -> Syntax.DeclVal p
  | Syntax.DeclType p -> Syntax.DeclType p
  | Syntax.DeclMod { name; ty } ->
    let path = Syntax.PathAccess { prefix; var = name } in
    let ty = strengthen_delayed ty path in
    Syntax.DeclMod { name; ty }
  | Syntax.DeclSig p -> Syntax.DeclSig p

and strengthen_decl_delayed path = strengthen_decl_delayed_prefix (PrefixPath path)

and strengthen_zipper_with_subst subst path (z : Syntax.zipper) =
  (* P.A *)
  let path' = Syntax.PathZipperAccess { path; zipper = Syntax.Self_ref.create z.self } in
  (* A |-> P.A *)
  let subst = Subst.add_self_var_exn z.self (PrefixPath path') subst in
  let z =
    (* substitute D* in < A : D* > S using A |-> P.A *)
    subst_zipper z subst
    (* then strenghten D* // P.A *)
    |> Syntax.map_gen_zipper_decl ~f:(strengthen_decl_delayed path')
  in
  subst, z

and strengthen_zipper path z = strengthen_zipper_with_subst Subst.empty path z |> snd

and strengthen_zippers path zippers =
  let rec go subst zs =
    match zs with
    | Bwd.Emp -> subst, Bwd.Emp
    | Bwd.Snoc (zs, z) ->
      let subst, zs = go subst zs in
      let subst, z = strengthen_zipper_with_subst subst path z in
      subst, Bwd.Snoc (zs, z)
  in
  let subst, zippers = go Subst.empty zippers in
  subst, zippers

and strengthen_delayed (ty : Syntax.mod_zip_sig) path : Syntax.Transparent.mod_zip_sig =
  match ty with
  | { zippers; ty } ->
    let subst, zippers = strengthen_zippers path zippers in
    let ty = subst_unzip_sig ty subst |> Fn.flip strengthen_delayed' path in
    Syntax.Transparent.{ zippers; ty }

and strengthen_shallow (ty : Syntax.Value.mod_sig) (path : Syntax.mod_path)
  : Syntax.Transparent.Value.mod_sig
  =
  match ty with
  | Syntax.Value.SigStruct { self; decls } ->
    let subst = Subst.empty |> Subst.add_self_var_exn self (PrefixPath path) in
    let decls =
      Bwd.map ~f:(fun decl -> subst_decl decl subst |> strengthen_decl_delayed path) decls
    in
    Syntax.Transparent.Value.SigStruct { self; decls }
  | Syntax.Value.SigFunct { param = AppParam { name; ty }; body_ty } ->
    let path' = Syntax.PathApp { funct = path; arg = Syntax.PathParam name } in
    let body_ty = strengthen_delayed body_ty path' in
    Syntax.Transparent.Value.SigAppFunct { param = name; param_ty = ty; body_ty }
  | Syntax.Value.SigFunct { param = GenParam; body_ty } ->
    Syntax.Transparent.Value.SigGenFunct body_ty
;;

let rec unzip_sig_free_vars pred bound (ty : Syntax.mod_unzip_sig) =
  match ty with
  | Syntax.SigVar var when pred var ->
    Syntax.Prefixed_set.singleton (Syntax.map_prefixed_var ~f:Syntax.Var_sum.modtyvar var)
  | Syntax.SigVar var -> todo ()
  | Syntax.SigFunct _ | Syntax.SigStruct _ | Syntax.SigTransparent _ -> todo ()
;;

(*
   Lifting turns a transparent signature into a normal signature.
   this is just to make the types work out, the signature will still be internally transparent/strengthened.
   We regard transparent signatures as a syntactic subclass of normal signatures,
   but we represent them as different algebraic types, we we need to lift them.
*)
let rec lift_decl (decl : Syntax.Transparent.mod_decl) : Syntax.mod_decl =
  Syntax.map_gen_mod_decl ~f:lift_zip_sig decl

and lift_value value =
  match value with
  | Syntax.Transparent.Value.SigStruct { self; decls } ->
    Syntax.Value.SigStruct { self; decls = Bwd.map ~f:lift_decl decls }
  | Syntax.Transparent.Value.SigAppFunct { param; param_ty; body_ty } ->
    Syntax.Value.SigFunct
      { param = Syntax.AppParam { name = param; ty = param_ty }
      ; body_ty = lift_zip_sig body_ty
      }
  | Syntax.Transparent.Value.SigGenFunct body_ty ->
    Syntax.Value.SigFunct { param = Syntax.GenParam; body_ty }

and lift_zip_sig (zip_sig : Syntax.Transparent.mod_zip_sig) =
  let Syntax.Transparent.{ zippers; ty } = zip_sig in
  let zippers = Bwd.map ~f:lift_zipper zippers in
  let ty = lift_unzip_sig ty in
  ({ zippers; ty } : Syntax.mod_zip_sig)

and lift_unzip_sig ty = Syntax.SigTransparent ty

and lift_zipper (zipper : Syntax.Transparent.zipper) =
  Syntax.map_gen_zipper_decl ~f:lift_decl zipper
;;

type st =
  { cx : Context.t
  ; debug : bool
  }
[@@deriving sexp_of]

let create_state ?(debug = false) () = { cx = Context.empty; debug }
let debug st sexp = if st.debug then print_s sexp

let add_cx_zipper st (zipper : Syntax.zipper) =
  let zipper =
    { zipper with
      decls =
        Bwd.map
          ~f:
            (strengthen_decl_delayed_prefix
               (PrefixSelf (Syntax.Self_ref.create zipper.self)))
          zipper.decls
    }
  in
  { st with cx = Context.add_elem (Zipper zipper) st.cx }
;;

let add_cx_zippers st zippers =
  List.fold_left ~init:st ~f:add_cx_zipper (Bwd.to_list zippers)
;;

let add_cx_param st (param : Syntax.funct_param) =
  match param with
  | Syntax.AppParam { name; ty } ->
    let ty = strengthen_delayed' ty (Syntax.PathParam name) in
    { st with cx = Context.add_elem (ParamVar (name, ty)) st.cx }
  | Syntax.GenParam -> st
;;

let add_cx_empty_zipper st self = add_cx_zipper st { self; decls = Bwd.Emp }

let add_cx_decl_to_last_zipper st self_var decl =
  let decl =
    strengthen_decl_delayed_prefix
      (Syntax.PrefixSelf (Syntax.Self_ref.create self_var))
      decl
  in
  { st with cx = Context.add_to_last_zipper_exn self_var decl st.cx }
;;

(* map over a structure while maintaining the context *)
let map_cx_sig_struct st ({ self; decls } : _ Syntax.gen_mod_sig_struct) ~f =
  let rec go st decls =
    match decls with
    | Bwd.Snoc (decls, decl) ->
      let st, decls = go st decls in
      let decl = f st decl in
      let st = add_cx_decl_to_last_zipper st self decl in
      st, Bwd.snoc decls decl
    | Bwd.Emp -> st, Bwd.Emp
  in
  let _st, decls = go (add_cx_empty_zipper st self) decls in
  Syntax.{ self; decls }
;;

(* map over zippers while maintaining the context *)
let map_cx_zippers st zippers ~f =
  let rec go st zippers =
    match zippers with
    | Bwd.Snoc (zippers, zipper) ->
      let st, zippers = go st zippers in
      let zipper = f st zipper in
      let st = add_cx_zipper st zipper in
      st, Bwd.Snoc (zippers, zipper)
    | Bwd.Emp -> st, Bwd.Emp
  in
  go st zippers
;;

let rec infer_path st (path : Syntax.mod_path) : Syntax.Transparent.mod_zip_sig =
  match path with
  | Syntax.PathAccess prefixed -> infer_path_access st prefixed
  | Syntax.PathParam param ->
    let ty =
      Context.find_param st.cx param
      |> Option.value_or_thunk ~default:(fun () ->
        E.raise_s [%message "Parameter not found in context" (param : Syntax.Param_var.t)])
    in
    ty |> Syntax.Transparent.zip_sig
  | Syntax.PathZipperAccess { path; zipper = self_var } ->
    let ty = infer_path st path in
    let zippers = ty.zippers in
    let zipper =
      Bwd.find_opt zippers ~f:(fun (zipper : Syntax.Transparent.zipper) ->
        Syntax.Self_var.equal self_var.var zipper.self)
      |> Option.value_or_thunk ~default:(fun () ->
        E.raise_s
          [%message
            "internal error: could not find zipper"
              (path : Syntax.mod_path)
              (ty : Syntax.Transparent.mod_zip_sig)
              (self_var : Syntax.Self_ref.t)])
    in
    (*
       We lift the zipper here because zippers have already been shallow strengthened,
       but we want a type that has only been delayed strengthened (headed by some transparent ascription).
       Basically, we have already pushed the strengthening down one level.
       So instead, we forget that we strengthened the zipper and lift it.
       When we later re-strengthen the zipper, we won't do anything because the zipper was already strengthened.
    *)
    let lifted_zipper = lift_zipper zipper in
    let lifted_sig = Syntax.zipper_to_sig lifted_zipper in
    { path; ty = lifted_sig } |> Syntax.Transparent.zip_sig
  | Syntax.PathApp { funct; arg } ->
    let funct_val_ty = resolve_path_value st funct in
    (match funct_val_ty with
     | Syntax.Transparent.Value.SigAppFunct { param; param_ty; body_ty } ->
       let arg_ty = infer_path st arg in
       sub_sig Sub_decls_mode.WithCode st (lift_zip_sig arg_ty) param_ty;
       let subst = Subst.empty |> Subst.add_param_var_exn param arg in
       subst_transparent_zip_sig body_ty subst
     | _ ->
       E.raise_s
         [%message
           "path was not an applicative functor"
             ~path:(funct : Syntax.mod_path)
             ~ty:(funct_val_ty : Syntax.Transparent.Value.mod_sig)])

and infer_path_access st prefixed =
  match prefixed with
  | Syntax.{ prefix = PrefixSelf self; var } ->
    let mod_var = Syntax.{ prefix = self.var; var } in
    let ty =
      Context.find_mod_var st.cx mod_var
      |> Option.value_or_thunk ~default:(fun () ->
        E.raise_s
          [%message
            "Module variable not found in context"
              (mod_var : Syntax.Mod_var.t Syntax.self_prefixed)
              (st.cx : Context.t)])
    in
    ty
  | Syntax.{ prefix = PrefixPath path; var } ->
    let ty_val = resolve_path_value st path in
    (match ty_val with
     | Syntax.Transparent.Value.SigStruct { self = _; decls } ->
       let res =
         Bwd.find_map decls ~f:(function
           | Syntax.DeclMod { name; ty } when Syntax.Mod_var.equal var name -> Some ty
           | _ -> None)
         |> Option.value_or_thunk ~default:(fun () ->
           E.raise_s
             [%message
               "did not find module in signature"
                 (path : Syntax.mod_path)
                 (var : Syntax.Mod_var.t)
                 (ty_val : Syntax.Transparent.Value.mod_sig)])
       in
       res
     | _ ->
       E.raise_s
         [%message
           "expected struct"
             (path : Syntax.mod_path)
             (ty_val : Syntax.Transparent.Value.mod_sig)])

and eval_step_sig_var st (prefixed : Syntax.Mod_ty_var.t Syntax.prefixed) =
  let Syntax.{ prefix; var } = prefixed in
  match prefix with
  | PrefixSelf self ->
    let mod_ty_var = Syntax.{ prefix = self.var; var } in
    let ty =
      Context.find_mod_ty_var st.cx mod_ty_var
      |> Option.value_or_thunk ~default:(fun () ->
        E.raise_s
          [%message
            "Module type variable not found in context"
              (mod_ty_var : Syntax.Mod_ty_var.t Syntax.self_prefixed)])
    in
    ty
  | PrefixPath path ->
    let ty_val = resolve_path_value st path in
    (match ty_val with
     | Syntax.Transparent.Value.SigStruct { self = _; decls } ->
       let res =
         Bwd.find_map decls ~f:(function
           | Syntax.DeclSig { name; ty } when Syntax.Mod_ty_var.equal var name -> Some ty
           | _ -> None)
         |> Option.value_or_thunk ~default:(fun () ->
           E.raise_s
             [%message
               "did not find module type in signature"
                 (path : Syntax.mod_path)
                 (var : Syntax.Mod_ty_var.t)
                 (ty_val : Syntax.Transparent.Value.mod_sig)])
       in
       res
     | _ ->
       E.raise_s
         [%message
           "expected struct"
             (path : Syntax.mod_path)
             (ty_val : Syntax.Transparent.Value.mod_sig)])

(*
   Evaluates a signature to weak head normal form.

   This means we evaluate a signature to a normal form but we don't
   evaluate under values to prevent from unfolding to much
*)
and eval_unzip_sig (st : st) (ty : Syntax.mod_unzip_sig) : Syntax.Normal.mod_sig =
  match ty with
  | Syntax.SigVar prefixed ->
    let ty' = eval_step_sig_var st prefixed in
    eval_unzip_sig st ty'
  | Syntax.SigTransparent sig_trans ->
    Syntax.Normal.SigTransparent (eval_sig_transparent st sig_trans)
  (* already in normal form *)
  | Syntax.SigStruct sig_struct ->
    Syntax.Normal.SigVal (Syntax.Value.SigStruct sig_struct)
  (* already in normal form *)
  | Syntax.SigFunct sig_funct -> Syntax.Normal.SigVal (Syntax.Value.SigFunct sig_funct)

and eval_sig_transparent (st : st) ({ path; ty } : Syntax.mod_transparent_ascription)
  : Syntax.Normal.mod_transp_sig
  =
  (*
     We have (= P < S)
     first evaluate the signature S
  *)
  let ty = eval_unzip_sig st ty in
  match ty with
  (*
     keep the new transparent signature

     (= P < (= P' < S'))

     should evaluate to

     (= P' < S')

     We don't care about the true identity of P, because it will be overridden by P'
  *)
  | Syntax.Normal.SigTransparent ty -> ty
  (*
     (= P < S')

     We need to find the true identity of P, because we know that S' is not transparent so P's identity won't be overridden.
  *)
  | Syntax.Normal.SigVal val_ty ->
    let path = resolve_path_identity st path in
    { path; ty = val_ty }

and resolve_path_value (st : st) (path : Syntax.mod_path)
  : Syntax.Transparent.Value.mod_sig
  =
  let ty = infer_path st path in
  match ty with
  | { zippers = _; ty = trans_ty } ->
    let trans_ty' = eval_sig_transparent st trans_ty in
    let Syntax.Normal.{ path; ty = val_ty } = trans_ty' in
    strengthen_shallow val_ty path

and resolve_path_identity (st : st) (path : Syntax.mod_path) : Syntax.mod_path =
  resolve_path_identity_with_fuel 100 st path

and resolve_path_identity_with_fuel fuel (st : st) (path : Syntax.mod_path)
  : Syntax.mod_path
  =
  assert (fuel >= 0);
  if fuel = 0
  then
    E.raise_s
      [%message
        "Internal error: Path identity resolution exhausted fuel" (path : Syntax.mod_path)];
  let ty = infer_path st path in
  let path' = ty.ty.path in
  if Syntax.equal_mod_path path path'
  then path
  else resolve_path_identity_with_fuel (fuel - 1) st path'

and resolve_unzip_sig_value st (ty : Syntax.mod_unzip_sig) =
  let norm_ty = eval_unzip_sig st ty in
  match norm_ty with
  | Syntax.Normal.SigTransparent { path; ty = val_ty } ->
    strengthen_shallow val_ty path |> lift_value
  | Syntax.Normal.SigVal val_ty -> val_ty

and eval_zip_sig_while st config (zip_sig : Syntax.mod_zip_sig) =
  let st, zippers =
    map_cx_zippers st zip_sig.zippers ~f:(fun st zipper ->
      eval_sig_struct_while st config zipper)
  in
  let ty = eval_unzip_sig_while st config zip_sig.ty in
  Syntax.{ zippers; ty }

(* Used to solve signature avoidance by avoiding zippers *)
(* TODO: need to add stuff to the context *)
and eval_unzip_sig_while st config (ty : Syntax.mod_unzip_sig) : Syntax.mod_unzip_sig =
  match ty with
  | Syntax.SigVar prefixed when config.should_eval_sig_var prefixed ->
    let ty' = eval_step_sig_var st prefixed in
    eval_unzip_sig_while st config ty'
  | Syntax.SigVar _ -> ty
  | Syntax.SigTransparent { path; ty } ->
    let ty' = eval_unzip_sig_while st config ty in
    Syntax.SigTransparent { path; ty = ty' }
  | Syntax.SigFunct { param; body_ty } ->
    let param =
      match param with
      | Syntax.AppParam { name; ty } ->
        let ty = eval_unzip_sig_while st config ty in
        Syntax.AppParam { name; ty }
      | Syntax.GenParam -> Syntax.GenParam
    in
    let st = add_cx_param st param in
    let body_ty = eval_zip_sig_while st config body_ty in
    Syntax.SigFunct { param; body_ty }
  | Syntax.SigStruct sig_struct ->
    let sig_struct = eval_sig_struct_while st config sig_struct in
    Syntax.SigStruct sig_struct

and eval_sig_struct_while st config (sig_struct : Syntax.mod_sig_struct) =
  map_cx_sig_struct st sig_struct ~f:(fun st decl -> eval_decl_while st config decl)

and eval_decl_while st config (decl : Syntax.mod_decl) =
  match decl with
  | Syntax.DeclVal { name; ty } ->
    Syntax.DeclVal { name; ty = eval_ty_while st config.should_eval_ty_var ty }
  | Syntax.DeclType { name; ty } ->
    Syntax.DeclType { name; ty = eval_ty_while st config.should_eval_ty_var ty }
  | Syntax.DeclMod { name; ty } ->
    Syntax.DeclMod { name; ty = eval_zip_sig_while st config ty }
  | Syntax.DeclSig { name; ty } ->
    Syntax.DeclSig { name; ty = eval_unzip_sig_while st config ty }

(*
   Important!
   The types here don't capture all the preconditions that sig_subtype needs.
   sig_subtype doesn't just take a mod_unzip_sig for ty2, there must be NO zippers at all in ty2.
   This precondition cannot be just captured by the ocaml type system.
   The precondition is what f-ing modules calls "explicit".
   It is needed to make sure that subtyping is decidable.
   Usually a signature that is of type mod_unzip_sig does not contain any nested zippers,
   but this is not always true when more advanced constructs are added.
   An "explicit" signature corresponds to some signature that came from the source code,
   and not one that was elaborated by the typechecker.
   This means that an "explicit" signature has no zippers because signature avoidance cannot happen.

   TODO: return a runtime coercion as evidence of subtyping
*)
and sub_sig sub_decls (st : st) (ty1 : Syntax.mod_zip_sig) (ty2 : Syntax.mod_unzip_sig) =
  sub_sig' sub_decls (add_cx_zippers st ty1.zippers) ty1.ty ty2

and sub_sig' sub_decls (st : st) (ty1 : Syntax.mod_unzip_sig) (ty2 : Syntax.mod_unzip_sig)
  =
  let ty1 = eval_unzip_sig st ty1 in
  let ty2 = eval_unzip_sig st ty2 in
  sub_norm_sig sub_decls st ty1 ty2

and sub_norm_sig
  sub_decls
  (st : st)
  (ty1 : Syntax.Normal.mod_sig)
  (ty2 : Syntax.Normal.mod_sig)
  =
  match ty1, ty2 with
  | Syntax.Normal.SigVal val1, Syntax.Normal.SigVal val2 ->
    sub_val_sig sub_decls st val1 val2
  | ( Syntax.Normal.SigTransparent { path = path1; ty = ty1 }
    , Syntax.Normal.SigTransparent { path = path2; ty = ty2 } ) ->
    let ty1 = strengthen_shallow ty1 path1 in
    let ty2 = strengthen_shallow ty2 path2 in
    sub_val_sig sub_decls st (lift_value ty1) (lift_value ty2)
  | Syntax.Normal.SigTransparent { path = path1; ty = ty1 }, Syntax.Normal.SigVal ty2 ->
    let ty1 = strengthen_shallow ty1 path1 in
    sub_val_sig sub_decls st (lift_value ty1) ty2
  | Syntax.Normal.SigVal _, Syntax.Normal.SigTransparent _ ->
    (* if the right side is transparent, then the left side must also be transparent *)
    E.raise_s
      [%message
        "Not a subtype" (ty1 : Syntax.Normal.mod_sig) (ty2 : Syntax.Normal.mod_sig)]

(* TODO: make this code better *)
and sub_val_sig sub_decls st (ty1 : Syntax.Value.mod_sig) (ty2 : Syntax.Value.mod_sig) =
  match ty1, ty2 with
  | ( Syntax.Value.SigStruct { self = self1; decls = decls1 }
    , Syntax.Value.SigStruct { self = self2; decls = decls2 } ) ->
    let decls2 =
      (*
         Rename the self2 to self1.
         This is important so that all abstract types in the second structure will point to all the types in the first structure.
         This is because we represent abstract types as self referencing types, for example

         sig(A)
         type t = A.t
         end

         This means that when A is renamed to self1 and all the declarations of self1 are added to the context, then
         all of the self references will actually point to types in self1.
      *)
      (* *)
      let subst =
        Subst.empty
        |> Subst.add_self_var_exn self2 (PrefixSelf (Syntax.Self_ref.create self1))
      in
      Bwd.map ~f:(Fn.flip subst_decl subst) decls2
    in
    let decl_struct1 = Syntax.Decl_struct.of_bwd decls1 in
    let st = add_cx_zipper st { self = self1; decls = decls1 } in
    (* All the declarations in ty2 should be present in ty1 *)
    Bwd.iter decls2 ~f:(fun decl2 ->
      let p2 = Syntax.decl_to_pair decl2 in
      let elim_pair
        : 'a. 'a Syntax.Var_sing.t -> ('a, 'mod_sig) Syntax.Decl_elem.t -> unit
        =
        fun sing2 elem2 ->
        let elem1 =
          Syntax.Decl_struct.find decl_struct1 sing2
          |> Option.value_or_thunk ~default:(fun () ->
            E.raise_s
              [%message
                "Could not find decl in struct"
                  (ty1 : Syntax.Value.mod_sig)
                  (Syntax.Var_sing.to_sum sing2 : Syntax.Var_sum.t)])
        in
        sub_decl_elem sub_decls st elem1 elem2
      in
      Syntax.Decl_map.Pair.elim p2 { f = elim_pair };
      ());
    ()
  | ( Syntax.Value.SigFunct
        { param = AppParam { name = _name1; ty = ty1 }; body_ty = body_ty1 }
    , Syntax.Value.SigFunct
        { param = AppParam { name = _name2; ty = ty2 }; body_ty = body_ty2 } ) ->
    sub_sig' sub_decls st ty2 ty1;
    sub_sig sub_decls st body_ty1 (unzip_exn body_ty2);
    ()
  | ( Syntax.Value.SigFunct { param = GenParam; body_ty = body_ty1 }
    , Syntax.Value.SigFunct { param = GenParam; body_ty = body_ty2 } ) ->
    sub_sig sub_decls st body_ty1 (unzip_exn body_ty2);
    ()
  | _, _ ->
    E.raise_s
      [%message "Not a subtype" (ty1 : Syntax.Value.mod_sig) (ty2 : Syntax.Value.mod_sig)]

and sub_decl_elem
  : 'var 'mod_sig.
  Sub_decls_mode.t
  -> st
  -> ('var, Syntax.mod_zip_sig) Syntax.Decl_elem.t
  -> ('var, Syntax.mod_zip_sig) Syntax.Decl_elem.t
  -> unit
  =
  fun (type var)
    sub_decls
    st
    (decl1 : (var, _) Syntax.Decl_elem.t)
    (decl2 : (var, _) Syntax.Decl_elem.t) ->
  match decl1, decl2 with
  | DeclVal { ty = ty1; _ }, DeclVal { ty = ty2; _ } ->
    sub_ty st ty1 ty2;
    ()
  | DeclType ty1, DeclType ty2 ->
    (* make sure to use code-free equivalence here *)
    unify_ty st ty1.ty ty2.ty;
    ()
  | DeclMod { ty = ty1; _ }, DeclMod { ty = ty2; _ } ->
    sub_sig sub_decls st ty1 (unzip_exn ty2);
    ()
  | DeclSig { ty = ty1; _ }, DeclSig { ty = ty2; _ } ->
    sub_sig' CodeFree st ty1 ty2;
    sub_sig' CodeFree st ty2 ty1;
    ()
  | _ -> raise_s [%message "Internal error, should not happen"]

and check_ty_ok st ty =
  match ty with
  | Syntax.TyUnit -> ()
  | Syntax.TyVar var ->
    eval_ty_var_step st var |> ignore;
    ()

and eval_ty_var_step st ty_var =
  let Syntax.{ prefix; var } = ty_var in
  match prefix with
  | Syntax.PrefixSelf self ->
    let ty_var = Syntax.{ prefix = self.var; var } in
    let ty' =
      Context.find_ty_var st.cx ty_var
      |> Option.value_or_thunk ~default:(fun () ->
        E.raise_s
          [%message
            "Type variable not found in context"
              (ty_var : Syntax.Ty_var.t Syntax.self_prefixed)])
    in
    ty'
  | Syntax.PrefixPath path ->
    let ty_val = resolve_path_value st path in
    (match ty_val with
     | Syntax.Transparent.Value.SigStruct { self = _; decls } ->
       let ty' =
         Bwd.find_map decls ~f:(function
           | Syntax.DeclType { name; ty } when Syntax.Ty_var.equal var name -> Some ty
           | _ -> None)
         |> Option.value_or_thunk ~default:(fun () ->
           E.raise_s
             [%message
               "did not find module type in signature"
                 (path : Syntax.mod_path)
                 (var : Syntax.Ty_var.t)
                 (ty_val : Syntax.Transparent.Value.mod_sig)])
       in
       ty'
     | _ ->
       E.raise_s [%message "expected struct" (ty_val : Syntax.Transparent.Value.mod_sig)])

and eval_ty_while st should_eval_var (ty : Syntax.ty) =
  match ty with
  | Syntax.TyUnit -> Syntax.TyUnit
  | Syntax.TyVar prefixed when should_eval_var prefixed ->
    let ty' = eval_ty_var_step st prefixed in
    (match ty' with
     | Syntax.TyVar prefixed'
       when [%equal: Syntax.Ty_var.t Syntax.prefixed] prefixed prefixed' -> ty'
     | _ -> eval_ty_while st should_eval_var ty')
  | Syntax.TyVar _ -> ty

and eval_ty st ty = eval_ty_while st (Fn.const true) ty

and unify_ty st ty1 ty2 =
  let ty1' = eval_ty st ty1 in
  let ty2' = eval_ty st ty2 in
  let raise_error () =
    E.raise_s
      [%message
        (ty1 : Syntax.ty)
          "!="
          (ty2 : Syntax.ty)
          "because"
          (ty1' : Syntax.ty)
          "!="
          (ty2' : Syntax.ty)]
  in
  match ty1', ty2' with
  | Syntax.TyUnit, Syntax.TyUnit -> ()
  | Syntax.TyVar prefixed1, Syntax.TyVar prefixed2 ->
    if [%equal: Syntax.Ty_var.t Syntax.prefixed] prefixed1 prefixed2
    then ()
    else raise_error ()
  | _, _ -> raise_error ()

(* we don't have core level subtyping yet *)
and sub_ty st ty1 ty2 = unify_ty st ty1 ty2

and infer_mod_expr st expr : Opacity.t * Syntax.mod_zip_sig =
  match expr with
  | Syntax.ModPath path ->
    let ty = infer_path st path in
    Opacity.Transparent, lift_zip_sig ty
  | Syntax.ModStruct { self; binds } ->
    let st = add_cx_empty_zipper st self in
    let opacity, decls = infer_binds st self binds in
    opacity, Syntax.SigStruct { self; decls } |> Syntax.zip_sig
  | Syntax.ModAnn { expr; ty } ->
    check_sig_ok st ty;
    let opacity, ty' = infer_mod_expr st expr in
    sub_sig WithCode st ty' ty;
    opacity, Syntax.zip_sig ty
  | Syntax.ModGenApp arg ->
    let val_ty = resolve_path_value st arg in
    (match val_ty with
     (* generative functor applications are opaque *)
     | Syntax.Transparent.Value.SigGenFunct res_ty -> Opacity.Opaque, res_ty
     | _ ->
       E.raise_s
         [%message
           "expected generative functor" (val_ty : Syntax.Transparent.Value.mod_sig)])
  | Syntax.ModFunct { param = GenParam; body } ->
    let _opacity, body_ty = infer_mod_expr st body in
    Opacity.Transparent, Syntax.SigFunct { param = GenParam; body_ty } |> Syntax.zip_sig
  | Syntax.ModFunct { param = AppParam { name = _; ty } as param; body } ->
    check_sig_ok st ty;
    let st' = add_cx_param st param in
    let body_opacity, body_ty = infer_mod_expr st' body in
    (match body_opacity with
     | Opacity.Transparent -> ()
     | Opacity.Opaque ->
       E.raise_s
         [%message
           "Body of an applicative functor must be transparent"
             (param : Syntax.funct_param)
             (body : Syntax.mod_expr)]);
    Opacity.Transparent, Syntax.SigFunct { param; body_ty } |> Syntax.zip_sig
  | Syntax.ModProj { expr; name } ->
    let opacity, Syntax.{ zippers; ty } = infer_mod_expr st expr in
    let val_ty = resolve_unzip_sig_value (add_cx_zippers st zippers) ty in
    (match val_ty with
     | Syntax.Value.SigStruct { self; decls } ->
       let ty' =
         Bwd.find_map decls ~f:(function
           | Syntax.DeclMod { name = name'; ty } when Syntax.Mod_var.equal name name' ->
             Some ty
           | _ -> None)
         |> Option.value_or_thunk ~default:(fun () ->
           E.raise_s
             [%message
               "did not find module in signature"
                 (name : Syntax.Mod_var.t)
                 (val_ty : Syntax.Value.mod_sig)])
       in
       let decls_before =
         Bwd.to_list decls
         |> List.take_while ~f:(function
           | Syntax.DeclMod { name = name'; _ } -> not (Syntax.Mod_var.equal name name')
           | _ -> true)
         |> Bwd.of_list
       in
       let new_zipper = ({ self; decls = decls_before } : Syntax.zipper) in
       opacity, Syntax.create_zip_sig (Bwd.Snoc (zippers, new_zipper)) ty'
     | _ -> E.raise_s [%message "expected struct" (val_ty : Syntax.Value.mod_sig)])

and infer_binds st self (binds : _ Bwd.t) =
  let rec go st binds =
    match binds with
    | Bwd.Snoc (binds, bind) ->
      let opacity1, st, decls = go st binds in
      let opacity2, decl = infer_bind st bind in
      let st = add_cx_decl_to_last_zipper st self decl in
      Opacity.combine opacity1 opacity2, st, Bwd.snoc decls decl
    | Bwd.Emp -> Opacity.Transparent, st, Bwd.Emp
  in
  let opacity, _st, decls = go st binds in
  opacity, decls

and infer_bind st bind =
  match bind with
  | Syntax.BindVal { name; ty; expr } ->
    Option.iter ~f:(check_ty_ok st) ty;
    let ty' = infer_expr st expr in
    (match ty with
     | Some ty -> unify_ty st ty ty'
     | None -> ());
    (* TODO: check the opacity of the core level expression *)
    Opacity.Transparent, Syntax.DeclVal { name; ty = Option.value ty ~default:ty' }
  | Syntax.BindType { name; ty } ->
    check_ty_ok st ty;
    Opacity.Transparent, Syntax.DeclType { name; ty }
  | Syntax.BindMod { name; expr } ->
    let opacity, ty = infer_mod_expr st expr in
    opacity, Syntax.DeclMod { name; ty }
  | Syntax.BindSig { name; ty } ->
    check_sig_ok st ty;
    Opacity.Transparent, Syntax.DeclSig { name; ty }

and infer_expr st expr =
  match expr with
  | Syntax.ExprUnit -> Syntax.TyUnit
  | Syntax.ExprVar { prefix = Syntax.PrefixPath path; var } ->
    let ty_val = resolve_path_value st path in
    (match ty_val with
     | Syntax.Transparent.Value.SigStruct { self = _; decls } ->
       let ty' =
         Bwd.find_map decls ~f:(function
           | Syntax.DeclVal { name; ty } when Syntax.Var.equal var name -> Some ty
           | _ -> None)
         |> Option.value_or_thunk ~default:(fun () ->
           E.raise_s
             [%message
               "did not find variable in signature"
                 (path : Syntax.mod_path)
                 (var : Syntax.Var.t)
                 (ty_val : Syntax.Transparent.Value.mod_sig)])
       in
       ty'
     | _ ->
       E.raise_s [%message "expected struct" (ty_val : Syntax.Transparent.Value.mod_sig)])
  | Syntax.ExprVar { prefix = Syntax.PrefixSelf self; var } -> todo ~loc:[%here] ()

and check_sig_ok st (ty : Syntax.mod_unzip_sig) =
  match ty with
  | Syntax.SigVar prefixed ->
    eval_step_sig_var st prefixed |> ignore;
    ()
  | Syntax.SigFunct { param; body_ty } ->
    (match param with
     | Syntax.AppParam { name = _; ty } ->
       check_sig_ok st ty;
       ()
     | Syntax.GenParam -> ());
    let st = add_cx_param st param in
    check_sig_ok st (unzip_exn body_ty);
    ()
  | Syntax.SigStruct sig_struct ->
    map_cx_sig_struct st sig_struct ~f:(fun st decl ->
      check_decl_ok st decl;
      decl)
    |> ignore;
    ()
  | Syntax.SigTransparent { path; ty } ->
    check_sig_ok st ty;
    let path_ty = infer_path st path in
    sub_sig WithCode st (lift_zip_sig path_ty) ty;
    ()

and check_decl_ok st decl =
  match decl with
  | Syntax.DeclVal { ty; _ } ->
    check_ty_ok st ty;
    ()
  (* Check if this is an abstract type *)
  | Syntax.DeclType { name; ty = Syntax.TyVar { prefix = PrefixSelf self; var } }
    when Syntax.Ty_var.equal name var
         && Syntax.Self_var.equal (Context.current_self_var_exn st.cx) self.var -> ()
  | Syntax.DeclType { ty; _ } ->
    check_ty_ok st ty;
    ()
  | Syntax.DeclMod { ty; _ } ->
    check_sig_ok st (unzip_exn ty);
    ()
  | Syntax.DeclSig { ty; _ } ->
    check_sig_ok st ty;
    ()
;;

let rec annotate_self_ref_zip_sig st (ty : Syntax.mod_zip_sig) =
  let st, zippers = annotate_self_ref_zippers st ty.zippers in
  let ty = annotate_self_ref_unzip_sig st ty.ty in
  { Syntax.zippers; ty }

and annotate_self_ref_unzip_sig st (ty : Syntax.mod_unzip_sig) =
  match ty with
  | Syntax.SigVar var -> Syntax.SigVar (annotate_self_ref_prefixed st var)
  | Syntax.SigFunct { param; body_ty } ->
    let st' = add_cx_param st param in
    let body_ty = annotate_self_ref_zip_sig st' body_ty in
    let param =
      match param with
      | Syntax.AppParam { name; ty } ->
        let ty = annotate_self_ref_unzip_sig st ty in
        Syntax.AppParam { name; ty }
      | Syntax.GenParam -> Syntax.GenParam
    in
    Syntax.SigFunct { param; body_ty }
  | Syntax.SigStruct sig_struct ->
    Syntax.SigStruct (annotate_self_ref_sig_struct st sig_struct)
  | Syntax.SigTransparent { path; ty } ->
    let path = annotate_self_ref_path st path in
    let ty = annotate_self_ref_unzip_sig st ty in
    Syntax.SigTransparent { path; ty }

and annotate_self_ref_sig_struct st (sig_struct : Syntax.mod_sig_struct) =
  map_cx_sig_struct st sig_struct ~f:(fun st decl -> annotate_self_ref_decl st decl)

and annotate_self_ref st (self_ref : Syntax.Self_ref.t) : Syntax.Self_ref.t =
  let index = Context.find_self_var_index_exn self_ref.var st.cx in
  Syntax.Self_ref.create ~index ~necessary:true self_ref.var

and annotate_self_ref_prefixed : 'a. _ -> 'a Syntax.prefixed -> 'a Syntax.prefixed =
  fun st (prefixed : _ Syntax.prefixed) ->
  match prefixed.prefix with
  | Syntax.PrefixSelf self_ref ->
    let self = annotate_self_ref st self_ref in
    { prefixed with prefix = Syntax.PrefixSelf self }
  | Syntax.PrefixPath path ->
    { prefixed with prefix = Syntax.PrefixPath (annotate_self_ref_path st path) }

and annotate_self_ref_path st path =
  match path with
  | Syntax.PathAccess { prefix; var } ->
    Syntax.PathAccess { prefix = annotate_self_ref_prefix st prefix; var }
  | Syntax.PathParam _param -> path
  | Syntax.PathZipperAccess { path; zipper } ->
    let ty = infer_path st path in
    let zippers = ty.zippers in
    let index =
      Bwd.find_index zippers ~f:(fun (z : Syntax.Transparent.zipper) ->
        Syntax.Self_var.equal z.self zipper.var)
      |> Option.value_exn ~message:"Internal error: Could not find zipper"
    in
    Syntax.PathZipperAccess
      { path = annotate_self_ref_path st path
      ; zipper = Syntax.Self_ref.create ~index ~necessary:true zipper.var
      }
  | Syntax.PathApp { funct; arg } ->
    Syntax.PathApp
      { funct = annotate_self_ref_path st funct; arg = annotate_self_ref_path st arg }

and annotate_self_ref_prefix st prefix =
  match prefix with
  | Syntax.PrefixSelf self_ref -> Syntax.PrefixSelf (annotate_self_ref st self_ref)
  | Syntax.PrefixPath path -> Syntax.PrefixPath (annotate_self_ref_path st path)

and annotate_self_ref_zippers st zippers =
  map_cx_zippers st zippers ~f:annotate_self_ref_zipper

and annotate_self_ref_zipper st (zipper : Syntax.zipper) : Syntax.zipper =
  annotate_self_ref_sig_struct st zipper

and annotate_self_ref_decl st decl =
  match decl with
  | Syntax.DeclVal { name; ty } ->
    Syntax.DeclVal { name; ty = annotate_self_ref_ty st ty }
  | Syntax.DeclType { name; ty } ->
    Syntax.DeclType { name; ty = annotate_self_ref_ty st ty }
  | Syntax.DeclMod { name; ty } ->
    Syntax.DeclMod { name; ty = annotate_self_ref_zip_sig st ty }
  | Syntax.DeclSig { name; ty } ->
    Syntax.DeclSig { name; ty = annotate_self_ref_unzip_sig st ty }

and annotate_self_ref_ty st ty =
  match ty with
  | Syntax.TyUnit -> ty
  | Syntax.TyVar var -> Syntax.TyVar (annotate_self_ref_prefixed st var)
;;

module Anchor_status = struct
  type t =
    | Anchorable of Syntax.Ty_var.t Syntax.prefixed
    | Used
end

let simplify_zip_sig st (zip_sig : Syntax.mod_zip_sig) =
  let zipper_self_set =
    zip_sig.zippers
    |> Bwd.to_list
    |> List.map ~f:(fun zipper -> zipper.self)
    |> Syntax.Self_var.Set.of_list
  in
  (* TODO: evaluate the unzip_sig while a type has a prefix in the zipper_set *)
  todo ()
;;

let anchor st path ty =
  match ty with
  | Syntax.SigStruct { self; decls } -> todo ()
  | _ -> todo ()
;;

let anchor_decl st path decl =
  match decl with
  | Syntax.DeclVal { ty; _ } -> todo ()
  | _ -> todo ()
;;

let annotate_self_ref st expr = E.catch (fun () -> annotate_self_ref_zip_sig st expr)
let infer_mod st expr = E.catch (fun () -> infer_mod_expr st expr)
