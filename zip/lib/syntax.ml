open! O

module Mod_var : sig
  include Variables.Fresh_var

  val of_surface : Surface.Mod_var.t -> t
end = struct
  include Variables.Fresh_var

  let of_surface v = create (Surface.Mod_var.name v)
end

module Mod_ty_var : sig
  include Variables.Fresh_var

  val of_surface : Surface.Mod_ty_var.t -> t
end = struct
  include Variables.Fresh_var

  let of_surface v = create (Surface.Mod_ty_var.name v)
end

module Var : sig
  include Variables.Fresh_var

  val of_surface : Surface.Var.t -> t
end = struct
  include Variables.Fresh_var

  let of_surface v = create (Surface.Var.name v)
end

module Ty_var : sig
  include Variables.Fresh_var

  val of_surface : Surface.Ty_var.t -> t
end = struct
  include Variables.Fresh_var

  let of_surface v = create (Surface.Ty_var.name v)
end

module Ty_abs_var : Variables.Fresh_var = Variables.Fresh_var
module Self_var : Variables.Fresh_var = Variables.Fresh_var

module Param_var : sig
  include Variables.Fresh_var

  val of_surface : Surface.Mod_var.t -> t
end = struct
  include Variables.Fresh_var

  let of_surface v = create (Surface.Mod_var.name v)
end

(* use Self_ref instead of Self_var *)
module Self_ref = struct
  type t =
    { var : Self_var.t
    ; index : int option
    ; necessary : bool
    }
  [@@deriving sexp_of]

  let equal { var; _ } { var = var'; _ } = Self_var.equal var var'
  let compare { var; _ } { var = var'; _ } = Self_var.compare var var'
  let create ?index ?(necessary = true) var = { var; index; necessary }
end

type prefix =
  | PrefixSelf of Self_ref.t
  | PrefixPath of mod_path
[@@deriving sexp_of]

and ('prefix, 'var) gen_prefixed =
  { prefix : 'prefix
  ; var : 'var
  }
[@@deriving sexp_of, equal]

and 'var prefixed = (prefix, 'var) gen_prefixed [@@deriving sexp_of, equal]
and 'var self_prefixed = (Self_var.t, 'var) gen_prefixed [@@deriving sexp_of, equal]

and mod_path =
  | PathAccess of Mod_var.t prefixed
  | PathParam of Param_var.t
  | PathZipperAccess of
      { path : mod_path
      ; zipper : Self_ref.t
      }
  | PathApp of
      { funct : mod_path
      ; arg : mod_path
      }
[@@deriving sexp_of, equal, compare]

and funct_param =
  | AppParam of
      { name : Param_var.t
      ; ty : mod_unzip_sig
      }
  | GenParam
[@@deriving sexp_of]

and mod_expr =
  | ModPath of mod_path
  | ModGenApp of mod_path
  | ModProj of
      { expr : mod_expr
      ; name : Mod_var.t
      }
  | ModAnn of
      { (* Allow expressions in annotations, annotations should not cause signature avoidance *)
        expr : mod_expr
      ; ty : mod_unzip_sig
      }
  | ModFunct of
      { param : funct_param
      ; body : mod_expr
      }
  | ModStruct of
      { self : Self_var.t
      ; binds : mod_bind Bwd.t
      }
[@@deriving sexp_of]

and mod_bind =
  | BindVal of
      { name : Var.t
      ; ty : ty option
      ; expr : expr
      }
  | BindType of
      { name : Ty_var.t
      ; ty : ty
      }
  | BindMod of
      { name : Mod_var.t
      ; expr : mod_expr
      }
  | BindSig of
      { name : Mod_ty_var.t
      ; ty : mod_unzip_sig
      }
[@@deriving sexp_of]

and mod_decl_val =
  { name : Var.t
  ; ty : ty
  }

and mod_decl_type =
  { name : Ty_var.t
  ; ty : ty
  }

and 'mod_sig mod_decl_mod =
  { name : Mod_var.t
  ; ty : 'mod_sig
  }

and mod_decl_sig =
  { name : Mod_ty_var.t
  ; ty : mod_unzip_sig
  }

(*
   Generic declaration.

   Polymorphic in the type of the module signature for module declarations.
   Normally these will just be signatures, but for transparent structure values we want them to be transparent ascriptions
*)
and 'mod_sig gen_mod_decl =
  | DeclVal of mod_decl_val
  | DeclType of mod_decl_type
  | DeclMod of 'mod_sig mod_decl_mod
  | DeclSig of mod_decl_sig
[@@deriving sexp_of]

and mod_decl = mod_zip_sig gen_mod_decl [@@deriving sexp_of]

(*
   < y1; y2; y3 > S

   is equivalent to

   < y1 > < y2 > < y3 > S

   is equivalent to

   < y1 > (< y2 > (< y3 > S))

   < > S

   is equivalent to

   S
*)
and mod_zip_sig =
  { zippers : zipper Bwd.t
  ; ty : mod_unzip_sig
  }
[@@deriving sexp_of]

and 'decl gen_zipper = 'decl gen_mod_sig_struct [@@deriving sexp_of]
and zipper = mod_sig_struct [@@deriving sexp_of]

and 'd gen_mod_sig_struct =
  { self : Self_var.t
  ; decls : 'd Bwd.t
  }
[@@deriving sexp_of]

and mod_sig_struct = mod_decl gen_mod_sig_struct [@@deriving sexp_of]

and 'mod_zip_sig gen_mod_sig_funct =
  { param : funct_param
  ; body_ty : 'mod_zip_sig
  }
[@@deriving sexp_of]

and mod_sig_funct = mod_zip_sig gen_mod_sig_funct [@@deriving sexp_of]

and mod_transparent_ascription =
  { path : mod_path
  ; ty : mod_unzip_sig
  }

and mod_unzip_sig =
  | SigVar of Mod_ty_var.t prefixed
  | SigFunct of mod_sig_funct
  | SigStruct of mod_sig_struct
  | SigTransparent of mod_transparent_ascription
[@@deriving sexp_of]

and expr =
  | ExprUnit
  | ExprVar of Var.t prefixed
[@@deriving sexp_of]

and ty =
  | TyUnit
  | TyVar of Ty_var.t prefixed
[@@deriving sexp_of]

let empty_sig_struct self = { self; decls = Bwd.Emp }
let zip_sig ty = { zippers = Bwd.Emp; ty }

let create_zip_sig zippers zip_sig =
  { zippers = Bwd.append zippers (Bwd.to_list zip_sig.zippers); ty = zip_sig.ty }
;;

let create_path_app funct args =
  List.fold_left ~init:funct ~f:(fun acc arg -> PathApp { funct = acc; arg }) args
;;

let create_funct params body =
  List.fold_right ~init:body ~f:(fun param acc -> ModFunct { param; body = acc }) params
;;

let map_gen_mod_decl ~f (decl : _ gen_mod_decl) =
  match decl with
  | DeclVal { name; ty } -> DeclVal { name; ty }
  | DeclType { name; ty } -> DeclType { name; ty }
  | DeclMod { name; ty } -> DeclMod { name; ty = f ty }
  | DeclSig { name; ty } -> DeclSig { name; ty }
;;

let map_prefixed_var ~f prefixed = { prefixed with var = f prefixed.var }
let map_gen_zipper_decl ~f zipper = { zipper with decls = Bwd.map ~f zipper.decls }
let zipper_to_sig_struct ({ self; decls } : zipper) : mod_sig_struct = { self; decls }
let zipper_to_sig ({ self; decls } : zipper) = SigStruct { self; decls }

(* weak head value *)
module Value = struct
  type mod_sig =
    | SigStruct of mod_sig_struct
    | SigFunct of mod_sig_funct
  [@@deriving sexp_of]
end

module Normal = struct
  type mod_transp_sig =
    { path : mod_path
    ; ty : Value.mod_sig
    }
  [@@deriving sexp_of]

  (* weak head normal form *)
  type mod_sig =
    | SigVal of Value.mod_sig
    | SigTransparent of mod_transp_sig
  [@@deriving sexp_of]
end

(*
   Everything is the transparent module is completely transparent,
   which is either a transparent ascription of some value with child signatures that are completely transparent.
   Transparent signatures are strengthened
*)
module Transparent = struct
  open struct
    type mod_zip_sig' = mod_zip_sig [@@deriving sexp_of]
    type mod_unzip_sig' = mod_unzip_sig [@@deriving sexp_of]
    type mod_decl' = mod_decl [@@deriving sexp_of]
  end

  type zipper = mod_decl gen_zipper [@@deriving sexp_of]

  (*
     Each transparent zip signature must be headed by a transparent signature.
     Also, the zipper must have transparent declarations.
  *)
  and mod_zip_sig =
    { zippers : zipper Bwd.t
    ; ty : mod_unzip_sig
    }
  [@@deriving sexp_of]

  and mod_unzip_sig = mod_transparent_ascription [@@deriving sexp_of]
  and mod_decl = mod_zip_sig gen_mod_decl [@@deriving sexp_of]
  and mod_sig_struct = mod_decl gen_mod_sig_struct [@@deriving sexp_of]

  module Value = struct
    (* we don't use the non transparent value here because the body of a SigGenFunct doesn't need to be transparent *)
    type mod_sig =
      | SigStruct of mod_sig_struct
      | SigAppFunct of
          { param : Param_var.t
          ; param_ty : mod_unzip_sig'
          ; body_ty : mod_zip_sig
          }
      | SigGenFunct of mod_zip_sig'
    [@@deriving sexp_of]
  end

  module Normal = struct
    type mod_transp_sig =
      { path : mod_path
      ; ty : Value.mod_sig
      }
    [@@deriving sexp_of]

    type mod_sig =
      | SigVal of Value.mod_sig
      | SigTransparent of mod_transp_sig
    [@@deriving sexp_of]
  end

  let zip_sig ty = { zippers = Bwd.Emp; ty }
end

module type Decl_map = sig
  type t

  val empty : t
  val add_exn : mod_decl -> t -> t
  val find_param : t -> Param_var.t -> mod_decl option
end

(* Fake haskell data kinds *)
module Var_promoted = struct
  type param_var = |
  type var = |
  type ty_var = |
  type mod_var = |
  type mod_ty_var = |
end

module Var_sum = struct
  module T = struct
    type t =
      | Param of Param_var.t
      | Var of Var.t
      | TyVar of Ty_var.t
      | ModVar of Mod_var.t
      | ModTyVar of Mod_ty_var.t
    [@@deriving sexp_of, compare, equal, hash, variants]
  end

  include T
  include Comparable.Make_plain (T)
end

module Var_sing = struct
  type _ t =
    | Param : Param_var.t -> Var_promoted.param_var t
    | Var : Var.t -> Var_promoted.var t
    | TyVar : Ty_var.t -> Var_promoted.ty_var t
    | ModVar : Mod_var.t -> Var_promoted.mod_var t
    | ModTyVar : Mod_ty_var.t -> Var_promoted.mod_ty_var t
  [@@deriving sexp_of, hash]

  let to_sum (type a) (sing : a t) =
    match sing with
    | Param x -> Var_sum.Param x
    | Var x -> Var_sum.Var x
    | TyVar x -> Var_sum.TyVar x
    | ModVar x -> Var_sum.ModVar x
    | ModTyVar x -> Var_sum.ModTyVar x
  ;;

  let compare x y = Var_sum.compare (to_sum x) (to_sum y)

  let g_equal (type a b) (x : a t) (y : b t) : (a, b) Type.eq option =
    match x, y with
    | Param x, Param y when Param_var.equal x y -> Some Type.Equal
    | Var x, Var y when Var.equal x y -> Some Type.Equal
    | TyVar x, TyVar y when Ty_var.equal x y -> Some Type.Equal
    | ModVar x, ModVar y when Mod_var.equal x y -> Some Type.Equal
    | ModTyVar x, ModTyVar y when Mod_ty_var.equal x y -> Some Type.Equal
    | _, _ -> None
  ;;
end

module Var_map = struct
  module type Arg = sig
    module Elem : sig
      type ('var, 'a) t
    end
  end

  module type S = sig
    type 'a t

    module Elem : sig
      type ('var, 'a) t
    end

    module Pair : sig
      type 'a t = P : 'var Var_sing.t * ('var, 'a) Elem.t -> 'a t
      type ('r, 'a) elim = { f : 'var. 'var Var_sing.t -> ('var, 'a) Elem.t -> 'r }

      val elim : 'a t -> ('r, 'a) elim -> 'r
    end

    val empty : 'a t
    val of_list_exn : 'a Pair.t list -> 'a t
    val union : 'a t -> 'a t -> 'a t
    val find : 'a t -> 'var Var_sing.t -> ('var, 'a) Elem.t option
    val find_exn : 'a t -> 'var Var_sing.t -> ('var, 'a) Elem.t
    val exists : 'a t -> 'var Var_sing.t -> bool
    val add_exn : 'a t -> 'var Var_sing.t -> ('var, 'a) Elem.t -> 'a t
    val add_override : 'a t -> 'var Var_sing.t -> ('var, 'a) Elem.t -> 'a t
  end

  module Make (Arg : Arg) : S with type ('var, 'a) Elem.t = ('var, 'a) Arg.Elem.t = struct
    open Arg
    module Elem = Elem

    module Pair = struct
      type 'a t = P : 'var Var_sing.t * ('var, 'a) Elem.t -> 'a t

      let get_sum (P (sing, _)) = Var_sing.to_sum sing

      type ('r, 'a) elim = { f : 'var. 'var Var_sing.t -> ('var, 'a) Elem.t -> 'r }

      let elim (type r a) (pair : a t) (elim : (r, a) elim) =
        match pair with
        | P (sing, elem) -> elim.f sing elem
      ;;
    end

    type 'a t = 'a Pair.t Var_sum.Map.t

    let of_list_exn ps =
      List.map ~f:(fun p -> Pair.get_sum p, p) ps |> Var_sum.Map.of_alist_exn
    ;;

    let empty = Var_sum.Map.empty

    let cast_pair (type var) (sing : var Var_sing.t) pair : (var, 'a) Elem.t option =
      match pair with
      | Pair.P (sing', elem) ->
        (match Var_sing.g_equal sing sing' with
         | Some Type.Equal -> Some elem
         | _ -> None)
    ;;

    let cast_pair_exn sing pair =
      match cast_pair sing pair with
      | Some elem -> elem
      | None -> raise_s [%message "internal error" (sing : _ Var_sing.t)]
    ;;

    let find t sing =
      Map.find t (Var_sing.to_sum sing) |> Option.map ~f:(cast_pair_exn sing)
    ;;

    let find_exn t sing =
      match find t sing with
      | Some elem -> elem
      | None -> raise_s [%message "Variable not found in map" (sing : _ Var_sing.t)]
    ;;

    let exists t sing = Option.is_some (find t sing)

    let add_exn t sing elem =
      Map.add_exn t ~key:(Var_sing.to_sum sing) ~data:(Pair.P (sing, elem))
    ;;

    let add_override t sing elem =
      Map.set t ~key:(Var_sing.to_sum sing) ~data:(Pair.P (sing, elem))
    ;;

    let union t1 t2 =
      Map.merge t1 t2 ~f:(fun ~key:_ ->
          function
          | `Both (x, _y) -> Some x
          | `Left x -> Some x
          | `Right x -> Some x)
    ;;
  end
end

module Prefixed_set : sig
  type t

  val empty : t
  val add : t -> Var_sum.t prefixed -> t
  val mem : t -> Var_sum.t prefixed -> bool
  val singleton : Var_sum.t prefixed -> t
end = struct
  module S = Set.Make_plain (struct
      type t = Var_sum.t prefixed [@@deriving sexp_of, compare, equal]
    end)

  type t = S.t

  let empty = S.empty
  let add = Set.add
  let mem = Set.mem
  let singleton = S.singleton
end

module Decl_elem = struct
  type ('var, 'mod_sig) t =
    | DeclVal : mod_decl_val -> (Var_promoted.var, 'mod_sig) t
    | DeclType : mod_decl_type -> (Var_promoted.ty_var, 'mod_sig) t
    | DeclMod : 'mod_sig mod_decl_mod -> (Var_promoted.mod_var, 'mod_sig) t
    | DeclSig : mod_decl_sig -> (Var_promoted.mod_ty_var, 'mod_sig) t
end

module Decl_map = struct
  include Var_map.Make (struct
      module Elem = Decl_elem
    end)
end

(* let decl_to_var_sum *)
let decl_to_pair = function
  | DeclVal decl -> Decl_map.Pair.P (Var decl.name, Decl_elem.DeclVal decl)
  | DeclType decl -> Decl_map.Pair.P (TyVar decl.name, Decl_elem.DeclType decl)
  | DeclMod decl -> Decl_map.Pair.P (ModVar decl.name, Decl_elem.DeclMod decl)
  | DeclSig decl -> Decl_map.Pair.P (ModTyVar decl.name, Decl_elem.DeclSig decl)
;;

module type Decl_struct = sig
  type 'mod_sig t

  val of_list : 'mod_sig gen_mod_decl list -> 'mod_sig t
  val of_bwd : 'mod_sig gen_mod_decl Bwd.t -> 'mod_sig t
  val to_list : 'mod_sig t -> 'mod_sig gen_mod_decl list
  val to_bwd : 'mod_sig t -> 'mod_sig gen_mod_decl Bwd.t
  val find : 'mod_sig t -> 'var Var_sing.t -> ('var, 'mod_sig) Decl_elem.t option
end

module Decl_struct : Decl_struct = struct
  type 'mod_sig t =
    { map : 'mod_sig Decl_map.t
    ; list : 'mod_sig gen_mod_decl Bwd.t
    }

  let of_list list =
    let map = List.map ~f:decl_to_pair list |> Decl_map.of_list_exn in
    { map; list = Bwd.of_list list }
  ;;

  let of_bwd bwd =
    let map = Bwd.to_list bwd |> List.map ~f:decl_to_pair |> Decl_map.of_list_exn in
    { map; list = bwd }
  ;;

  let to_list t = Bwd.to_list t.list
  let to_bwd t = t.list
  let find t var = Decl_map.find t.map var
end
