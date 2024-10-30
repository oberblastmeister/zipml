open! O

type t [@@deriving sexp_of]

module Elem : sig
  type t =
    | ParamVar of Syntax.Param_var.t * Syntax.Transparent.mod_unzip_sig
    | Zipper of Syntax.Transparent.zipper
  [@@deriving sexp_of]
end

val empty : t
val add_elem : Elem.t -> t -> t
val find_param : t -> Syntax.Param_var.t -> Syntax.Transparent.mod_unzip_sig option
val find_var : t -> Syntax.Var.t Syntax.self_prefixed -> Syntax.ty option
val find_ty_var : t -> Syntax.Ty_var.t Syntax.self_prefixed -> Syntax.ty option

val find_mod_var
  :  t
  -> Syntax.Mod_var.t Syntax.self_prefixed
  -> Syntax.Transparent.mod_zip_sig option

val find_mod_ty_var
  :  t
  -> Syntax.Mod_ty_var.t Syntax.self_prefixed
  -> Syntax.mod_unzip_sig option

val add_to_last_zipper_exn : Syntax.Self_var.t -> Syntax.Transparent.mod_decl -> t -> t

(* De bruijn index corresponding to the self var *)
val find_self_var_index_exn : Syntax.Self_var.t -> t -> int
val current_self_var_exn : t -> Syntax.Self_var.t
