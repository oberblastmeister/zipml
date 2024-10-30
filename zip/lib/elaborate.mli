open! O

module Opacity : sig
  type t =
    | Opaque
    | Transparent
  [@@deriving sexp_of, equal, compare]

  val combine : t -> t -> t
end

type st

val create_state : ?debug:bool -> unit -> st
val infer_mod : st -> Syntax.mod_expr -> (Opacity.t * Syntax.mod_zip_sig) Or_error.t
val annotate_self_ref : st -> Syntax.mod_zip_sig -> Syntax.mod_zip_sig Or_error.t
