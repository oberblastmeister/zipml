open! O

type 'a t = Cst.t -> 'a

module type Error_kind = sig
  type t [@@deriving sexp_of]

  val unexpected_empty_list : unit -> t
  val expected_list : got:Cst.t -> t
  val expected_atom : got:Cst.t -> t
  val unexpected_atom : got:Cst.t -> t
  val unexpected_item : got:Cst.t -> t
  val expected_literal : lit:string -> got:Cst.t -> t
end

module Sexp_error_kind : Error_kind with type t = Sexp.t

module Make (Error_kind : Error_kind) : sig
  module Error : sig
    type t =
      { kind : Error_kind.t
      ; span : Span.t
      }
    [@@deriving sexp_of]
  end

  module List_state : sig
    type t

    val with_s : Cst.t -> (t -> 'a) -> 'a
    val with_list : Cst.List.t -> (t -> 'a) -> 'a
    val with_list' : Cst.t list -> (t -> 'a) -> 'a
    val next : t -> Cst.t
    val next_opt : t -> Cst.t option
    val peek : t -> Cst.t option
    val put : Cst.t -> t -> unit
    val take : t -> Cst.t list
    val skip : t -> unit
  end

  val parse_error : Error_kind.t -> 'a
  val run : (unit -> 'a) -> ('a, Error.t) Result.t
  val with_span : Span.t -> (unit -> 'a) -> 'a
  val with_s : Cst.t -> (unit -> 'a) -> 'a
  val get_span : unit -> Span.t
  val atom : Cst.t -> (Cst.Atom.t -> 'a) -> 'a
  val expect_atom : Cst.t -> Cst.Atom.t
  val expect_literal : string -> Cst.t -> unit
  val expect_list : Cst.t -> Cst.List.t
  val string : Cst.t -> (string -> 'a) -> 'a
  val slist : Cst.t -> (Cst.List.t -> 'a) -> 'a
  val list : Cst.t -> (Cst.t list -> 'a) -> 'a
  val list_of : Cst.t -> (Cst.t -> 'a) -> 'a list
  val list_ref : Cst.t -> (Cst.t list ref -> 'a) -> 'a
  val item : Cst.t list ref -> (Cst.t -> 'a) -> 'a
  val next : Cst.t list ref -> Cst.t
  val finish : Cst.t list ref -> unit
  val optional_item : Cst.t list -> (Cst.t -> 'a) -> 'a option
  val rest : Cst.t list -> (Cst.t -> 'a) -> 'a list
  val either : (Cst.t -> 'a) -> (Cst.t -> 'b) -> ('a, 'b) Either.t t

  module Syntax : sig end
end
