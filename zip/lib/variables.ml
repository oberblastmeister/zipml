open! O

module type Var = sig
  type t [@@deriving sexp_of, compare, equal, hash]

  val create : string -> t
  val name : t -> string
end

module Var : Var = struct
  type t = string [@@deriving sexp_of, compare, equal, hash]

  let create name = name
  let name t = t
end

module type Id_var = sig
  type t [@@deriving sexp_of, compare, equal, hash]

  val create : int -> t
  val create_fresh : int ref -> t
  val id : t -> int
end

module type Fresh_var = sig
  type t [@@deriving sexp_of, compare, equal, hash]

  val create : ?id:int -> string -> t
  val create_fresh : int ref -> string -> t
  val name : t -> string
  val id : t -> int

  include Comparable.S_plain with type t := t
end

module Fresh_var : Fresh_var = struct
  module T = struct
    type t =
      { name : string
      ; id : int
      }
    [@@deriving sexp_of, compare, equal, hash]
  end

  include T

  let create ?(id = -1) name = { name; id }

  let create_fresh id_ref name =
    let res = create ~id:!id_ref name in
    incr id_ref;
    res
  ;;

  let name t = t.name
  let id t = t.id

  include Comparable.Make_plain (T)
end

module Id_var : Id_var = struct
  type t = int [@@deriving sexp_of, compare, equal, hash]

  let create id = id

  let create_fresh id_ref =
    let res = create !id_ref in
    incr id_ref;
    res
  ;;

  let id t = t
end

let testing =
  let module M = struct
    type t
  end
  in
  let module M = struct
    type t
  end
  in
  ()
;;
