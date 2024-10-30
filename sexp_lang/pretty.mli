module Ann : sig
  type t =
    | Line
    | IndentLine
  [@@deriving equal, compare, sexp]
end

module Delim : sig
  type t =
    | Paren
    | Brack
    | Brace
  [@@deriving sexp, equal, compare, sexp]
end


type t =
  | List of t list * Delim.t
  | Dot of t * t
  | Atom of string
  | Keyword of string
  | Ann of Ann.t
[@@deriving equal, compare, sexp]

val atom : string -> t
val (@.@) : t -> t -> t
val list : t list -> t
val brack_list : t list -> t
val brace_list : t list -> t
val char_of_open_delim : Delim.t -> char
val char_of_close_delim : Delim.t -> char
val to_string : t -> string