open Core

module Delim : sig
  type t =
    | Paren
    | Bracket
    | Brace
  [@@deriving sexp, compare, equal, hash]
end

module Atom : sig
  type t =
    { span : Span.t
    ; value : string
    }
  [@@deriving equal, compare, sexp]
end

module Keyword : sig
  type t =
    { span : Span.t
    ; value : string
    }
  [@@deriving equal, compare, sexp]
end

type t =
  | Atom of Atom.t
  | Keyword of Keyword.t
  | Dot of dot
  | List of slist
[@@deriving equal, compare, sexp]

and dot =
  { span : Span.t
  ; lhs : t
  ; rhs : t
  }
[@@deriving equal, compare, sexp]

and slist =
  { span : Span.t
  ; items : t list
  ; delim : Delim.t
  }
[@@deriving equal, compare, sexp]

module List : sig
  type nonrec t = slist =
    { span : Span.t
    ; items : t list
    ; delim : Delim.t
    }
  [@@deriving equal, compare, sexp]
end

module Dot : sig
  type nonrec t = dot =
    { span : Span.t
    ; lhs : t
    ; rhs : t
    }
  [@@deriving equal, compare, sexp]
end

module Token : sig
  type t =
    | LParen
    | RParen
    | LBrack
    | RBrack
    | LBrace
    | RBrace
    | Dot
    | Atom of string
    | Keyword of string
    | Error of string
  [@@deriving sexp, compare, equal]
end

module SpannedToken : sig
  type t =
    { token : Token.t
    ; span : Span.t
    }
  [@@deriving sexp]
end

val tokenize : string -> SpannedToken.t list
val parse_tokens : SpannedToken.t list -> t list Or_error.t
val parse_tokens_single : SpannedToken.t list -> t Or_error.t
val parse : string -> t list Or_error.t
val parse_single : string -> t Or_error.t
val get_span : t -> Span.t
