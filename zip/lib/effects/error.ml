open! O

module Make (E : sig
    type t
  end) : sig
  val raise : E.t -> _
  val catch : (unit -> 'a) -> ('a, E.t) result
end = struct
  exception Exn of E.t

  let raise e = raise (Exn e)

  let catch f =
    match f () with
    | x -> Ok x
    | exception Exn s -> Error s
  ;;
end
