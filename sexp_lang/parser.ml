open! O

type 'a t = Cst.t -> 'a

module Pos = struct
  type t = int [@@deriving equal, compare, sexp]
end

module type Error_kind = sig
  type t [@@deriving sexp_of]

  val unexpected_empty_list : unit -> t
  val expected_list : got:Cst.t -> t
  val expected_atom : got:Cst.t -> t
  val unexpected_atom : got:Cst.t -> t
  val unexpected_item : got:Cst.t -> t
  val expected_literal : lit:string -> got:Cst.t -> t
end

module Sexp_error_kind = struct
  type t = Sexp.t [@@deriving sexp_of]

  let unexpected_empty_list () = [%message "unexpected empty list"]
  let expected_list ~got = [%message "expected list" (got : Cst.t)]
  let expected_atom ~got = [%message "expected atom" (got : Cst.t)]
  let unexpected_atom ~got = [%message "unexpected atom" (got : Cst.t)]
  let unexpected_item ~got = [%message "unexpected item" (got : Cst.t)]

  let expected_literal ~lit ~got =
    [%message "expected literal" (lit : string) (got : Cst.t)]
  ;;
end

module Make (Error_kind : Error_kind) = struct
  module R = Algaeff.Reader.Make (Span)

  module Error = struct
    type t =
      { kind : Error_kind.t
      ; span : Span.t
      }
    [@@deriving sexp_of]
  end

  exception Exn of Error.t

  let run f =
    try Result.Ok (R.run ~env:Span.empty f) with
    | Exn e -> Result.Error e
  ;;

  let with_span (span : Span.t) f = R.scope (const span) f
  let with_s sexp = with_span (Cst.get_span sexp)
  let get_span () = R.read ()
  let parse_error kind = raise (Exn { kind; span = R.read () })

  let expect_atom sexp =
    let@ () = with_s sexp in
    match sexp with
    | Cst.Atom atom -> atom
    | _ -> parse_error (Error_kind.expected_atom ~got:sexp)
  ;;

  let expect_list sexp =
    let@ () = with_s sexp in
    match sexp with
    | Cst.List list -> list
    | _ -> parse_error (Error_kind.expected_list ~got:sexp)
  ;;

  let expect_literal lit sexp =
    let@ () = with_s sexp in
    match sexp with
    | Cst.Atom { value; _ } when String.(value = lit) -> ()
    | _ -> parse_error (Error_kind.expected_literal ~lit ~got:sexp)
  ;;

  module List_state = struct
    type t =
      { mutable last_span : Span.t
      ; mutable xs : Cst.t list
      }

    let create (xs : Cst.List.t) = { last_span = xs.span; xs = xs.items }

    let with_list (list : Cst.List.t) f =
      let@ () = with_span list.span in
      let p = { last_span = list.span; xs = list.items } in
      let res = f p in
      (match p.xs with
       | [] -> ()
       | s :: _ -> parse_error (Error_kind.unexpected_item ~got:s));
      res
    ;;

    let with_list' xs f =
      let p = { last_span = get_span (); xs } in
      let res = f p in
      (match p.xs with
       | [] -> ()
       | s :: _ -> parse_error (Error_kind.unexpected_item ~got:s));
      res
    ;;

    let with_s sexp f = with_list (expect_list sexp) f
    let put x p = p.xs <- x :: p.xs

    let take p =
      let xs = p.xs in
      p.xs <- [];
      xs
    ;;

    let peek p =
      match p.xs with
      | [] -> None
      | x :: _ -> Some x
    ;;

    let next p =
      match p.xs with
      | [] ->
        let@ () = with_span p.last_span in
        parse_error (Error_kind.unexpected_empty_list ())
      | x :: xs ->
        p.xs <- xs;
        p.last_span <- Cst.get_span x;
        x
    ;;

    let next_opt p =
      match p.xs with
      | [] -> None
      | x :: xs ->
        p.xs <- xs;
        p.last_span <- Cst.get_span x;
        Some x
    ;;

    let skip p = next p |> ignore
  end

  let atom sexp f =
    with_s sexp (fun () ->
      match sexp with
      | Cst.Atom s -> f s
      | List _ | Keyword _ | Dot _ ->
        R.scope
          (const (Cst.get_span sexp))
          (fun () -> parse_error (Error_kind.expected_atom ~got:sexp)))
  ;;

  let string s f = atom s (fun s -> f s.value)

  let slist sexp f =
    with_span (Cst.get_span sexp) (fun () ->
      match sexp with
      | Cst.List x -> f x
      | Cst.Atom _ | Keyword _ | Dot _ -> parse_error (Error_kind.expected_list ~got:sexp))
  ;;

  let list sexp f = slist sexp (fun x -> f x.items)
  let list_ref sexp f = list sexp (fun xs -> f (ref xs))

  let list_of sexp f =
    slist sexp (fun sl ->
      List.map sl.items ~f:(fun item -> with_s item (fun () -> f item)))
  ;;

  let item list_ref f =
    match !list_ref with
    | [] -> parse_error (Error_kind.unexpected_empty_list ())
    | x :: xs ->
      list_ref := xs;
      let res = R.scope (const (Cst.get_span x)) (fun () -> f x) in
      res
  ;;

  let next list_ref =
    match !list_ref with
    | [] -> parse_error (Error_kind.unexpected_empty_list ())
    | x :: xs ->
      list_ref := xs;
      x
  ;;

  let finish list_ref =
    match !list_ref with
    | [] -> ()
    | x :: _xs -> parse_error (Error_kind.unexpected_atom ~got:x)
  ;;

  let optional_item list f =
    match list with
    | [] -> None
    | x :: [] -> with_span (Cst.get_span x) (fun () -> Some (f x))
    | _ -> None
  ;;

  let rest xs f = List.map xs ~f

  module Syntax = struct
    let ( <$> ) f p sexp = f (p sexp)

    let ( <|> ) p1 p2 sexp =
      match p1 sexp with
      | exception Exn _e1 -> p2 sexp
      | x -> x
    ;;
  end

  let either p1 p2 sexp = Syntax.(Either.first <$> p1 <|> (Either.second <$> p2)) sexp
end
