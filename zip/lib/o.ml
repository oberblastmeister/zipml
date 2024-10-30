include Core

module List = struct
  include List

  let intercalate ~sep xs =
    List.map xs ~f:(fun x -> [ x ]) |> List.intersperse ~sep |> List.concat
  ;;
end

module Bwd = struct
  include Bwd.BwdLabels

  open struct
    module Bwd = Bwd.BwdLabels
  end

  let sexp_of_t f t = sexp_of_list f (Bwd.to_list t)
  let t_of_sexp f sexp = List.t_of_sexp f sexp |> Bwd.of_list
  let equal = Bwd.equal
  let compare = Bwd.compare
end

let ( let@ ) f x = f x
let todo ?loc () = raise_s [%message "todo" (loc : Source_code_position.t option)]
