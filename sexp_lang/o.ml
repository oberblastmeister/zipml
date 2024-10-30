include Core

let ( let@ ) f x = f x
let todo () = raise_s [%message "todo"]