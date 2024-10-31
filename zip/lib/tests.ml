open! O

let check_parse s =
  let res = Parse.parse s in
  print_s [%sexp (res : Surface.mod_expr Or_error.t)]
;;

let check_rename s =
  let res =
    let open Result.Let_syntax in
    let%bind res = Parse.parse s in
    let%bind ren = Rename.rename_mod_expr (Rename.create_state ()) res in
    Ok ren
  in
  print_s [%sexp (res : Syntax.mod_expr Or_error.t)]
;;

let check_infer ?debug s =
  let res =
    let open Result.Let_syntax in
    let%bind res = Parse.parse s in
    let%bind ren = Rename.rename_mod_expr (Rename.create_state ()) res in
    let st = Elaborate.create_state ?debug () in
    let%bind opacity, mod_ty = Elaborate.infer_mod st ren in
    let%bind mod_ty = Elaborate.annotate_self_ref st mod_ty in
    let printed_mod_ty = Pretty.pretty_zip_sig mod_ty in
    Ok (opacity, printed_mod_ty)
  in
  match res with
  | Ok (opacity, printed_mod_ty) ->
    print_s [%sexp (opacity : Elaborate.Opacity.t)];
    print_endline printed_mod_ty;
    ()
  | Error e -> print_s [%message "Error" (e : Error.t)]
;;

let%expect_test "parse" =
  check_parse {|
  (val first mkunit)
  |};
  [%expect {| (Ok (ModStruct ((BindVal (name first) (ty ()) (expr ExprUnit))))) |}]
;;

let%expect_test "not valid mod name" =
  check_parse {|
    (module first (struct))
    |};
  [%expect {| (Error ("expected module ident" (got first))) |}]
;;

let%expect_test "parse mod ascription" =
  check_rename
    {|
  (module First
    (struct
      (type t unit)
    )
  )

  (module Second
    (:
      First
      (sig (type t))
    )
  )

  (module Third : (sig (type t))
    First)
  |};
  [%expect
    {|
    (Ok
     (ModStruct (self ((name self) (id 2)))
      (binds
       ((BindMod (name ((name First) (id -1)))
         (expr
          (ModStruct (self ((name self) (id 3)))
           (binds ((BindType (name ((name t) (id -1))) (ty TyUnit)))))))
        (BindMod (name ((name Second) (id -1)))
         (expr
          (ModAnn
           (expr
            (ModPath
             (PathAccess
              ((prefix
                (PrefixSelf
                 ((var ((name self) (id 2))) (index ()) (necessary true))))
               (var ((name First) (id -1)))))))
           (ty
            (SigStruct
             ((self ((name self) (id 4)))
              (decls
               ((DeclType
                 ((name ((name t) (id -1)))
                  (ty
                   (TyVar
                    ((prefix
                      (PrefixSelf
                       ((var ((name self) (id 4))) (index ()) (necessary true))))
                     (var ((name t) (id -1))))))))))))))))
        (BindMod (name ((name Third) (id -1)))
         (expr
          (ModAnn
           (expr
            (ModPath
             (PathAccess
              ((prefix
                (PrefixSelf
                 ((var ((name self) (id 2))) (index ()) (necessary true))))
               (var ((name First) (id -1)))))))
           (ty
            (SigStruct
             ((self ((name self) (id 5)))
              (decls
               ((DeclType
                 ((name ((name t) (id -1)))
                  (ty
                   (TyVar
                    ((prefix
                      (PrefixSelf
                       ((var ((name self) (id 5))) (index ()) (necessary true))))
                     (var ((name t) (id -1))))))))))))))))))))
    |}]
;;

let%expect_test "parse more" =
  check_parse
    {|
  (val first mkunit)

  (module First
    (struct
      (type t unit)

      (val x : t
        mkunit)
    )
  )
  |};
  [%expect
    {|
    (Ok
     (ModStruct
      ((BindVal (name first) (ty ()) (expr ExprUnit))
       (BindMod (name ((name First) (id -1)))
        (expr
         (ModStruct
          ((BindType (name t) (ty TyUnit))
           (BindVal (name x) (ty ((TyVar t))) (expr ExprUnit)))))))))
    |}]
;;

let%expect_test "simple app funct" =
  check_parse
    {|
  (module type Stack
    (sig
      (type t)
      (type value)
      (type another unit)

      (val push : t)
      (val empty : t)
    )
  )

  (module (First () (X : (sig)) (Y : (sig)))
    (struct
      (type t unit)
    )
  )

  (module Another
    (functor
      (Y : (sig)) ->
      (struct
        (type t unit)

        (val x : t mkunit)
      )
    )
  )
|};
  [%expect
    {|
    (Ok
     (ModStruct
      ((BindSig (name Stack)
        (ty
         (SigStruct
          ((DeclType (name t) (ty ())) (DeclType (name value) (ty ()))
           (DeclType (name another) (ty (TyUnit)))
           (DeclVal (name push) (ty (TyVar t)))
           (DeclVal (name empty) (ty (TyVar t)))))))
       (BindMod (name ((name First) (id -1)))
        (expr
         (ModFunct (param GenParam)
          (body
           (ModFunct
            (param (AppParam (name ((name X) (id -1))) (ty (SigStruct ()))))
            (body
             (ModFunct
              (param (AppParam (name ((name Y) (id -1))) (ty (SigStruct ()))))
              (body (ModStruct ((BindType (name t) (ty TyUnit))))))))))))
       (BindMod (name ((name Another) (id -1)))
        (expr
         (ModFunct
          (param (AppParam (name ((name Y) (id -1))) (ty (SigStruct ()))))
          (body
           (ModStruct
            ((BindType (name t) (ty TyUnit))
             (BindVal (name x) (ty ((TyVar t))) (expr ExprUnit)))))))))))
    |}]
;;

let%expect_test "rename" =
  check_rename
    {|
  (val first mkunit)

  (val second mkunit)

  (type t unit)

  (val third : t
    mkunit)

  (module First
    (struct
      (type t unit)

      (val x : t
        mkunit)
    )
  )
    |};
  [%expect
    {|
    (Ok
     (ModStruct (self ((name self) (id 2)))
      (binds
       ((BindVal (name ((name first) (id -1))) (ty ()) (expr ExprUnit))
        (BindVal (name ((name second) (id -1))) (ty ()) (expr ExprUnit))
        (BindType (name ((name t) (id -1))) (ty TyUnit))
        (BindVal (name ((name third) (id -1)))
         (ty
          ((TyVar
            ((prefix
              (PrefixSelf
               ((var ((name self) (id 2))) (index ()) (necessary true))))
             (var ((name t) (id -1)))))))
         (expr ExprUnit))
        (BindMod (name ((name First) (id -1)))
         (expr
          (ModStruct (self ((name self) (id 3)))
           (binds
            ((BindType (name ((name t) (id -1))) (ty TyUnit))
             (BindVal (name ((name x) (id -1)))
              (ty
               ((TyVar
                 ((prefix
                   (PrefixSelf
                    ((var ((name self) (id 3))) (index ()) (necessary true))))
                  (var ((name t) (id -1)))))))
              (expr ExprUnit)))))))))))
    |}]
;;

let%expect_test "simple app funct" =
  check_rename
    {|
  (module type Stack
    (sig
      (type t)
      (type value)
      (type another unit)

      (module Bruh : (sig))

      (module F :
        (functor
          (X : (sig (type t))) () (Y : (sig)) -> (sig (type t X.t))
        )
      )

      (val push : t)
      (val empty : t)
    )
  )

  (module (First () (X : (sig)) (Y : (sig)))
    (struct
      (type t unit)
    )
  )

  (module Another
    (functor
      (Y : (sig)) ->
      (struct
        (type t unit)

        (val x : t mkunit)
      )
    )
  )
|};
  [%expect
    {|
    (Ok
     (ModStruct (self ((name self) (id 2)))
      (binds
       ((BindSig (name ((name Stack) (id -1)))
         (ty
          (SigStruct
           ((self ((name self) (id 3)))
            (decls
             ((DeclType
               ((name ((name t) (id -1)))
                (ty
                 (TyVar
                  ((prefix
                    (PrefixSelf
                     ((var ((name self) (id 3))) (index ()) (necessary true))))
                   (var ((name t) (id -1))))))))
              (DeclType
               ((name ((name value) (id -1)))
                (ty
                 (TyVar
                  ((prefix
                    (PrefixSelf
                     ((var ((name self) (id 3))) (index ()) (necessary true))))
                   (var ((name value) (id -1))))))))
              (DeclType ((name ((name another) (id -1))) (ty TyUnit)))
              (DeclMod
               ((name ((name Bruh) (id -1)))
                (ty
                 ((zippers ())
                  (ty (SigStruct ((self ((name self) (id 4))) (decls ()))))))))
              (DeclMod
               ((name ((name F) (id -1)))
                (ty
                 ((zippers ())
                  (ty
                   (SigFunct
                    ((param
                      (AppParam (name ((name X) (id -1)))
                       (ty
                        (SigStruct
                         ((self ((name self) (id 5)))
                          (decls
                           ((DeclType
                             ((name ((name t) (id -1)))
                              (ty
                               (TyVar
                                ((prefix
                                  (PrefixSelf
                                   ((var ((name self) (id 5))) (index ())
                                    (necessary true))))
                                 (var ((name t) (id -1)))))))))))))))
                     (body_ty
                      ((zippers ())
                       (ty
                        (SigFunct
                         ((param GenParam)
                          (body_ty
                           ((zippers ())
                            (ty
                             (SigFunct
                              ((param
                                (AppParam (name ((name Y) (id -1)))
                                 (ty
                                  (SigStruct
                                   ((self ((name self) (id 6))) (decls ()))))))
                               (body_ty
                                ((zippers ())
                                 (ty
                                  (SigStruct
                                   ((self ((name self) (id 7)))
                                    (decls
                                     ((DeclType
                                       ((name ((name t) (id -1)))
                                        (ty
                                         (TyVar
                                          ((prefix
                                            (PrefixPath
                                             (PathParam ((name X) (id -1)))))
                                           (var ((name t) (id -1))))))))))))))))))))))))))))))))
              (DeclVal
               ((name ((name push) (id -1)))
                (ty
                 (TyVar
                  ((prefix
                    (PrefixSelf
                     ((var ((name self) (id 3))) (index ()) (necessary true))))
                   (var ((name t) (id -1))))))))
              (DeclVal
               ((name ((name empty) (id -1)))
                (ty
                 (TyVar
                  ((prefix
                    (PrefixSelf
                     ((var ((name self) (id 3))) (index ()) (necessary true))))
                   (var ((name t) (id -1))))))))))))))
        (BindMod (name ((name First) (id -1)))
         (expr
          (ModFunct (param GenParam)
           (body
            (ModFunct
             (param
              (AppParam (name ((name X) (id -1)))
               (ty (SigStruct ((self ((name self) (id 8))) (decls ()))))))
             (body
              (ModFunct
               (param
                (AppParam (name ((name Y) (id -1)))
                 (ty (SigStruct ((self ((name self) (id 9))) (decls ()))))))
               (body
                (ModStruct (self ((name self) (id 10)))
                 (binds ((BindType (name ((name t) (id -1))) (ty TyUnit)))))))))))))
        (BindMod (name ((name Another) (id -1)))
         (expr
          (ModFunct
           (param
            (AppParam (name ((name Y) (id -1)))
             (ty (SigStruct ((self ((name self) (id 11))) (decls ()))))))
           (body
            (ModStruct (self ((name self) (id 12)))
             (binds
              ((BindType (name ((name t) (id -1))) (ty TyUnit))
               (BindVal (name ((name x) (id -1)))
                (ty
                 ((TyVar
                   ((prefix
                     (PrefixSelf
                      ((var ((name self) (id 12))) (index ()) (necessary true))))
                    (var ((name t) (id -1)))))))
                (expr ExprUnit)))))))))))))
    |}]
;;

let%expect_test "simple infer val" =
  check_infer {|
  (val first mkunit)
  |};
  [%expect {|
    Transparent
    (sig
      (val first : unit))
    |}]
;;

let%expect_test "simple infer struct" =
  check_infer
    {|
  (val first mkunit)

  (module First
    (struct
      (type t unit)

      (val x : t
        mkunit)
    )
  )
  |};
  [%expect
    {|
    Transparent
    (sig
      (val first : unit)
      (module First :
        (sig
          (type t unit)
          (val x : Self.t))))
    |}]
;;

let%expect_test "simple infer ascription" =
  check_infer
    {|
    (module First
      (struct
        (type t unit)

        (val x : t
          mkunit)
      )
    )

    (module Second
      (:
        First
        (sig
          (type t)

          (val x : t)
        )
      )
    )

    (val res : Second.t
      Second.x)
  |};
  [%expect
    {|
    Transparent
    (sig
      (module First :
        (sig
          (type t unit)
          (val x : Self.t)))
      (module Second :
        (sig
          (type t Self.t)
          (val x : Self.t)))
      (val res : Self.Second.t))
    |}]
;;

let%expect_test "simple infer ascription fail" =
  check_infer
    {|
  (module First
    (struct
      (type t unit)

      (val x : t
        mkunit)
    )
  )

  (module Second
    (:
      First
      (sig
        (type t)

        (val x : t)
      )
    )
  )

  (val res : Second.t
    mkunit)
  |};
  [%expect
    {|
    (Error
     (e
      ((ty1
        (TyVar
         ((prefix
           (PrefixPath
            (PathAccess
             ((prefix
               (PrefixSelf
                ((var ((name self) (id 2))) (index ()) (necessary true))))
              (var ((name Second) (id -1)))))))
          (var ((name t) (id -1))))))
       != (ty2 TyUnit) because
       (ty1'
        (TyVar
         ((prefix
           (PrefixPath
            (PathAccess
             ((prefix
               (PrefixSelf
                ((var ((name self) (id 2))) (index ()) (necessary true))))
              (var ((name Second) (id -1)))))))
          (var ((name t) (id -1))))))
       != (ty2' TyUnit))))
    |}]
;;

let%expect_test "applicative functor" =
  check_infer
    {|
  (module First
    (struct
      (type t unit)

      (val x : t
        mkunit)
    )
  )

  (module Second
    (:
      First
      (sig
        (type t)

        (val x : t)
      )
    )
  )

  (module type Type
    (sig
      (type t)
    )
  )

  (module type Result
    (sig
      (type t)

      (val v : t)
    )
  )
  |};
  [%expect
    {|
    Transparent
    (sig
      (module First :
        (sig
          (type t unit)
          (val x : Self.t)))
      (module Second :
        (sig
          (type t Self.t)
          (val x : Self.t)))
      (module type Type
        (sig
          (type t Self.t)))
      (module type Result
        (sig
          (type t Self.t)
          (val v : Self.t))))
    |}]
;;

let%expect_test "single applicative functor" =
  check_infer
    {|
  (module type Type
    (sig
      (type t)
    )
  )

  (module type Result
    (sig
      (type t)

      (val v : t)
    )
  )

  (module (F (T : Type)) : Result
    (struct
      (type t unit)
      (type t' T.t)

     (val v mkunit)
    )
  )

  (module (Id (T : Type))
    (:
      (struct
        (type t T.t)
      )
      (sig
        (type t T.t)
      )
    )
  )

  (module T1 : Type 
    (struct (type t unit))
  )

  (module T2
    (:
      (struct (type t unit))
      Type
    )
  )

  (module T3 T2)

  (module T4 T3)

  (module T5 (: T3 (= T3 < Type)))

  (module T6 T5)

  (module T7 (: T6 (= T2 < Type)))

  (module T8 (Id T7))

  (module FT1 (F T1))

  (module FT2 (F T2))

  (module F' F)

  (module F'' F')

  (module F''1 (F'' T1))

  (module type TypeType
    (sig
      (type t)
      (type t')
    )
  )

  (module (MakeTypeType ())
    (:
      (struct
        (type t unit)
        (type t' unit)
      )
      TypeType
    )
  )

  (module TT1 (MakeTypeType ()))

  (module TT2 (MakeTypeType ()))
  |};
  [%expect
    {|
    Opaque
    (sig
      (module type Type
        (sig
          (type t Self.t)))
      (module type Result
        (sig
          (type t Self.t)
          (val v : Self.t)))
      (module F :
        (functor (T : Self.Type)
          Self.Result))
      (module Id :
        (functor (T : Self.Type)
          (sig
            (type t T.t))))
      (module T1 :
        Self.Type)
      (module T2 :
        Self.Type)
      (module T3 :
        (= Self.T2 < Self.Type))
      (module T4 :
        (= Self.T2 < Self.Type))
      (module T5 :
        (= Self.T3 < Self.Type))
      (module T6 :
        (= Self.T3 < Self.Type))
      (module T7 :
        (= Self.T2 < Self.Type))
      (module T8 :
        (= (Self.Id Self.T7) < (sig
          (type t Super.T7.t))))
      (module FT1 :
        (= (Self.F Self.T1) < Self.Result))
      (module FT2 :
        (= (Self.F Self.T2) < Self.Result))
      (module F' :
        (= Self.F < (functor (T : Self.Type)
          Self.Result)))
      (module F'' :
        (= Self.F < (functor (T : Self.Type)
          Self.Result)))
      (module F''1 :
        (= (Self.F Self.T1) < Self.Result))
      (module type TypeType
        (sig
          (type t Self.t)
          (type t' Self.t')))
      (module MakeTypeType :
        (functor ()
          Self.TypeType))
      (module TT1 :
        Self.TypeType)
      (module TT2 :
        Self.TypeType))
    |}]
;;

let%expect_test "signature avoidance" =
  check_infer
    ~debug:true
    {|
  (module Weird
    (:
      (struct
        (type t unit)

        (val x
          mkunit)

        (module M
          (struct
            (type t t)
          )
        )

      )
      (sig
        (type t)

        (val x : t)

        (module M :
          (sig
            (type t t)
          )
        )
      )
    ).M
  )

  (module M Weird)

  (module type Type
    (sig
      (type t)
    )
  )

  (module M'
    (:
      M
      Type
    )
  )

  |};
  [%expect
    {|
    Transparent
    (sig
      (module Weird :
        (zip
          ((sig
            (type t Self.t)
            (val x : Self.t)))
          (sig
            (type t Super.t))))
      (module M :
        (zip
          ((sig
            (type t Super.Weird.Hidden.Self.t)
            (val x : Super.Weird.Hidden.Self.t)))
          (= Super.Weird < (sig
            (type t Super.Super.Weird.Hidden.Self.t)))))
      (module type Type
        (sig
          (type t Self.t)))
      (module M' :
        Self.Type))
    |}]
;;

let%expect_test "wrong opacity" =
  check_infer
    ~debug:true
    {|
  (module (Gen ())
    (struct
      (type t unit)

      (val x mkunit)
    )
  )

  (module (App (A : (sig)))
    (struct
      (module M (Gen ()))
    )
  )
  |};
  [%expect
    {|
    (Error
     (e
      ("Body of an applicative functor must be transparent"
       (param
        (AppParam (name ((name A) (id -1)))
         (ty (SigStruct ((self ((name self) (id 4))) (decls ()))))))
       (body
        (ModStruct (self ((name self) (id 5)))
         (binds
          ((BindMod (name ((name M) (id -1)))
            (expr
             (ModGenApp
              (PathAccess
               ((prefix
                 (PrefixSelf
                  ((var ((name self) (id 2))) (index ()) (necessary true))))
                (var ((name Gen) (id -1)))))))))))))))
    |}]
;;

let%expect_test "module type not in scope" =
  check_infer
    {|
  (module M
    (struct
    )
  )

  (module type S M.T)

  (type t M.t)
  |};
  [%expect
    {|
    (Error
     (e
      ("did not find module type in signature"
       (path
        (PathAccess
         ((prefix
           (PrefixSelf ((var ((name self) (id 2))) (index ()) (necessary true))))
          (var ((name M) (id -1))))))
       (var ((name T) (id -1)))
       (ty_val (SigStruct ((self ((name self) (id 3))) (decls ())))))))
    |}]
;;

let%expect_test "type not in scope" =
  check_infer {|
  (module M
    (struct
    )
  )

  (type t M.t)
  |};
  [%expect
    {|
    (Error
     (e
      ("did not find module type in signature"
       (path
        (PathAccess
         ((prefix
           (PrefixSelf ((var ((name self) (id 2))) (index ()) (necessary true))))
          (var ((name M) (id -1))))))
       (var ((name t) (id -1)))
       (ty_val (SigStruct ((self ((name self) (id 3))) (decls ())))))))
    |}]
;;

let%expect_test "applicative functor without path" =
  check_infer
    {|
  (module type Type
    (sig
      (type t)))

  (module (F (A : Type))
    (:
      (struct
        (type t A.t)
      )
      Type
    )
  )

  (module A
    (F
      (struct
        (type t unit)
      )
    )
  )

  (module B
    (F
      (struct
        (type t unit)
      )
    )
  )
  |};
  [%expect
    {|
    Transparent
    (sig
      (module type Type
        (sig
          (type t Self.t)))
      (module F :
        (functor (A : Self.Type)
          Self.Type))
      (module A :
        (zip
          ((sig
            (module App_funct :
              (= Super.F < (functor (A : Super.Type)
                Super.Type))))
          (sig
            (module App_arg :
              (sig
                (type t unit)))))
          (= (Super.Super.F Self.App_arg) < Super.Super.Type)))
      (module B :
        (zip
          ((sig
            (module App_funct :
              (= Super.F < (functor (A : Super.Type)
                Super.Type))))
          (sig
            (module App_arg :
              (sig
                (type t unit)))))
          (= (Super.Super.F Self.App_arg) < Super.Super.Type))))
    |}]
;;

let%expect_test "functor expression" =
  check_infer
    {|
  (module type Type
    (sig
      (type t)))

  (module T
    (struct
      (type t unit)
    )
  )

  (module M
    (
      (functor (A : Type) ->
        (:
          (struct
            (type t unit)
          )
          Type
        )
      )
      T
    )
  )
  |};
  [%expect
    {|
    Transparent
    (sig
      (module type Type
        (sig
          (type t Self.t)))
      (module T :
        (sig
          (type t unit)))
      (module M :
        (zip
          ((sig
            (module App_funct :
              (functor (A : Super.Type)
                Super.Type)))
          (sig
            (module App_arg :
              (= Super.Super.T < (sig
                (type t unit))))))
          (= (Super.App_funct Self.App_arg) < Super.Super.Type))))
    |}]
;;
