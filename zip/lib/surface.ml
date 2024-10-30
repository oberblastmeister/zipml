open! O
module Var : Variables.Var = Variables.Var
module Mod_var : Variables.Fresh_var = Variables.Fresh_var
module Mod_ty_var : Variables.Var = Variables.Var
module Ty_var : Variables.Var = Variables.Var

type mod_path =
  | PathName of Mod_var.t
  | PathAccess of
      { path : mod_path
      ; name : Mod_var.t
      }
  | PathApp of
      { funct : mod_path
      ; arg : mod_path
      }
[@@deriving sexp_of]

and funct_param =
  | AppParam of
      { name : Mod_var.t
      ; ty : mod_sig
      }
  | GenParam
[@@deriving sexp_of]

and funct_arg =
  | AppArg of mod_expr
  | GenArg

and mod_expr =
  | ModPath of mod_path
  | ModLet of
      { name : Mod_var.t
      ; expr : mod_expr
      ; body : mod_expr
      }
  | ModProj of
      { expr : mod_expr
      ; name : Mod_var.t
      }
  | ModAnn of
      { expr : mod_expr
      ; ty : mod_sig
      }
  | ModApp of
      { expr : mod_expr
      ; arg : funct_arg
      }
  | ModFunct of
      { param : funct_param
      ; body : mod_expr
      }
  | ModStruct of mod_bind list
[@@deriving sexp_of]

and mod_bind =
  | BindVal of
      { name : Var.t
      ; ty : ty option
      ; expr : expr
      }
  | BindType of
      { name : Ty_var.t
      ; ty : ty
      }
  | BindMod of
      { name : Mod_var.t
      ; expr : mod_expr
      }
  | BindSig of
      { name : Mod_ty_var.t
      ; ty : mod_sig
      }
[@@deriving sexp_of]

and mod_decl =
  | DeclVal of
      { name : Var.t
      ; ty : ty
      }
  | DeclType of
      { name : Ty_var.t
      ; ty : ty option
      }
  | DeclMod of
      { name : Mod_var.t
      ; ty : mod_sig
      }
  | DeclSig of
      { name : Mod_ty_var.t
      ; ty : mod_sig
      }
[@@deriving sexp_of]

and mod_sig =
  | SigVar of Mod_ty_var.t
  | SigAccess of
      { path : mod_path
      ; name : Mod_ty_var.t
      }
  | SigFunct of
      { param : funct_param
      ; body_ty : mod_sig
      }
  | SigStruct of mod_decl list
  | SigTransparent of
      { path : mod_path
      ; ty : mod_sig
      }
[@@deriving sexp_of]

and expr =
  | ExprUnit
  | ExprVar of Var.t
  | ExprApp of
      { func : expr
      ; arg : expr
      }
  | ExprAccess of
      { path : mod_path
      ; name : Var.t
      }
[@@deriving sexp_of]

and ty =
  | TyUnit
  | TyVar of Ty_var.t
  | TyAccess of
      { path : mod_path
      ; name : Ty_var.t
      }
[@@deriving sexp_of]

and ident =
  | Param of Mod_var.t
  | ModVar of Mod_var.t
  | ModTyVar of Mod_ty_var.t
  | Var of Var.t
  | TyVar of Ty_var.t
[@@deriving sexp_of]

let create_path_app funct args =
  List.fold_left ~init:funct ~f:(fun acc arg -> PathApp { funct = acc; arg }) args
;;

let create_mod_expr_app funct args =
  List.fold_left ~init:funct ~f:(fun acc arg -> ModApp { expr = acc; arg }) args
;;

let create_funct params body =
  List.fold_right ~init:body ~f:(fun param acc -> ModFunct { param; body = acc }) params
;;

let create_funct_ty params body_ty =
  List.fold_right
    ~init:body_ty
    ~f:(fun param acc -> SigFunct { param; body_ty = acc })
    params
;;

let create_expr_app func args =
  List.fold_left ~init:func ~f:(fun arg acc -> ExprApp { func = acc; arg }) args
;;
