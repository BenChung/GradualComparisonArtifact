module AST

type Type =
| Any
| Class of string
 override x.ToString() = sprintf "%A" x

type Expr =
| Var of string
| This
| That
| NewExn of string * (Expr list)
| GetF of string
| SetF of string * Expr
| Call of Expr * Type * Type * string * Expr
| DynCall of Expr * string * Expr * FParsec.Position
| SubCast of Type * Expr * FParsec.Position
| BehCast of Type * Expr * FParsec.Position
 override x.ToString() = sprintf "%A" x

let rec subst(n:string, wth : Expr)(ine:Expr) = 
    match ine with
    | Var np -> if np = n then wth else Var np
    | This -> This
    | That -> That
    | NewExn(name, exprs) -> NewExn(name, List.map (subst(n, wth)) exprs)
    | GetF(f) -> GetF(f)
    | SetF(f, v) -> SetF(f, subst(n,wth)(v))
    | Call(recr, t1, t2, m, arg) -> Call(subst(n,wth) recr, t1, t2, m, subst(n,wth) arg)
    | DynCall(recr, m, arg, p) -> DynCall(subst(n,wth) recr, m, subst(n,wth) arg, p)
    | SubCast(t, e, p) -> SubCast(t, subst(n,wth) e, p)
    | BehCast(t, e, p) -> BehCast(t, subst(n,wth) e, p)

type md = 
| MDef of string * string * Type * Type * Expr list
 override x.ToString() = sprintf "%A" x

type fd =
| FDef of string * Type
 override x.ToString() = sprintf "%A" x

type k =
| ClassDef of string * fd list * md list
 override x.ToString() = sprintf "%A" x

type prog =
| Program of k list * Expr
 override x.ToString() = sprintf "%A" x

  