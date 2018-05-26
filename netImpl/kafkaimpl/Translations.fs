module Translations
open SurfAST
open Typechecker

let rec private butlast<'a,'b>(f1 : 'a -> 'b)(f2 : 'a -> 'b)(l:'a list) : 'b list = 
    match l with
    | e1 :: e2 :: r -> f1(e1) :: butlast(f1)(f2)(e2::r)
    | e2 :: nil -> [f2(e2)]
    | nil -> []

exception ClassNotFound of string*Map<string, SurfAST.k>
exception TypeNotFound of Type*Map<string, SurfAST.k>
exception VariableNotFound of string*Map<string,SurfAST.Type>
exception IncompatibleType of SurfAST.Type*Expr*Expr
exception NotSubtype of SurfAST.Type*SurfAST.Type
exception FullyTypedBehaviouralCast of SurfAST.Type
exception FieldAccessOnAny of SurfAST.Expr
exception MethodCallOnAny of SurfAST.Expr
exception IncompatibleMethodFound of mtd*SurfAST.Expr*string
exception FieldOrMethodNotFound of string*Expr*string
exception IncompatibleReturnValue of Type*SurfAST.Expr
exception EmptyMethodBody of string
exception MalformedMethod of md
exception MethodExistsException of string
exception FieldAccessOnNotThis of Expr

type mt =
| MDT of string * Type * Type

let findinclass<'a>(K:Map<string,SurfAST.k>)(recCls:string)(sel : k -> 'a list)(sub : 'a -> bool): 'a option =
    match K.TryFind recCls with
    | None ->  raise (ClassNotFound(recCls, new Map<string,k>([]) ))
    | Some(SurfAST.ClassDef(name, fds, mds, pos) as k) -> List.tryFind sub (sel k)

let findmethod(K:Map<string,SurfAST.k>)(recCls:string)(nm:string): (Type*Type) option =
    match findinclass K recCls
                  (function SurfAST.ClassDef(name, fds, mds, pos) -> mds)
                  (function SurfAST.MDef(name,var,argty,retty,body,posn) -> name.Equals(nm)) with
    | Some(SurfAST.MDef(name,var,argty,retty,body,posn)) -> Some((argty,retty))
    | None -> None

let findfield(K:Map<string,SurfAST.k>)(recCls:string)(nm:string): Type option =
    match findinclass K recCls
                  (function SurfAST.ClassDef(name, fds, mds, pos) -> fds)
                  (function SurfAST.FDef(name,ty,posn) -> name.Equals(nm)) with
    | Some(SurfAST.FDef(name,ty,posn)) -> Some(ty)
    | None -> None


let mtypes (ClassDef(name, fds, mds, posn)) : mt list = (List.map (function (MDef(name, _, t1, t2, _, _)) -> MDT(name, t1, t2)) mds)
let makek(ks:k list) : Map<string, k> = Map.ofList (List.map (fun k -> match k with (ClassDef(name, fds, mds, posn)) -> (name,k)) ks)

let rec subtype(K:Map<string,k>)(mu:Set<string * string>) : Type -> Type -> bool = fun x -> fun y -> 
    match (x,y) with
    |   (Class a, Class b) -> 
        match Set.contains (a,b) mu with
        |   true -> true
        |   false -> 
            match (K.TryFind a, K.TryFind b) with
            |   (Some (ClassDef(n1,fds1,mds1, posn) as k1) , Some (ClassDef(n2, fds2, mds2, pos) as k2)) -> 
                let mt1, mt2 = mtypes(k1), mtypes(k2)
                let nameof = (function MDT(n,_,_) -> n)
                let other = Map.ofList (List.groupBy nameof mt1)
                let collapse = function Some(l) -> l | None -> []
                let mup = Set.add (n1, n2) mu
                List.forall (fun mt2 -> List.exists (fun mt1 -> mtsub K mup mt1 mt2) (collapse (Map.tryFind (nameof mt2) other))) mt2
            |   _ -> false
    |   (t1, t2) -> t1 = t2
and mtsub(K:Map<string,k>)(mu:Set<string*string>) (a:mt) (b:mt): bool = 
    match (a,b) with
    |   (MDT(n1, t11, t12), MDT(n2, t21, t22)) -> n1 = n2 && (subtype K mu t21 t11) && (subtype K mu t12 t22)

let rec private ts_syntrans(K:Map<string,SurfAST.k>)(env:Map<string,Type>) : SurfAST.Expr -> AST.Expr * Type = function
|   SurfAST.That(_) -> raise (VariableNotFound("that", env))
|   SurfAST.This(pos) -> AST.SubCast(AST.Any, AST.This, pos), match env.TryFind "this" with Some(t) -> t | None -> raise (VariableNotFound("this", env))
|   SurfAST.Var(x, pos) -> AST.Var(x), match env.TryFind x with Some(t) -> t | None -> raise (VariableNotFound(x, env))
|   SurfAST.Call(receiver, method, argument, pos) -> 
    let epr,tr = ts_syntrans K env receiver
    match tr with
    |   Class(C) -> match findmethod K C method with
                    |   Some((t1,t2)) ->
                        let ep = ts_anatrans K env argument t1
                        AST.DynCall(AST.SubCast(AST.Any,epr,pos), method, AST.SubCast(AST.Any, ep, pos), pos), t2
                    |   _ -> raise (FieldOrMethodNotFound(method, receiver, ""))
    |   Any -> 
        let ep = ts_anatrans K env argument Any
        AST.DynCall(AST.SubCast(AST.Any, epr, pos), method, AST.SubCast(AST.Any, ep, pos), pos), Any
|   GetF(This(_) as th,field,posn) as g -> 
    let epr,tr = ts_syntrans K env th
    match tr with
    |   Class(C) -> match findfield K C field with
                    |   Some(t) -> AST.GetF(field), t
                    |   _ -> raise (FieldOrMethodNotFound(field, g, ""))
    |   Any -> (raise (FieldAccessOnAny(th)))
|   GetF(_, _, _) as gf -> raise (FieldAccessOnNotThis(gf))
|   SetF(This(_) as th, field, value, posn) as sf ->
    let epr,tr = ts_syntrans K env th
    match tr with
    |   Class(C) -> match findfield K C field with
                    |   Some(t) -> AST.SetF(field,ts_anatrans K env value t), t
                    |   _ -> raise (FieldOrMethodNotFound(field, sf, ""))
    |   Any -> (raise (FieldAccessOnAny(th)))
|   SetF(_,_,_,_) as sf -> raise (FieldAccessOnNotThis(sf))
|   NewExn(C, exprs, posn) ->
    let fdts = match K.TryFind C with
               |   None -> raise (ClassNotFound(C, K))
               |   Some(ClassDef(_,fds,_, posn)) -> List.map (function (FDef(name, tpe, posn)) -> tpe) fds
    let tns = List.map2 (ts_anatrans K env) exprs fdts
    AST.SubCast(AST.Any, AST.NewExn(C, tns), posn), Class(C)
and private ts_anatrans(K:Map<string,k>)(env:Map<string,Type>)(expr:Expr) : Type -> AST.Expr = function
|   Class(C) -> 
    let epr, tr = ts_syntrans K env expr
    match subtype K (Set.empty) tr (Class(C)) with
    |   true -> epr
    |   false -> match tr with
                 |   Class(D) -> raise (NotSubtype((Class C), (Class D)))
                 |   Any -> epr
|   Any -> 
    let epr, tr = ts_syntrans K env expr
    epr
let private ts_methtrans(K:Map<string,k>)(C:string) : md -> AST.md = function
|   MDef(name, var, t1, t2, body, posn) ->
    let env = (Map[ ("this", Class C) ; ("x", t1) ])
    match butlast (fun exp -> match ts_syntrans K env exp with (epr,tr) -> epr) 
                  (fun exp -> AST.SubCast(AST.Any, ts_anatrans K env exp t2, posn)) body with
    |   [] -> raise (EmptyMethodBody(name))
    |   body -> AST.MDef(name, var, AST.Any, AST.Any, body)
let private ts_classtrans(K:Map<string,k>) : k -> AST.k = function
|   ClassDef(name, fds, mds,posn) ->
    AST.ClassDef(name, List.map (function FDef(name,tpe,psn) -> AST.FDef(name, AST.Any)) fds, List.map (ts_methtrans K name) mds)
let ts_progtrans : prog -> AST.prog = function
|   Program(ks, exp) -> 
    let K = makek(ks)
    let expp, outt = ts_syntrans K (Map.empty) exp
    AST.Program(List.map (ts_classtrans K) ks, expp)

let convert_type : Type -> AST.Type = function
|   Any -> AST.Any
|   Class C -> AST.Class C

//transient
let rec trs_anatrans(K:Map<string,k>)(env:Map<string,Type>)(ex : Expr)(tgt : Type)(check:bool)(posn : FParsec.Position): AST.Expr =
    let exp,ty = trs_syntrans K env ex
    match subtype K (Set.empty) ty tgt with
    | true -> exp
    | false -> match check with
        | true -> AST.SubCast(convert_type tgt, exp, posn)
        | false -> exp
and trs_syntrans(K:Map<string,k>)(env:Map<string,Type>) : Expr -> AST.Expr * Type = function
|   That(_) -> raise (VariableNotFound("that", env))
|   This(_) -> AST.This, match env.TryFind "this" with Some(t) -> t | None -> raise (VariableNotFound("this", env))
|   Var(x,posn) -> match env.TryFind x with Some(t) -> AST.SubCast(convert_type t, AST.Var(x), posn), t | None -> raise (VariableNotFound(x, env))
|   SurfAST.Call(receiver, method, argument, pos) -> 
    let epr,tr = trs_syntrans K env receiver
    match tr with
    |   Class(C) -> match findmethod K C method with
                    |   Some((t1,t2)) ->
                        let ep = trs_anatrans K env argument t1 false pos
                        AST.SubCast(convert_type t2, AST.Call(epr, AST.Any, AST.Any, method, AST.SubCast(AST.Any, ep, pos)), pos), t2
                    |   _ -> raise (FieldOrMethodNotFound(method, receiver, ""))
    |   Any -> 
        let ep = trs_anatrans K env argument Any true pos
        AST.DynCall(AST.SubCast(AST.Any, epr, pos), method, AST.SubCast(AST.Any, ep, pos), pos), Any
|   GetF(This(_) as th,field,posn) as g -> 
    let epr,tr = trs_syntrans K env th
    match tr with
    |   Class(C) -> match findfield K C field with
                    |   Some(t) -> AST.SubCast(convert_type t, AST.GetF(field), posn), t
                    |   _ -> raise (FieldOrMethodNotFound(field, g, ""))
    |   Any -> (raise (FieldAccessOnAny(th)))
|   GetF(_, _, _) as gf -> raise (FieldAccessOnNotThis(gf))
|   SetF(This(_) as th, field, value, posn) as sf ->
    let epr,tr = trs_syntrans K env th
    match tr with
    |   Class(C) -> match findfield K C field with
                    |   Some(t) -> 
                        let epv = trs_anatrans K env value t false posn
                        AST.SetF(field,epv), t
                    |   _ -> raise (FieldOrMethodNotFound(field, sf, ""))
    |   Any -> (raise (FieldAccessOnAny(th)))
|   SetF(_,_,_,_) as sf -> raise (FieldAccessOnNotThis(sf))
|   NewExn(C, exprs, posn) ->
    let fdts = match K.TryFind C with
               |   None -> raise (ClassNotFound(C, K))
               |   Some(ClassDef(_,fds,_, posn)) -> List.map (function (FDef(name, tpe, posn)) -> tpe) fds
    let tns = List.map (fun ex -> trs_anatrans K env ex Any true posn) exprs
    AST.NewExn(C, tns), Class(C)

let private trs_methtrans(K:Map<string,k>)(C:string) : md -> AST.md = function
|   MDef(name, var, t1, t2, body, posn) ->
    let env = (Map[ ("this", Class C) ; (var, t1) ])
    match butlast (fun exp -> match trs_syntrans K env exp with (epr,tr) -> epr) 
                  (fun exp -> AST.SubCast(AST.Any, trs_anatrans K env exp t2 false posn, posn)) body with
    |   [] -> raise (EmptyMethodBody(name))
    |   body -> AST.MDef(name, var, AST.Any, AST.Any, AST.SubCast(convert_type t1, AST.Var(var), posn) :: body)

let private trs_classtrans(K:Map<string,k>) : k -> AST.k = function
|   ClassDef(name, fds, mds, posn) ->
    AST.ClassDef(name, List.map (function FDef(name,tpe, posn) -> AST.FDef(name, AST.Any)) fds, List.map (trs_methtrans K name) mds)

let trs_progtrans : prog -> AST.prog = function
|   Program(ks, exp) -> 
    let K = makek(ks)
    let expp, outt = trs_syntrans K (Map.empty) exp
    AST.Program(List.map (trs_classtrans K) ks, expp)

    
//behavioural
let rec beh_anatrans(K:Map<string,k>)(env:Map<string,Type>)(ex : Expr)(tgt : Type)(posn : FParsec.Position): AST.Expr =
    let exp,ty = beh_syntrans K env ex
    match subtype K (Set.empty) ty tgt with
    | true -> exp
    | false -> AST.BehCast(convert_type tgt, exp, posn)
and beh_syntrans(K:Map<string,k>)(env:Map<string,Type>) : Expr -> AST.Expr * Type = function
|   That(_) -> raise (VariableNotFound("that", env))
|   This(_) -> AST.This, match env.TryFind "this" with Some(t) -> t | None -> raise (VariableNotFound("this", env))
|   Var(x,posn) -> match env.TryFind x with Some(t) -> AST.Var(x), t | None -> raise (VariableNotFound(x, env))
|   SurfAST.Call(receiver, method, argument, pos) -> 
    let epr,tr = beh_syntrans K env receiver
    match tr with
    |   Class(C) -> match findmethod K C method with
                    |   Some((t1,t2)) ->
                        let ep = beh_anatrans K env argument t1 pos
                        AST.Call(epr, convert_type t1, convert_type t2, method, ep), t2
                    |   _ -> raise (FieldOrMethodNotFound(method, receiver, ""))
    |   Any -> 
        let ep = beh_anatrans K env argument Any pos
        AST.DynCall(epr, method, ep, pos), Any
|   GetF(This(_) as th,field,posn) as g -> 
    let epr,tr = beh_syntrans K env th
    match tr with
    |   Class(C) -> match findfield K C field with
                    |   Some(t) -> AST.GetF(field), t
                    |   _ -> raise (FieldOrMethodNotFound(field, g, ""))
    |   Any -> (raise (FieldAccessOnAny(th)))
|   GetF(_, _, _) as gf -> raise (FieldAccessOnNotThis(gf))
|   SetF(This(_) as th, field, value, posn) as sf ->
    let epr,tr = beh_syntrans K env th
    match tr with
    |   Class(C) -> match findfield K C field with
                    |   Some(t) -> 
                        let epv = beh_anatrans K env value t posn
                        AST.SetF(field,epv), t
                    |   _ -> raise (FieldOrMethodNotFound(field, sf, ""))
    |   Any -> (raise (FieldAccessOnAny(th)))
|   SetF(_,_,_,_) as sf -> raise (FieldAccessOnNotThis(sf))
|   NewExn(C, exprs, posn) ->
    let fdts = match K.TryFind C with
               |   None -> raise (ClassNotFound(C, K))
               |   Some(ClassDef(_,fds,_, posn)) -> List.map (function (FDef(name, tpe, posn)) -> tpe) fds
    let tns = List.map2 (fun ex t -> beh_anatrans K env ex t posn) exprs fdts
    AST.NewExn(C, tns), Class(C)

let private beh_methtrans(K:Map<string,k>)(C:string) : md -> AST.md = function
|   MDef(name, var, t1, t2, body, posn) ->
    let env = (Map[ ("this", Class C) ; (var, t1) ])
    match butlast (fun exp -> match beh_syntrans K env exp with (epr,tr) -> epr) 
                  (fun exp -> beh_anatrans K env exp t2 posn) body with
    |   [] -> raise (EmptyMethodBody(name))
    |   body -> AST.MDef(name, var, convert_type t1, convert_type t2, body)

let private beh_classtrans(K:Map<string,k>) : k -> AST.k = function
|   ClassDef(name, fds, mds, posn) ->
    AST.ClassDef(name, List.map (function FDef(name,tpe, posn) -> AST.FDef(name, convert_type tpe)) fds, List.map (beh_methtrans K name) mds)

let beh_progtrans : prog -> AST.prog = function
|   Program(ks, exp) -> 
    let K = makek(ks)
    let expp, outt = beh_syntrans K (Map.empty) exp
    AST.Program(List.map (beh_classtrans K) ks, expp)

    
//concrete
let rec con_anatrans(K:Map<string,k>)(env:Map<string,Type>)(ex : Expr)(tgt : Type)(posn : FParsec.Position): AST.Expr =
    let exp,ty = con_syntrans K env ex
    match subtype K (Set.empty) ty tgt with
    | true -> exp
    | false -> AST.SubCast(convert_type tgt, exp, posn)
and con_syntrans(K:Map<string,k>)(env:Map<string,Type>) : Expr -> AST.Expr * Type = function
|   That(_) -> raise (VariableNotFound("that", env))
|   This(_) -> AST.This, match env.TryFind "this" with Some(t) -> t | None -> raise (VariableNotFound("this", env))
|   Var(x,posn) -> match env.TryFind x with Some(t) -> AST.Var(x), t | None -> raise (VariableNotFound(x, env))
|   SurfAST.Call(receiver, method, argument, pos) -> 
    let epr,tr = con_syntrans K env receiver
    match tr with
    |   Class(C) -> match findmethod K C method with
                    |   Some((t1,t2)) ->
                        let ep = con_anatrans K env argument t1 pos
                        AST.Call(epr, convert_type t1, convert_type t2, method, ep), t2
                    |   _ -> raise (FieldOrMethodNotFound(method, receiver, ""))
    |   Any -> 
        let ep = con_anatrans K env argument Any pos
        AST.DynCall(epr, method, ep, pos), Any
|   GetF(This(_) as th,field,posn) as g -> 
    let epr,tr = beh_syntrans K env th
    match tr with
    |   Class(C) -> match findfield K C field with
                    |   Some(t) -> AST.GetF(field), t
                    |   _ -> raise (FieldOrMethodNotFound(field, g, ""))
    |   Any -> (raise (FieldAccessOnAny(th)))
|   GetF(_, _, _) as gf -> raise (FieldAccessOnNotThis(gf))
|   SetF(This(_) as th, field, value, posn) as sf ->
    let epr,tr = beh_syntrans K env th
    match tr with
    |   Class(C) -> match findfield K C field with
                    |   Some(t) -> 
                        let epv = con_anatrans K env value t posn
                        AST.SetF(field,epv), t
                    |   _ -> raise (FieldOrMethodNotFound(field, sf, ""))
    |   Any -> (raise (FieldAccessOnAny(th)))
|   SetF(_,_,_,_) as sf -> raise (FieldAccessOnNotThis(sf))
|   NewExn(C, exprs, posn) ->
    let fdts = match K.TryFind C with
               |   None -> raise (ClassNotFound(C, K))
               |   Some(ClassDef(_,fds,_, posn)) -> List.map (function (FDef(name, tpe, posn)) -> tpe) fds
    let tns = List.map2 (fun ex t -> con_anatrans K env ex t posn) exprs fdts
    AST.NewExn(C, tns), Class(C)

let private con_methtrans(K:Map<string,k>)(C:string) : md -> AST.md = function
|   MDef(name, var, t1, t2, body, posn) ->
    let env = (Map[ ("this", Class C) ; (var, t1) ])
    match butlast (fun exp -> match con_syntrans K env exp with (epr,tr) -> epr) 
                  (fun exp -> con_anatrans K env exp t2 posn) body with
    |   [] -> raise (EmptyMethodBody(name))
    |   body -> AST.MDef(name, var, convert_type t1, convert_type t2, body)

let private con_classtrans(K:Map<string,k>) : k -> AST.k = function
|   ClassDef(name, fds, mds, posn) ->
    AST.ClassDef(name, List.map (function FDef(name,tpe, posn) -> AST.FDef(name, convert_type tpe)) fds, List.map (con_methtrans K name) mds)

let con_progtrans : prog -> AST.prog = function
|   Program(ks, exp) -> 
    let K = makek(ks)
    let expp, outt = con_syntrans K (Map.empty) exp
    AST.Program(List.map (con_classtrans K) ks, expp)