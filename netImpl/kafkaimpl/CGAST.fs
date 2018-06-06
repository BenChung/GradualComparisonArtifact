module CGAST
open AST

type cgmd = 
| CMDef of string * string * Type * Type * Expr list
 override x.ToString() = sprintf "%A" x

type cgsd =
| CSDef of string * Expr list
 override x.ToString() = sprintf "%A" x

type cggd =
| CGDef of Expr list
 override x.ToString() = sprintf "%A" x

type cgfd =
| CFDef of string * Type
| CPDef of string * Type * cggd option * cgsd option
 override x.ToString() = sprintf "%A" x

type cgk =
| CClassDef of string * cgfd list * cgmd list
 override x.ToString() = sprintf "%A" x

type Cprog =
| CProgram of cgk list * Map<string, string list> * Expr
 override x.ToString() = sprintf "%A" x 

let mapUpdate<'k, 'v when 'k : comparison>(m : Map<'k,'v>)(k:'k)(v:'v)(res : 'v -> 'v) : Map<'k,'v> =
    if Map.containsKey k m then Map.add k (res (Map.find k m)) m else Map.add k v m
    
exception FieldExistsError of string

let findps(fds: fd list) (mds:md list) : (cgfd list) * (cgmd list) =
    let fdsInter = Map.ofList(List.map (fun fd -> match fd with (FDef(name, tpe)) -> name, CFDef(name, tpe)) fds : (string * cgfd) list)
    let updateGet = fun (nt : Type) (getter : cggd) -> fun existing -> 
        match existing with
        | (CPDef(name,tpe,None,oset)) -> if nt = tpe then (CPDef(name,tpe,Some getter,oset)) else raise (FieldExistsError "Inconsistent field typing")
        | _ -> raise (FieldExistsError "A getter is duplicated... somewhere in your program") 
    let updateSet = fun (nt : Type) (setter : cgsd) -> fun existing -> 
        match existing with
        | (CPDef(name,tpe,oget,None)) -> if nt = tpe then (CPDef(name,tpe,oget,Some setter)) else raise (FieldExistsError "Inconsistent field typing")
        | _ -> raise (FieldExistsError "A setter is duplicated... somewhere in your program") 
    let fdsUp : Map<string, cgfd> = List.fold (fun map el -> 
                                 match el with
                                 | (MDef(_, _, _, _, _)) -> map) fdsInter mds
    let newmds = List.map (fun (MDef(n,v,t1,t2,e)) -> (CMDef(n,v,t1,t2,e))) mds
    (List.map (fun (k,v) -> v) (Map.toList fdsUp), newmds)

let transk(c:k):cgk =
    match c with
    | ClassDef(name, fds, mds) -> 
        let newfds, newmds = findps(fds)(mds)
        CClassDef(name,newfds, newmds)

let findSubtypes(lk : k list) =
    let K = Map.ofList (List.map (fun k -> match k with (ClassDef(name, fds, mds)) -> (name,k)) lk)
    Map.ofList (List.map (fun (ClassDef(c1, _, _)) -> (c1, (List.collect (fun (ClassDef(c2, _, _)) -> if Typechecker.subtype K (Set.empty) (Class c1) (Class c2) then [c2] else []) lk))) lk)
    


let transp(p:prog) : Cprog =
    match p with
    | Program(ks, se) -> CProgram(List.map transk ks, findSubtypes(ks), se)