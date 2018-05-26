module SubIL
open AST
open CGAST

type subim =
| CIPDef of string * string * Type * bool * bool
| CIMDef of string * string * Type * Type

type subk =
| SubClassDef of string * cgfd list * cgmd list * subim list

type subp = 
| SubProgram of subk list * Map<string, string list> * Expr

let reqImpls (CClassDef(name, fields, methods)) = 
    List.append(List.map (function (CFDef(iname, tpe)) -> CIPDef(name, iname, tpe, true, true) 
                                  | CPDef(iname, tpe, g, s) -> CIPDef(name, iname, tpe, g.IsSome, s.IsSome)) fields)
               (List.map (function (CMDef(iname, x, t1, t2, body)) -> CIMDef(name, iname, t1, t2)) methods)


let findSubtypeImpls(k : k list, lk : cgk list) =
    let K = Map.ofList (List.map (fun k -> match k with (ClassDef(name, fds, mds)) -> (name,k)) k)
    let rel = Map.ofList (List.zip k lk)
    List.map (fun (CClassDef(c1, fds, mds) as k1) -> 
        SubClassDef(c1, fds, mds, (List.collect (fun (ClassDef(c2, _, _) as k2) -> 
        if (not (c1 = c2)) && (Typechecker.subtype K (Set.empty) (Class c1) (Class c2)) then 
            reqImpls (rel.Item k2) 
        else 
            []) k))) lk

let addSubtypeImpls(Program(ksi, _)) = function (CProgram(ks, subtypes, main)) -> SubProgram(findSubtypeImpls(ksi, ks), subtypes, main)