module CodeGen
open AST
open CGAST
open SubIL
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.Formatting

let toCsType(t:Type) : string = 
    match t with
    | Any -> "dynamic"
    | Class c -> "I" + c
let cnt = ref 0
let gen() : string = 
    let ocnt = !cnt
    cnt := !cnt + 1
    string ocnt
let rec genExpr(ex:Expr) : string =
    match ex with
    | Var n -> n
    | This -> "this"
    | That -> "this.that"
    | NewExn(c, exprs) -> "new " + c + "(" + (String.concat "," (List.map genExpr exprs)) + ")"
    | GetF(f) -> "this." + f
    | SetF(f, v) -> "this." + f + " = " + (genExpr v)
    | Call(rece, tp, t, m, arg) -> (genExpr rece) + "." + m + "(" + (genExpr arg) + ")"
    | DynCall(rece, m, arg, posn) -> (genExpr rece) + "." + m + "(" + (genExpr arg) + ")"
    | SubCast(t, expr, posn) -> 
        let locinfo = "new LocationInfo(\"" + posn.StreamName + "\", " + string posn.Line + ", " + string posn.Index + ", " + string posn.Column + ")"
        "Runtime.rtCast<" + (toCsType t) + ">(" + (genExpr expr) + ", " + locinfo + ")"
    | BehCast(t, expr, posn) -> 
                          let locinfo = "new LocationInfo(\"" + posn.StreamName + "\", " + string posn.Line + ", " + string posn.Index + ", " + string posn.Column + ")"
                          match t with
                          | Class C -> "Runtime.tyWrapper<" + toCsType(t) + ">(" + locinfo + ", " + genExpr(expr) + ")"
                          | Any -> "Runtime.dyWrapper(" + locinfo + ", " + genExpr(expr) + ")"

and genExprTl(ex:Expr) : string = 
    match ex with 
    | NewExn(_,_) -> genExpr(ex)
    | SetF(_,_) -> genExpr(ex)
    | _ -> "var xv" + gen() + " = " + genExpr(ex)
    
let genBody(ex:Expr list) : string = 
    Seq.fold (fun acc x -> acc + x + ";\n") "" 
        (List.mapi (fun i expr -> if i = (List.length ex) - 1 then "return " + (genExpr expr) else (genExprTl expr))
                ex)

let genDef(md:cgmd) : string =
    match md with
    | CMDef(name, var, vtype, rtype, body) -> "public " + toCsType(rtype) + " " + name + "(" + toCsType(vtype) + " " + var + ")" + "{\n" + genBody(body) + "}\n" 


let genGet(getter:cggd option) : string =
    match getter with
    | Some(CGDef(body)) -> "get {\n" + genBody(body) + "}\n"
    | None -> ""

let genSet(setter: cgsd option) : string =
    match setter with
    | Some(CSDef(var, body)) -> "set {\n" + genBody(List.map (subst(var, Var "value")) body) + "}\n"
    | None -> ""

let genFd(fd:cgfd) : string =
    match fd with
    | CFDef(name, tpe) -> "public " + toCsType(tpe) + " " + name + " {get; set;}"
    | CPDef(name, tpe, get, set) -> "public " + toCsType(tpe) + " " + name + "{\n" + genGet(get) + genSet(set) + "}"

let genConstructor(name:string, fds: cgfd list) : string =
    let cfds = (Seq.choose(fun (fd : cgfd) -> match fd with
                                              | CFDef(name,tpe) -> Some(name,tpe)
                                              | _ -> None) fds)
    "public " + name + "(" + (String.concat(", ")(Seq.map (fun (name, tpe) -> toCsType(tpe) + " " + name) cfds)) + ") { \n" +
                             (String.concat "\n" (Seq.map (fun (name, tpe) -> "this." + name + " = " + name + ";") cfds)) + "\n}"
                             
let genIfd: cgfd -> string = function
|   CFDef(name, tpe) -> toCsType(tpe) + " " + name + " {get; set;}"
|   CPDef(name, tpe, get, set) -> toCsType(tpe) + " " + name + "{\n" + match get with Some(_) -> "get;" | None -> "" + match set with Some(_) -> "set;" | None -> "" + "}"

let genImd : cgmd -> string = function
|   CMDef(name, x, t1, t2, body) -> toCsType(t2) + " " + name + "(" + toCsType(t1) + " " + x + ");"

let genInterface(k:subk, stOf : string list) : string =
    match k with
    | SubClassDef(name, fds, mds, _) -> 
        let prefix = if stOf.Length > 1 then // self reference
                        sprintf "[SubtypeOf(%s)]\n" (String.concat (",") (List.map (sprintf "typeof(I%s)") (List.filter (fun s -> not (s = name)) stOf)))
                     else
                        ""
        prefix + "public interface I" + name + "{\n"+ (String.concat "\n" (List.append (List.map genIfd fds) (List.map genImd mds))) + "\n}"  
    
let explicitImpls : subim -> string = function
|   CIPDef(from, name, tpe, get, set) -> sprintf "%s %s.%s { %s %s }" (toCsType(tpe)) (toCsType(Class from)) name 
                                                 (if get then sprintf "get => this.%s;" name else "") 
                                                 (if set then sprintf "set => this.%s = value;" name else "")
|   CIMDef(from, name, t1, t2) -> sprintf "%s %s.%s(%s x) => this.%s(x);" (toCsType(t2)) (toCsType(Class from)) name (toCsType(t1)) name

exception ThisShouldntHappenException of string
let genClass(env:Map<string, string list>)(k:subk) : string =
    match k with
    | SubClassDef(name, fds, mds, impls) -> 
        let interfaces = match env.TryFind name with
                         |  Some(n) -> n
                         |  None -> raise (ThisShouldntHappenException "wtf")
        let ifacestring = String.concat ", " (List.map (fun tpe -> toCsType(Class tpe)) interfaces)
        "public class " + name + " : " + ifacestring + " {\n" + (String.concat "\n" (genConstructor(name, fds) :: (List.append (List.map explicitImpls impls) (List.append (List.map genFd fds) (List.map genDef mds))))) + "\n}"

let genProg(p:subp, pretty:bool, standalone:bool) : string =
    match p with
    | SubProgram(ks, env, expr) -> 
        let preamble = if standalone then "using Kafka;\nnamespace Kafka {\n" else ""
        let generated = preamble + (String.concat "\n" 
                                                        (List.append (List.map (fun (SubClassDef(name, _, _, _) as k) -> (k, env.Item name)) ks |> List.map genInterface) 
                                                                     (List.map (genClass env) ks))) + "\n" + 
                                                                        "public class Program { \n public static dynamic Main(string[] args) { \n return " + genExpr(expr) + ";\n}\n}" + if standalone then "\n}" else ""
        if pretty then
            use ws = new AdhocWorkspace()
            let ast = CSharpSyntaxTree.ParseText(generated)
            Formatter.Format(ast.GetRoot(), ws).ToFullString()
        else
            generated