module SurfAST
open FParsec

type Type =
| Any
| Class of string
 override x.ToString() = sprintf "%A" x

type Expr =
| Var of string * Position
| This of Position
| That of Position
| NewExn of string * (Expr list) * Position
| GetF of Expr * string * Position
| SetF of Expr * string * Expr * Position
| Call of Expr * string * Expr * Position
 override x.ToString() = sprintf "%A" x

type md = 
| MDef of string * string * Type * Type * Expr list * Position
 override x.ToString() = sprintf "%A" x

type fd =
| FDef of string * Type * Position
 override x.ToString() = sprintf "%A" x

type k =
| ClassDef of string * fd list * md list * Position
 override x.ToString() = sprintf "%A" x

type prog =
| Program of k list * Expr
 override x.ToString() = sprintf "%A" x

let parse (prog:string) = 
    let (<!>) (p: Parser<_,_>) label : Parser<_,_> =
        fun stream ->
            printfn "%A: Entering %s" stream.Position label
            let reply = p stream
            printfn "%A: Leaving %s (%A)" stream.Position label reply.Status
            reply
    let ws = spaces <|> (skipMany skipNewline)
    let str_ws s = pstring s .>> ws
    let id = identifier (IdentifierOptions(isAsciiIdStart = isAsciiLetter, isAsciiIdContinue = fun c -> isAsciiLetter c || isDigit c))
    let tpe = (pstring "any" |>> fun x -> Any) <|> (id |>> fun x -> Class x)
    let term, termImpl = createParserForwardedToRef()
    let expr = (getPosition .>>. pstring "this" |>> fun (pos,x) -> This pos) <|> 
               (getPosition .>>. pstring "that" |>> fun (pos,x) -> That pos) <|> 
               (pipe3 (getPosition) 
                     (pstring "new" >>. ws >>. id .>> ws .>> pstring "(")
                     ((sepBy (ws >>. term) (ws >>. pstring ",")) .>> pstring ")")
                     (fun pos className args -> NewExn(className, args, pos))) <|>
               ((pstring "(" >>. ws >>. term .>> ws .>> pstring ")") |>> (fun e -> e)) <|> 
               (getPosition .>>. id |>> fun (pos, x) -> Var(x,pos))
    let callExpr = (attempt (pstring "." >>. (attempt (pipe3 (getPosition) (id .>> ws .>> pstring "=" .>> ws) (term .>> ws) (fun pos name arg -> fun exp -> SetF(exp, name, arg, pos))) <|>
                                              attempt (pipe3 (getPosition) (id .>> ws) (pstring "(" >>. ws >>. term .>> ws .>> pstring ")") (fun pos name arg -> fun exp -> Call(exp,name,arg,pos))) <|>
                                              attempt ( getPosition .>>. (id) |>> (fun (posn, name) -> fun exp -> GetF(exp, name, posn))) )))
    do termImpl := (attempt (pipe2 expr (many callExpr) (fun e l -> List.fold (fun acc f -> f acc) e l))) <|> expr
    let term = termImpl.Value
    let body = (sepBy1 term (attempt (ws >>. pstring ";" >>. ws)))
    let fd = pipe3 (getPosition) (id .>> ws .>> pstring ":" .>> ws) tpe (fun pos name tpe -> FDef(name, tpe, pos))
    let md = pipe5 (getPosition .>>. id .>> pstring "(") 
                   (ws >>. id) 
                   (ws .>> pstring ":" >>. ws >>. tpe .>> pstring ")" .>> ws .>> pstring ":" .>> ws) 
                   (tpe .>> ws .>> pstring "{" .>> ws) 
                   ( body .>> ws .>> pstring "}")
                   (fun (pos, name) var tp t body -> MDef(name, var, tp, t, body, pos)) 
    let clazz = pipe4 (getPosition) (ws >>. str_ws "class" >>. ws >>. id .>> ws .>> pstring "{") (sepEndBy (attempt (ws >>. fd)) ws) ((sepEndBy (ws >>. (attempt md)) ws) .>> pstring "}") (fun pos name fds mds -> ClassDef(name, fds, mds, pos))
    let program = pipe2 ((sepEndBy clazz ws) .>> ws) (term .>> ws .>> eof) (fun c t -> Program(c,t))
    match run program prog with
    | Success(result, _, _) -> Some(result)
    | Failure(errorMsg, _, _) -> printfn "Failure %s" errorMsg; None