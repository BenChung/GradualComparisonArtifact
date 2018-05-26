module program
open System
open Parser
open AST
open CGAST
open CodeGen
open System
open System.IO

    type CommandLineOptions = {
        gradual: SurfAST.prog -> prog;
        litmusfile: string;
        }

(**
Limtus tests in Kafka for each gradual semantics.

Optional Semantics:

*****************Litmus test one*****************

@"
class A {
    m(x:any):any { this } }
class I {
    n(x:any):any { this } }
class T {
    s(x:any):any { this } 
    t(x:any):any {this@s : any -> any (x) }}

(new T())@t(new A())"


*****************Litmus test two*****************

@"
class A {
    m(x:any):any { this } }
class Q {
    n(x:any):any { this } }
class I {
    m(x:any):any { this } }
class T {
    s(x:any):any { this } 
    t(x:any):any { this@s : any -> any (x) }}

(new T())@t(new A())"


*****************Litmus test three*****************

@"
class C {
    a(x:any):any { this } }
class D {
    b(x:any):any { this } }
class E {
    a(x:any):any { this } }
class F {
    m(x:any):any { x } 
    n(x:any):any { this@m : any -> any (x) }}

(new F())@n(new C())@a(new C())"


***************************************************
***************************************************
Transient Semantics:

*****************Litmus test one*****************

@"
class A {
    m(x:any):any { <A> x; <any> this } }
class I {
    n(x:any):any { <I> x; <any> this } }
class T {
    s(x:any):any { <I> x; <any> this } 
    t(x:any):any { <any> x; <any><T>(this.s : any -> any ( <any><any> x)) }}

(<any>new T())@t(<any>new A())"


*****************Litmus test two*****************

@"
class A {
    m(x:any):any { <A> x; <any> this } }
class Q {
    n(x:any):any { <Q> x; <any> this } }
class I {
    m(x:any):any { <Q> x; <any> this } }
class T {
    s(x:any):any { <I> x; <any> this } 
    t(x:any):any { <any> x; <any><T>(this.s : any -> any ( <any><any> x)) }}

(<any>new T())@t(<any>new A())"

*****************Litmus test three*****************

@"
class C {
    a(x:any):any { <C> x; <any> this } }
class D {
    b(x:any):any { <D> x; <any> this } }
class E {
    a(x:any):any { <D> x; <any> this } }
class F {
    m(x:any):any { <E> x; <any> x } 
    n(x:any):any { <any> x; <any>(<E>(this.m : any -> any ( <any>(<any> x)))) }}

(<any>new F())@n(<any>new C())@a(<any>new C())"


***************************************************
***************************************************
Behavioral Semantics:

*****************Litmus test one*****************
@"
class A {
    m(x:A):A { this } }
class I {
    n(x:I):I { this } }
class T {
    s(x:I):T { this } 
    t(x:any):any { <|any|>(this.s : I -> T ( <|I|> x)) }}

(<any>new T())@t(<|any|>new A())"


*****************Litmus test two*****************
@"
class A {
    m(x:A):A { this } }
class Q {
    n(x:Q):Q { this } }
class I {
    m(x:Q):I { this } }
class T {
    s(x:I):T { this } 
    t(x:any):any { <|any|>(this.s : I -> T ( <|I|> x)) }}

(<any>new T())@t(<|any|>new A())"


*****************Litmus test three*****************
@"
class C {
    a(x:C):C { this } }
class D {
    b(x:D):D { this } }
class E {
    a(x:D):D { this } }
class F {
    m(x:E):E { x } 
    n(x:any):any { <|any|>(this.m : E -> E ( <|E|> x)) }}

(<any>new F())@n(<|any|>new C())@a(<|any|>new C())"


***************************************************
***************************************************
Concrete Semantics:

*****************Litmus test one*****************
@"
class A {
    m(x:A):A { this } }
class I {
    n(x:I):I { this } }
class T {
    s(x:I):T { this } 
    t(x:any):any { <any>(this.s : I -> T ( <I> x)) }}

(<any>new T())@t(<any>new A())"


*****************Litmus test two*****************
@"
class A {
    m(x:A):A { this } }
class Q {
    n(x:Q):Q { this } }
class I {
    m(x:Q):I { this } }
class T {
    s(x:I):T { this } 
    t(x:any):any { <any>(this.s : I -> T ( <I> x)) }}

(<any>new T())@t(<any>new A())"


*****************Litmus test three*****************
@"
class C {
    a(x:C):C { this } }
class D {
    b(x:D):D { this } }
class E {
    a(x:D):D { this } }
class F {
    m(x:E):E { x } 
    n(x:any):any { <any>(this.m : E -> E ( <E> x)) }}

(<any>new F())@n(<any>new C())@a(<any>new C())"

*)

let litmus1 = @"
class A {
    m(x:A) : A { this } }
class I {
    n(x:I) : I { this } }
class T {
    s(x : I) : T { this } 
    t(x : any) : any { this.s(x) } }

new T().t(new A())"

let litmus2 = @"
class A {
    m(x:A):A {this}}
class Q {
    n(x:Q):Q {this}}
class I {
    m(x:Q):I {this}}
class T {
    s(x:I):T {this}
    t(x:any):any {this.s(x)}}
new T().t(new A())
"

let litmus3 = @"
class C {
    a(x:C):C {x}}
class D {
    b(x:D):D {x}}
class E {
    a(x:D):D {x}}
class F {
    m(x:E):E {x}
    n(x:any):any {this.m(x)}}

new F().n(new C()).a(new C())
"

[<EntryPoint>]

let main argv = 
    (*Just need to set the semantics and the file that will be parsed*)
  
    let rec parseCommandLineRec args optionsSoFar = 
        match args with 
        // empty array means we're done.
        | [||] -> eprintfn "No option for gradual semantics or tests file is passed. The default is optional semantics for litmus test1"
                  optionsSoFar
        // match verbose flag
        | args when args.[0] = "beh" -> 
            let newOptionsSoFar = { optionsSoFar with gradual=Translations.beh_progtrans }
            parseCommandLineRec args.[1..] newOptionsSoFar 
        | args when args.[0] = "opt" -> 
            let newOptionsSoFar = { optionsSoFar with gradual=Translations.ts_progtrans }
            parseCommandLineRec args.[1..] newOptionsSoFar 
        | args when args.[0] = "tra" -> 
            let newOptionsSoFar = { optionsSoFar with gradual=Translations.trs_progtrans }
            parseCommandLineRec args.[1..] newOptionsSoFar 
        | args when args.[0] = "con" -> 
            let newOptionsSoFar = { optionsSoFar with gradual=Translations.con_progtrans }
            parseCommandLineRec args.[1..] newOptionsSoFar       
        | _ ->             
            eprintfn "Test file: '%s'." args.[0]
            let newOptionsSoFar = { optionsSoFar with litmusfile = args.[0]}
            parseCommandLineRec args.[1..] newOptionsSoFar 

    let parseCommandLine args = 
        let defaultOptions = {
            gradual = Translations.ts_progtrans;
            litmusfile = "litmus1.txt";
        }
        parseCommandLineRec args defaultOptions

    let res = parseCommandLine argv
    let litmus = File.ReadAllText(res.litmusfile)
    let res1 = SurfAST.parse litmus
    let tsv = res.gradual res1.Value
    let _ = Typechecker.wfprog tsv
    let trans = CGAST.transp(tsv)
    let subtypeRels = SubIL.addSubtypeImpls(tsv)(trans)
    let outp = CodeGen.genProg(subtypeRels, true, true)
    let evaluated = Executor.execute(outp)
    
    printfn "%A" evaluated

    0 // return an integer exit code
