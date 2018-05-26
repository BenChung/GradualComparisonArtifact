module CompilerTests

open NUnit.Framework
open AST
open FsUnit
[<TestFixture>]
type CompilerTests() =
    static member Succeeding = [| "class A {\n}\nnew A()" |]
    
    [<Test>]
    member x.mtypes12() =
        Typechecker.mtypes(ClassDef("C",[],[])) |> should equal []
    [<TestCaseSource("Succeeding")>]
    member x.execute(program : string) =
        let res = Parser.parse program
        let _ = Typechecker.wfprog res.Value
        let trans = CGAST.transp(res.Value)
        let subtypeRels = SubIL.addSubtypeImpls(res.Value)(trans)
        let outp = CodeGen.genProg(subtypeRels, true, true)
        let evaluated = Executor.execute(outp)
        Assert.NotNull(evaluated)

    