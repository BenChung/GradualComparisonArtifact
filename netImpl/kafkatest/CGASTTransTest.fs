module CGASTTransTest
open NUnit.Framework
open FsUnit
open AST
open CGAST

[<TestFixture>]
type CGASTTests() =
    [<Test>]
    member x.TestEmpty() =
        (match CGAST.findps([])([]) with (a,b) -> a = [] && b = []) |> should equal true
    [<Test>]
    member x.TestMd() =
        (match CGAST.findps([])([MDef("m","x",Any,Any, [Var "x"])]) with (a,b) -> a = [] && b = [CMDef("m","x",Any,Any, [Var "x"])]) |> should equal true
     