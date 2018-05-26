module TypecheckerTests
open NUnit.Framework
open FsUnit
open AST
open Typechecker


[<TestFixture>]
type InMtypesTests() =
    let CK1 = Map[ ("C",ClassDef("C",[],[])) ]
    let CK2 = Map[ ("C",ClassDef("C",[FDef("x",Any)],[])) ]
    let CK3 = Map[ ("C",ClassDef("C",[],[MDef("m","x",Any,Any,[])])) ] 

    [<Test>]
    member x.Inmtypes1() =
        Typechecker.inmtypes(G("x"))("C") CK1 |> should equal None
    [<Test>]
    member x.Inmtypes2() =
        Typechecker.inmtypes(S("x"))("C") CK1 |> should equal None
    [<Test>]
    member x.Inmtypes3() =
        Typechecker.inmtypes(MD("x",Any,Any))("C") CK1 |> should equal None

    [<Test>]
    member x.Inmtypes4() =
        Typechecker.inmtypes(G("x"))("C") CK2 |> should equal (Some(GT("x", Any)))
    [<Test>]
    member x.Inmtypes5() =
        Typechecker.inmtypes(S("x"))("C") CK2 |> should equal (Some(ST("x",Any)))
    [<Test>]
    member x.Inmtypes6() =
        Typechecker.inmtypes(MD("x",Any,Any))("C") CK2 |> should equal None

    [<Test>]
    member x.Inmtypes7() =
        Typechecker.inmtypes(G("m"))("C") CK3 |> should equal None
    [<Test>]
    member x.Inmtypes8() =
        Typechecker.inmtypes(S("m"))("C") CK3 |> should equal None
    [<Test>]
    member x.Inmtypes9() =
        Typechecker.inmtypes(MD("m",Any,Any))("C") CK3 |> should equal (Some(MDT("m",Any,Any)))
  
[<TestFixture>]
type MtypesTests() =
    [<Test>]
    member x.mtypes1() =
        Typechecker.mtypes(ClassDef("C",[],[])) |> should equal []
    [<Test>]
    member x.mtypes2() =
        Typechecker.mtypes(ClassDef("C",[FDef("x", Any)],[])) |> should equal [GT("x",Any) ; ST("x", Any)]
    [<Test>]
    member x.mtypes5() =
        Typechecker.mtypes(ClassDef("C",[],[MDef("x","x",Any,Any,[])])) |> should equal [MDT("x",Any,Any)]
    [<Test>]
    member x.mtypes6() =
        Typechecker.mtypes(ClassDef("C",[FDef("x", Any) ; FDef("y", Any)],[MDef("m","x",Any,Any,[])])) 
            |> should equal [GT("x",Any) ; ST("x", Any) ; GT("y",Any) ; ST("y", Any) ; MDT("m",Any,Any)]
   
[<TestFixture>]
type SubtypeTests() =
    let CK1 = Map[ ("C",ClassDef("C",[],[])) ;
                   ("D",ClassDef("D",[FDef("x",Any)],[])) ;
                   ("E",ClassDef("E",[FDef("x",Any)],[MDef("m","x",Any,Any,[])])) ;
                   ("F",ClassDef("F",[],[MDef("m","x",Any,Any,[])]))]
    [<Test>]
    member x.st1() =
        Typechecker.subtype CK1 (Set.empty) (Class "C") (Class "C") |> should be True
    [<Test>]
    member x.st2() =
        Typechecker.subtype CK1 (Set.empty) (Class "C") (Class "D") |> should be False
    [<Test>]
    member x.st3() =
        Typechecker.subtype CK1 (Set.empty) (Class "D") (Class "C") |> should be True
    [<Test>]
    member x.st4() =
        Typechecker.subtype CK1 (Set.empty) (Class "E") (Class "C") |> should be True
    [<Test>]
    member x.st5() =
        Typechecker.subtype CK1 (Set.empty) (Class "C") (Class "E") |> should be False
    [<Test>]
    member x.st6() =
        Typechecker.subtype CK1 (Set.empty) (Class "E") (Class "F") |> should be True
    [<Test>]
    member x.st7() =
        Typechecker.subtype CK1 (Set.empty) (Class "F") (Class "E") |> should be True