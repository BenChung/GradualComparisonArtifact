module program
open System
open AST
open System.IO

    type CommandLineOptions = {
        gradual: Option<SurfAST.prog -> prog>;
        litmusfile: Option<string>;
        }
[<EntryPoint>]

let main argv = 
    (*Just need to set the semantics and the file that will be parsed*)
  
    let rec parseCommandLineRec args optionsSoFar = 
        match args with 
        // empty array means we're done.
        | [||] -> match optionsSoFar with 
                  | {gradual = Some _; litmusfile = Some _} -> optionsSoFar
                  | _ -> eprintfn "No or insufficient arguments passed.\nFormat: [kafka] [opt|tra|beh|con] [path to file]."
                         raise (Exception())
        // match verbose flag
        | args when args.[0] = "beh" -> 
            let newOptionsSoFar = { optionsSoFar with gradual=Some Translations.beh_progtrans }
            parseCommandLineRec args.[1..] newOptionsSoFar 
        | args when args.[0] = "opt" -> 
            let newOptionsSoFar = { optionsSoFar with gradual=Some Translations.ts_progtrans }
            parseCommandLineRec args.[1..] newOptionsSoFar 
        | args when args.[0] = "tra" -> 
            let newOptionsSoFar = { optionsSoFar with gradual=Some Translations.trs_progtrans }
            parseCommandLineRec args.[1..] newOptionsSoFar 
        | args when args.[0] = "con" -> 
            let newOptionsSoFar = { optionsSoFar with gradual=Some Translations.con_progtrans }
            parseCommandLineRec args.[1..] newOptionsSoFar       
        | _ ->             
            eprintfn "Test file: '%s'." args.[0]
            let newOptionsSoFar = { optionsSoFar with litmusfile = Some args.[0]}
            parseCommandLineRec args.[1..] newOptionsSoFar 

    let parseCommandLine args = 
        let defaultOptions = {
            gradual = None;
            litmusfile = None;
        }
        parseCommandLineRec args defaultOptions

    let res = parseCommandLine argv
    let litmus = File.ReadAllText(res.litmusfile.Value)
    let res1 = SurfAST.parse litmus
    let tsv = res.gradual.Value res1.Value
    let _ = Typechecker.wfprog tsv
    let trans = CGAST.transp(tsv)
    let subtypeRels = SubIL.addSubtypeImpls(tsv)(trans)
    let outp = CodeGen.genProg(subtypeRels, true, true)
    let evaluated = Executor.execute(outp)
    
    printfn "%A" evaluated

    0 // return an integer exit code
