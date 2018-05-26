module Executor
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open System.IO
open System.Collections.Generic
open System
open System.Reflection

exception CSharpCompilerError of string

let execute(s:string) =
    let an = Path.GetRandomFileName()
    let refs : MetadataReference list = [
        MetadataReference.CreateFromFile(typeof<obj>.Assembly.Location) ;
        MetadataReference.CreateFromFile(typeof<IEnumerable<int>>.Assembly.Location) ;
        MetadataReference.CreateFromFile(typeof<System.Runtime.CompilerServices.DynamicAttribute>.Assembly.Location) ;
        MetadataReference.CreateFromFile(typeof<Microsoft.CSharp.RuntimeBinder.Binder>.Assembly.Location) ;
        MetadataReference.CreateFromFile(typeof<Kafka.Runtime>.Assembly.Location) ]
    let compilation = CSharpCompilation.Create(
                        an,
                        [ CSharpSyntaxTree.ParseText(s) ],
                        refs,
                        CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary))
    use ms = new MemoryStream()
    let result = compilation.Emit(ms)
    File.WriteAllBytes("KafkaGen.dll", ms.ToArray());
    match result.Success with
    | false -> result.Diagnostics 
            //|> Seq.filter (fun res -> res.IsWarningAsError || res.Severity = DiagnosticSeverity.Error) 
            |> Seq.map Console.WriteLine 
            |> (fun x -> raise (CSharpCompilerError "exception"))
    | true -> do ms.Seek(int64(0), SeekOrigin.Begin) |> ignore
              let assembly = Assembly.Load(ms.ToArray())
              let mainClass = assembly.GetType("Kafka.Program")
              mainClass.GetMethod("Main").Invoke(null, Seq.toArray [ Array.empty<string> ])