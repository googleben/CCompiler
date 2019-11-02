namespace CCompiler
open System.Linq.Expressions
open System.IO

module Main =
    
    let p x =
        for f in x do
            printfn "%O" (f.ToString())
    
    [<EntryPoint>]
    let main argv =
        argv |> ignore
        let lexed = Lexer.lexEnt ((File.OpenRead "in.c") |> Lexer.fileToString)
        Lexer.printTokens lexed
        let parsed = Parser.parseEnt lexed
        p parsed
        printfn "%s" (AsmGen.genProg parsed)
        0 // return an integer exit code
        