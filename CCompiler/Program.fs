namespace CCompiler
open System.Linq.Expressions
open System.IO

module Main = 
    [<EntryPoint>]
    let main argv =
        argv |> ignore
        Lexer.lexEnt ((File.OpenRead "in.c") |> Lexer.fileToString)
        0 // return an integer exit code
        