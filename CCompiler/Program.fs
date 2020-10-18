namespace CCompiler
open System
open System.IO
open CCompiler.Lexer
open CCompiler.TACGen.TACGen

module Main =
    
    let p x =
        for f in x do
            printfn "%O" (f.ToString())
            
    let printTac (tac: TAC list) =
        let pa (a: Address) =
            match a with
                | Address.Constant (t, c) -> "("+(c.ToString())+": "+(t.ToString())+")"
                | Address.Temp (t, n) -> "(temp "+(n.ToString())+": "+(t.ToString())+")"
                | Address.Name (t, n) -> "("+n+": "+(t.ToString())+")"
        let ts = getTokenTypeAsStr
        let mutable exprN = 0
        let maxDigits= int32 (Math.Log10 (float tac.Length)) + 1
        let labelPrint = Printf.TextWriterFormat<int->unit>("%0"+(maxDigits.ToString())+"d ")
        for expr in tac do
            match expr with
                | TAC.NewScope _ | TAC.CloseScope -> ()
                | _ ->
                        printf labelPrint exprN
                        exprN <- exprN + 1
            match expr with
                | TAC.Binary (dest, a, o, b) ->
                    printfn "%s = %s %s %s" (pa dest) (pa a) (ts o) (pa b)
                | TAC.Unary (dest, o, v) ->
                    printfn "%s = %s%s" (pa dest) (ts o) (pa v)
                | TAC.Const (dest, v) ->
                    printfn "%s = %s" (pa dest) (v.ToString())
                | TAC.Copy (dest, src) ->
                    printfn "%s = %s" (pa dest) (pa src)
                | TAC.CopyToDeref (destPtr, src) ->
                    printfn "*%s = %s" (pa destPtr) (pa src)
                | TAC.GetDeref (dest, srcPtr) ->
                    printfn "%s = *%s" (pa dest) (pa srcPtr)
                | TAC.Jump (dest) ->
                    printfn "jump %d" dest
                | TAC.CondJump (cond, desired, dest) ->
                    printfn "jump %d if %s = %b" dest (pa cond) desired
                | TAC.Param (v) ->
                    printfn "param %s" (pa v)
                | TAC.FunCall (n) ->
                    printfn "call %s" n
                | TAC.CopyFunCall (dest, n) ->
                    printfn "%s = call %s" (pa dest) n
                | TAC.Return (v) ->
                    printfn "return %s" (pa v)
                | TAC.NewScope (names) ->
                    printfn "Scope start %O" names
                | TAC.CloseScope ->
                    printfn "Scope end"
    
    [<EntryPoint>]
    let main argv =
        argv |> ignore
        let lexed = Lexer.lexEnt ((File.OpenRead "in.c") |> Lexer.fileToString)
        Lexer.printTokens lexed
        let parsed = Parser.parseEnt lexed
        p parsed
        let tac = TACGen.TACGen.tacifyFuns parsed
        for p in tac.functions do
            printfn "%s: %d" p.Key p.Value
        printTac tac.code
        //printfn "%s" (AsmGen.genProg parsed)
        0 // return an integer exit code
        