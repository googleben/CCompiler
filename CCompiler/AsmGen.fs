namespace CCompiler
open CCompiler.TACGen.TACGen
open Lexer
open System.Text

module AsmGen =
    open Parser
    open System
    
    type Frame = {Vars: Tuple<string, AstType, int> list; PrevFrame: Frame Option}
    type GenState =
        {mutable Output: StringBuilder; mutable Frame: Frame}
        member this.emitLabel (name: string) =
            this.Output.Append(name).Append(':').Append('\n') |> ignore
        member this.emit (str: string) =
            this.Output.AppendLine(str) |> ignore
        member this.emitInst (inst: string) (args: string list) =
            this.Output.Append('\t').Append(inst).Append(' ') |> ignore
            if args.Length > 0 then
                this.Output.Append (List.head args) |> ignore
                (List.fold (fun a b -> a+", "+b) "" (List.tail args) )
                    |> this.Output.AppendLine |> ignore
            else this.Output.Append("\n") |> ignore
            
    
    let genStart (state: GenState) =
        state.emit ".global _start"
        state.emitLabel "_start"
        state.emitInst "callq" ["main"]
        state.emitInst "movq" ["%rax"; "%rdi"]
        state.emitInst "movq" ["$60"; "%rax"]
        state.emitInst "syscall" []
        
    let genConst (state: GenState) (c: AstConst) =
        match c with
            | AstConst.Int i -> state.emitInst "movq" ["$"+string(i); "%rax"]
            | AstConst.Void -> ()
            | _ -> raise Unimplemented
        
    let rec genBinary (state: GenState) (_type: AstType) (left: AstExpr) (op: TokenType) (right: AstExpr) =
        genExpr state left
        state.emitInst "push" ["%rbx"]
        state.emitInst "movq" ["%rax"; "%rbx"]
        genExpr state right
        match op with
            | TokenType.LESS ->
                state.emitInst "cmpl" ["%eax"; "%ebx"]
                state.emitInst "setl" ["%al"]
            | TokenType.LESS_EQUALS ->
                state.emitInst "cmpl" ["%eax"; "%ebx"]
                state.emitInst "setle" ["%al"]
            | TokenType.GREATER ->
                state.emitInst "cmpl" ["%eax"; "%ebx"]
                state.emitInst "setg" ["%al"]
            | TokenType.GREATER_EQUALS ->
                state.emitInst "cmpl" ["%eax"; "%ebx"]
                state.emitInst "setge" ["%al"]
            | TokenType.PIPE ->
                state.emitInst "orl" ["%ebx"; "%eax"]
            | TokenType.AMPERSAND ->
                state.emitInst "andl" ["%ebx"; "%eax"]
            | TokenType.PIPE_PIPE ->
                state.emitInst "orl" ["%ebx"; "%eax"]
                state.emitInst "setne" ["%al"]
            | TokenType.AMPERSAND_AMPERSAND ->
                state.emitInst "setne" ["%dl"]
                state.emitInst "xorl" ["%eax"; "%eax"]
                state.emitInst "testl" ["%esi"; "%esi"]
                state.emitInst "setne" ["%al"]
                state.emitInst "andl" ["%edx"; "%eax"]
            | TokenType.PLUS ->
                state.emitInst "addl" ["%ebx"; "%eax"]
            | _ -> raise Unimplemented
        state.emitInst "pop" ["%rbx"]
        
    and genExpr (state: GenState) (expr: AstExpr) =
        match expr with
            | AstExpr.Const (_, c) -> genConst state c
            | AstExpr.Binary (type_, left, op, right) -> genBinary state type_ left op right
            | _ -> raise Unimplemented
        
    let rec genStmt (state: GenState) (stmt: AstStmt) =
        match stmt with
            | AstStmt.Block l -> List.fold (fun _ b -> b) false (List.map (genStmt state) l)
            | AstStmt.Return e ->
                genExpr state e
                state.emitInst "leave" []
                state.emitInst "ret" []
                true
            | _ -> raise Unimplemented
    
    let genFunc (state: GenState) (func: AstFun) =
        state.emit ".text"
        if func.name = "main" then genStart state
        state.emitLabel func.name
        state.emitInst "push" ["%rbp"]
        state.emitInst "movq" ["%rsp"; "%rbp"]
        if not (genStmt state func.body) then
            state.emitInst "leave" []
            state.emitInst "ret" []
        
        
    let genProg (funcs: AstFun list): string =
        let state = {Output=new StringBuilder(); Frame={Vars=[]; PrevFrame=None}}
        List.iter (genFunc state) funcs
        state.Output.ToString()