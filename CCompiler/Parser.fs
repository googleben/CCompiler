﻿namespace CCompiler
open System
open System.Collections.Generic

module Parser =
    open Lexer

    exception NoSuchToken
    exception Unreachable
    
    [<RequireQualifiedAccess>]
    type AstType =
        | Char
        | Signed_Char
        | Unsigned_Char
        | Double
        | Long_Double
        | Float
        | Int
        | Signed
        | Signed_Int
        | Unsigned
        | Unsigned_Int
        | Long
        | Short
        | Void
        | Typedef of AstType
        | Struct of Tuple<AstType, string> list
        | Pointer of AstType
    
    type ParserState =
        {mutable Tokens: Token list; mutable Typedefs: Dictionary<string, AstType>}
        member this.isEnd = match this.Tokens with
                             | [] -> true
                             | _ -> false
        member this.peek = List.head this.Tokens
        member this.pop = match this.Tokens with
                           | head::[] -> this.Tokens <- []; head
                           | head::tail -> this.Tokens <- tail; head
                           | [] -> raise NoSuchToken
        member this.isTypedef =
            this.Typedefs.ContainsKey
        member this.getTypedef name =
            this.Typedefs.Item name
        
    [<RequireQualifiedAccess>]
    type AstConst =
        | Void
        | Int of int
        
    [<RequireQualifiedAccess>]
    type AstExpr =
        | Ident of string
        | Const of AstConst
        | Decl of type_:AstType * name:string
        | Unary of operator:TokenType * expr:AstExpr
        | Postfix of operator:TokenType * expr:AstExpr
        | Binary of left:AstExpr * operator:TokenType * right:AstExpr
        | Conditional of condition:AstExpr * left:AstExpr * right:AstExpr
        
    //[<RequireQualifiedAccess>]
    type AstStmt =
        | Return of AstExpr
        | Expr of AstExpr
        | Block of AstStmt list
        | Decl of AstType * string
        | StructDecl of string * AstType
        
    type AstFun(ret: AstType, name: string, parameters: AstExpr list, body: AstStmt) =
        member this.ret = ret
        member this.name = name
        member this.parameters = parameters
        member this.body = body
        override this.ToString() = ret.ToString()+" "+name.ToString()+"("+parameters.ToString()+") {\n"+body.ToString()+"\n}"
        
    exception UnexpectedToken of Token * string
        
    let expectType (state: ParserState): AstType =
        let t = state.pop
        match t.Type with
            | TokenType.CHAR -> AstType.Char
            | TokenType.DOUBLE -> AstType.Double
            | TokenType.FLOAT -> AstType.Float
            | TokenType.INT -> AstType.Int
            | TokenType.LONG -> AstType.Long
            | TokenType.SHORT -> AstType.Short
            | TokenType.VOID -> AstType.Void
            | TokenType.IDENT -> state.getTypedef t.Lexeme
            | _ -> raise (UnexpectedToken (t, "type"))
            
    let isType (state: ParserState): bool =
        let t = state.peek
        match t.Type with
            | TokenType.CHAR
            | TokenType.DOUBLE
            | TokenType.FLOAT
            | TokenType.INT
            | TokenType.LONG
            | TokenType.SHORT
            | TokenType.VOID -> true
            | TokenType.IDENT -> state.isTypedef t.Lexeme
            | _ -> false
            
    let expectIdent (state: ParserState): string =
        let t = state.pop
        match t.Type with
            | TokenType.IDENT -> (t.Lexeme)
            | _ -> raise (UnexpectedToken (t, "identifier"))
            
    let expectToken (state: ParserState) (tokenType: TokenType): Token =
        let t = state.pop
        match t.Type with
            | x when x = tokenType -> t
            | _ -> raise (UnexpectedToken (t, tokenType.ToString()))
    
    let rec parseStructInner (state: ParserState): Tuple<AstType, string> list =
        let mutable ans = []
        expectToken state TokenType.OPEN_CURLY |> ignore
        while not (state.peek.Type = TokenType.CLOSE_CURLY) do
            let t = parseDecl state
            match t with
                | AstStmt.Decl(typ,name) -> ans <- ans@[(typ,name)]
                | _ -> raise Unreachable
            expectToken state TokenType.SEMICOLON |> ignore
        expectToken state TokenType.CLOSE_CURLY |> ignore
        ans
    
    and parseTerminal (state: ParserState): AstExpr =
        match (state.peek).Type with
            | TokenType.INT_LITERAL -> AstExpr.Const (AstConst.Int (Int32.Parse (state.pop).Lexeme))
            | TokenType.IDENT -> AstExpr.Ident (expectIdent state)
            | _ -> raise (UnexpectedToken ((state.peek), "terminal"))
            
    and parseUnaryExpr (state: ParserState): AstExpr =
        match (state.peek).Type with
            | TokenType.MINUS | TokenType.TILDE | TokenType.PLUS | TokenType.BANG | TokenType.STAR
            | TokenType.PLUS_PLUS | TokenType.MINUS_MINUS | TokenType.AMPERSAND -> AstExpr.Unary ((state.pop.Type), (parseUnaryExpr state))
            | _ -> parseTerminal state
            
    and parseMult (state: ParserState): AstExpr =
        let mutable left = parseUnaryExpr state
        let mutable operator = state.peek.Type
        let mutable keepGoing = match operator with
                                 | TokenType.STAR | TokenType.SLASH | TokenType.PERCENT -> true
                                 | _ -> false
        while keepGoing do
            expectToken state operator |> ignore
            let right = parseUnaryExpr state
            left <- AstExpr.Binary (left, operator, right)
            operator <- state.peek.Type
            keepGoing <- match operator with
                                 | TokenType.STAR | TokenType.SLASH | TokenType.PERCENT -> true
                                 | _ -> false
        left
        
    and parseAdd (state: ParserState): AstExpr =
        let mutable left = parseMult state
        let mutable operator = state.peek.Type
        let mutable keepGoing = match operator with
                                 | TokenType.PLUS | TokenType.MINUS -> true
                                 | _ -> false
        while keepGoing do
            expectToken state operator |> ignore
            let right = parseMult state
            left <- AstExpr.Binary (left, operator, right)
            operator <- state.peek.Type
            keepGoing <- match operator with
                                 | TokenType.PLUS | TokenType.MINUS -> true
                                 | _ -> false
        left
        
    and parseShift (state: ParserState): AstExpr =
        let mutable left = parseAdd state
        let mutable operator = state.peek.Type
        let mutable keepGoing = match operator with
                                 | TokenType.GREATER_GREATER | TokenType.LESS_LESS -> true
                                 | _ -> false
        while keepGoing do
            expectToken state operator |> ignore
            let right = parseAdd state
            left <- AstExpr.Binary (left, operator, right)
            operator <- state.peek.Type
            keepGoing <- match operator with
                                 | TokenType.GREATER_GREATER | TokenType.LESS_LESS -> true
                                 | _ -> false
        left
        
    and parseRelational (state: ParserState): AstExpr =
        let mutable left = parseShift state
        let mutable operator = state.peek.Type
        let mutable keepGoing = match operator with
                                 | TokenType.GREATER | TokenType.GREATER_EQUALS | TokenType.LESS | TokenType.LESS_EQUALS -> true
                                 | _ -> false
        while keepGoing do
            expectToken state operator |> ignore
            let right = parseShift state
            left <- AstExpr.Binary (left, operator, right)
            operator <- state.peek.Type
            keepGoing <- match operator with
                                 | TokenType.GREATER | TokenType.GREATER_EQUALS | TokenType.LESS | TokenType.LESS_EQUALS -> true
                                 | _ -> false
        left
        
    and parseEquality (state: ParserState): AstExpr =
        let mutable left = parseRelational state
        let mutable operator = state.peek.Type
        let mutable keepGoing = match operator with
                                 | TokenType.EQUALS_EQUALS | TokenType.BANG_EQUALS -> true
                                 | _ -> false
        while keepGoing do
            expectToken state operator |> ignore
            let right = parseRelational state
            left <- AstExpr.Binary (left, operator, right)
            operator <- state.peek.Type
            keepGoing <- match operator with
                                 | TokenType.EQUALS_EQUALS | TokenType.BANG_EQUALS -> true
                                 | _ -> false
        left
        
    and parseBitwiseAnd (state: ParserState): AstExpr =
        let mutable left = parseEquality state
        let mutable operator = state.peek.Type
        let mutable keepGoing = match operator with
                                 | TokenType.AMPERSAND -> true
                                 | _ -> false
        while keepGoing do
            expectToken state operator |> ignore
            let right = parseEquality state
            left <- AstExpr.Binary (left, operator, right)
            operator <- state.peek.Type
            keepGoing <- match operator with
                                 | TokenType.AMPERSAND -> true
                                 | _ -> false
        left
        
    and parseBitwiseXor (state: ParserState): AstExpr =
        let mutable left = parseBitwiseAnd state
        let mutable operator = state.peek.Type
        let mutable keepGoing = match operator with
                                 | TokenType.CARET -> true
                                 | _ -> false
        while keepGoing do
            expectToken state operator |> ignore
            let right = parseBitwiseAnd state
            left <- AstExpr.Binary (left, operator, right)
            operator <- state.peek.Type
            keepGoing <- match operator with
                                 | TokenType.CARET -> true
                                 | _ -> false
        left
        
    and parseBitwiseOr (state: ParserState): AstExpr =
        let mutable left = parseBitwiseXor state
        let mutable operator = state.peek.Type
        let mutable keepGoing = match operator with
                                 | TokenType.PIPE -> true
                                 | _ -> false
        while keepGoing do
            expectToken state operator |> ignore
            let right = parseBitwiseXor state
            left <- AstExpr.Binary (left, operator, right)
            operator <- state.peek.Type
            keepGoing <- match operator with
                                 | TokenType.PIPE -> true
                                 | _ -> false
        left
    
    and parseLogicalAnd (state: ParserState): AstExpr =
        let mutable left = parseBitwiseOr state
        let mutable operator = state.peek.Type
        let mutable keepGoing = match operator with
                                 | TokenType.AMPERSAND_AMPERSAND -> true
                                 | _ -> false
        while keepGoing do
            expectToken state operator |> ignore
            let right = parseBitwiseOr state
            left <- AstExpr.Binary (left, operator, right)
            operator <- state.peek.Type
            keepGoing <- match operator with
                                 | TokenType.AMPERSAND_AMPERSAND -> true
                                 | _ -> false
        left
    
    and parseLogicalOr (state: ParserState): AstExpr =
        let mutable left = parseLogicalAnd state
        let mutable operator = state.peek.Type
        let mutable keepGoing = match operator with
                                 | TokenType.PIPE_PIPE -> true
                                 | _ -> false
        while keepGoing do
            expectToken state TokenType.PIPE_PIPE |> ignore
            let right = parseUnaryExpr state
            left <- AstExpr.Binary (left, operator, right)
            operator <- state.peek.Type
            keepGoing <- match operator with
                          | TokenType.PIPE_PIPE -> true
                          | _ -> false
        left
            
    and parseConditional (state: ParserState): AstExpr =
        let mutable cond = parseLogicalOr state
        match state.peek.Type with
            | TokenType.QUESTION ->
                expectToken state TokenType.QUESTION |> ignore
                let middle = parseExpr state
                expectToken state TokenType.COLON |> ignore
                cond <- AstExpr.Conditional (cond, middle, (parseConditional state))
            | _ -> ()
        cond
    and parseAssign (state: ParserState): AstExpr =
        let mutable left = parseConditional state
        match left with
            | AstExpr.Unary (_) -> match state.peek.Type with
                                    | TokenType.EQUALS | TokenType.PLUS_EQUALS | TokenType.MINUS_EQUALS | TokenType.STAR_EQUALS | TokenType.SLASH_EQUALS
                                    | TokenType.PERCENT_EQUALS | TokenType.AMPERSAND_EQUALS | TokenType.PIPE_EQUALS | TokenType.GREATER_GREATER_EQUALS
                                    | TokenType. LESS_LESS_EQUALS ->
                                        let op = state.pop
                                        left <- AstExpr.Binary (left, op.Type, (parseAssign state))
                                    | _ -> ()
            | _ -> ()
        left
    and parseExpr (state: ParserState): AstExpr =
        let mutable left = parseAssign state
        match state.peek.Type with
            | TokenType.COMMA -> expectToken state TokenType.COMMA |> ignore; left <- AstExpr.Binary (left, TokenType.COMMA, (parseExpr state))
            | _ -> ()
        left
        
    and parseReturn (state: ParserState): AstStmt =
        expectToken state TokenType.RETURN |> ignore
        if state.peek.Type=TokenType.SEMICOLON then
            AstStmt.Return (AstExpr.Const (AstConst.Int 0))
        else
            AstStmt.Return (parseExpr state)
        
    and parseStmt (state: ParserState): AstStmt =
        let ans = match (state.peek).Type with
                    | TokenType.RETURN -> parseReturn state
                    | _ when isType state -> parseDecl state
                    | _ -> AstStmt.Expr (parseExpr state)
        expectToken state TokenType.SEMICOLON |> ignore
        ans
    and parseDecl (state: ParserState): AstStmt =
        AstStmt.Decl ((expectType state), (state.pop.Lexeme))
    and parseStruct (state: ParserState): AstStmt =
        expectToken state TokenType.STRUCT |> ignore
        let name = (expectToken state TokenType.IDENT).Lexeme
        let contents = parseStructInner state
        AstStmt.StructDecl(name, AstType.Struct(contents))
        
    and parseBlock (state: ParserState): AstStmt =
        expectToken state TokenType.OPEN_CURLY |> ignore
        let mutable ans = []
        let mutable keepGoing = match (state.peek).Type with
                                 | TokenType.CLOSE_CURLY -> false
                                 | _ -> true
        while keepGoing do
            ans <- ans @ [parseStmt state]
            keepGoing <- match state.peek.Type with
                          | TokenType.CLOSE_CURLY -> false
                          | _ -> true
        expectToken state TokenType.CLOSE_CURLY |> ignore
        AstStmt.Block ans
        
    let rec parse (state: ParserState) (soFar: AstFun list): AstFun list =
        if state.isEnd then soFar else 
            let t = expectType state
            let name = expectIdent state
            expectToken state TokenType.OPEN_PAREN |> ignore
            let parameters = match state.peek.Type with
                              | TokenType.VOID -> state.pop |> ignore; []
                              | TokenType.CLOSE_PAREN -> []
                              | _ -> []
            expectToken state TokenType.CLOSE_PAREN |> ignore
            let body = parseBlock state
            parse state soFar @ [AstFun(t, name, parameters, body)]
        
        
    let parseEnt (tokens: Token list) : AstFun list =
        parse {Tokens=tokens; Typedefs=(new Dictionary<string, AstType>())} []