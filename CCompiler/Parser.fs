namespace CCompiler
open System

module Parser =
    open Lexer

    exception NoSuchToken
    
    type ParserState =
        {mutable Tokens: Token list}
        member this.isEnd = match this.Tokens with
                             | [] -> true
                             | _ -> false
        member this.peek = List.head this.Tokens
        member this.pop = match this.Tokens with
                           | head::[] -> this.Tokens <- []; head
                           | head::tail -> this.Tokens <- tail; head
                           | [] -> raise NoSuchToken
    
    [<RequireQualifiedAccess>]
    type AstConst =
        | Void
        | Int of int
        
    type Ident(name: string) =
        member this.name = name
        override this.ToString() = this.name
        
    [<RequireQualifiedAccess>]
    type AstType =
        | Void
        | Int
        | Typedef of Ident
        | Pointer of AstType
        
    [<RequireQualifiedAccess>]
    type AstExpr =
        | Ident of Ident
        | Const of AstConst
        | Decl of type_:AstType * name:Ident
        | Unary of operator:TokenType * expr:AstExpr
        | Binary of left:AstExpr * operator:TokenType * right:AstExpr
        
    //[<RequireQualifiedAccess>]
    type AstStmt =
        | Return of AstExpr
        | Expr of AstExpr
        | Block of AstStmt list
        
    type AstFun(ret: AstType, name: Ident, parameters: AstExpr list, body: AstStmt) =
        member this.ret = ret
        member this.name = name
        member this.parameters = parameters
        member this.body = body
        override this.ToString() = ret.ToString()+" "+name.ToString()+"("+parameters.ToString()+") {\n"+body.ToString()+"\n}"
        
    exception UnexpectedToken of Token * string
        
    let expectType (state: ParserState): AstType =
        let t = state.pop
        match t.Type with
            | TokenType.VOID -> AstType.Void
            | TokenType.INT -> AstType.Int
            | TokenType.IDENT -> AstType.Typedef(Ident(t.Lexeme))
            | _ -> raise (UnexpectedToken (t, "type"))
            
    let expectIdent (state: ParserState): Ident =
        let t = state.pop
        match t.Type with
            | TokenType.IDENT -> Ident(t.Lexeme)
            | _ -> raise (UnexpectedToken (t, "identifier"))
            
    let expectToken (state: ParserState) (tokenType: TokenType): Token =
        let t = state.pop
        match t.Type with
            | x when x = tokenType -> t
            | _ -> raise (UnexpectedToken (t, tokenType.ToString()))
    
    let parseTerminal (state: ParserState): AstExpr =
        match (state.peek).Type with
            | TokenType.INT_LITERAL -> AstExpr.Const (AstConst.Int (Int32.Parse (state.pop).Lexeme))
            | _ -> AstExpr.Const (AstConst.Void)
            
    let rec parseUnaryExpr (state: ParserState): AstExpr =
        match (state.peek).Type with
            | TokenType.MINUS | TokenType.TILDE | TokenType.PLUS | TokenType.BANG
            | TokenType.PLUS_PLUS | TokenType.MINUS_MINUS | TokenType.AMPERSAND -> AstExpr.Unary ((state.pop.Type), (parseUnaryExpr state))
            | _ -> parseTerminal state
    
    let parseLogicalOr (state: ParserState): AstExpr =
        let mutable left = parseUnaryExpr state
        let mutable operator = state.peek.Type
        let mutable keepGoing = match operator with
                                 | TokenType.PIPE_PIPE -> true
                                 | _ -> false
        while keepGoing do
            expectToken state TokenType.PIPE_PIPE |> ignore
            let right = parseUnaryExpr state
            left <- AstExpr.Binary (left, operator, right)
            keepGoing <- match operator with
                          | TokenType.PIPE_PIPE -> true
                          | _ -> false
        left
            
    
    let parseExpr (state: ParserState): AstExpr =
        parseLogicalOr state
        
    let parseReturn (state: ParserState): AstStmt =
        expectToken state TokenType.RETURN |> ignore
        AstStmt.Return (parseExpr state)
        
    let parseStmt (state: ParserState): AstStmt =
        let ans = match (state.peek).Type with
                    | TokenType.RETURN -> parseReturn state
                    | _ -> AstStmt.Expr (parseExpr state)
        expectToken state TokenType.SEMICOLON |> ignore
        ans
            
    let parseBlock (state: ParserState): AstStmt =
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
        parse {Tokens=tokens} []