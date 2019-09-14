namespace CCompiler

module Parser =
    open Lexer

    exception NoSuchToken
    
    type ParserState =
        {mutable Tokens: Token list}
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
        
    [<RequireQualifiedAccess>]
    type AstType =
        | Void
        | Int
        | Typedef of Ident
        
    [<RequireQualifiedAccess>]
    type AstExpr =
        | Ident of Ident
        | Const of AstConst
        | Decl of AstType * Ident
        
    //[<RequireQualifiedAccess>]
    type AstStmt =
        | Return of AstExpr
        | Block of AstStmt list
        
    type AstFun(ret: AstType, name: Ident, parameters: AstExpr list, body: AstStmt) =
        member this.ret = ret
        member this.name = name
        member this.parameters = parameters
        member this.body = body
        
    exception UnexpectedToken of Token * string
        
    let expectType (state: ParserState): AstType =
        let t = List.head state.Tokens
        state.Tokens <- state.Tokens
        match t.Type with
            | TokenType.VOID -> AstType.Void
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
            | tokenType -> t
            | _ -> raise (UnexpectedToken (t, tokenType.ToString()))
        
    let parseBlock (state: ParserState): AstStmt =
        expectToken state TokenType.OPEN_CURLY
        let mutable ans = []
        let keepGoing = match (state.peek).Type with
                         | TokenType.CLOSE_CURLY -> false
                         | _ -> true
        while keepGoing do
            ans <- ans @ [parseStmt state]
        expectToken state TokenType.CLOSE_CURLY
        AstStmt.Block ans
            
        
    let rec parse (state: ParserState): AstFun list =
        let t = expectType state
        let name = expectIdent state
        expectToken state TokenType.OPEN_PAREN
        let params = match state.peek.Type with
                      | TokenType.VOID | TokenType.CLOSE_PAREN -> []
                      | _ -> []
        let body = parseBlock state
        
        
    let ParseEnt (tokens: Token list) : AstFun list =
        parse {Tokens=tokens}