namespace CCompiler
open System
open System.Collections.Generic

module Parser =
    open Lexer

    exception NoSuchToken
    exception Unreachable
    
    exception UndefinedVar
    
 
    
    [<RequireQualifiedAccess>]
    type AstType =
        | SByte | UByte | SShort | UShort | SInt | UInt | SLong | ULong
        | Float | Double
        | Void
        | Typedef of AstType
        | Struct of Tuple<AstType, string> list
        | Pointer of AstType
        | Undef
    
    exception TypeMismatch of Tuple<AstType, AstType>
    
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
        | Float of float32
        
    [<RequireQualifiedAccess>]
    type AstExpr =
        | Ident of type_:AstType * string
        | Const of type_:AstType * value:AstConst
        | Unary of type_:AstType * operator:TokenType * expr:AstExpr
        | Postfix of type_:AstType * operator:TokenType * expr:AstExpr
        | Binary of type_:AstType * left:AstExpr * operator:TokenType * right:AstExpr
        | Conditional of type_:AstType * condition:AstExpr * left:AstExpr * right:AstExpr
        | Cast of type_:AstType * value:AstExpr
        
        
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
        let mutable ty =
            match t.Type with
                | TokenType.CHAR -> AstType.UByte
                | TokenType.DOUBLE -> AstType.Double
                | TokenType.FLOAT -> AstType.Float
                | TokenType.INT -> AstType.SInt
                | TokenType.LONG -> AstType.SLong
                | TokenType.SHORT -> AstType.SShort
                | TokenType.VOID -> AstType.Void
                | TokenType.IDENT -> state.getTypedef t.Lexeme
                | _ -> raise (UnexpectedToken (t, "type"))
        while state.peek.Type = TokenType.STAR do
            ty <- AstType.Pointer ty
            ignore state.pop
        ty
            
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
            
    let getType (expr: AstExpr): AstType =
        match expr with
            | AstExpr.Binary (t, _, _, _) | AstExpr.Conditional (t, _, _, _) | AstExpr.Const (t, _)
            | AstExpr.Ident (t, _) | AstExpr.Postfix (t, _, _) | AstExpr.Unary (t, _, _) | AstExpr.Cast(t, _) -> t
            
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
            | TokenType.INT_LITERAL -> AstExpr.Const (AstType.SInt, AstConst.Int (Int32.Parse (state.pop).Lexeme))
            | TokenType.FLOAT_LITERAL -> AstExpr.Const (AstType.Float, AstConst.Float (Single.Parse (state.pop).Lexeme))
            | TokenType.IDENT -> AstExpr.Ident (AstType.Undef, expectIdent state)
            | _ -> raise (UnexpectedToken ((state.peek), "terminal"))
            
    and parseCastOrGroup (state: ParserState): AstExpr =
        match (state.peek).Type with
            | TokenType.OPEN_PAREN ->
                expectToken state TokenType.OPEN_PAREN |> ignore
                if isType state then
                    let tmp = expectType state
                    expectToken state TokenType.CLOSE_PAREN |> ignore
                    AstExpr.Cast(tmp, parseExpr state)
                else
                    let tmp = parseExpr state
                    expectToken state TokenType.CLOSE_PAREN |> ignore
                    tmp
            | _ -> parseTerminal state
                
            
    and parseUnaryExpr (state: ParserState): AstExpr =
        match (state.peek).Type with
            | TokenType.MINUS | TokenType.TILDE | TokenType.PLUS | TokenType.BANG | TokenType.STAR
            | TokenType.PLUS_PLUS | TokenType.MINUS_MINUS | TokenType.AMPERSAND -> AstExpr.Unary (AstType.Undef, (state.pop.Type), (parseUnaryExpr state))
            | _ -> parseCastOrGroup state
            
    and parseMult (state: ParserState): AstExpr =
        let mutable left = parseUnaryExpr state
        let mutable operator = state.peek.Type
        let mutable keepGoing = match operator with
                                 | TokenType.STAR | TokenType.SLASH | TokenType.PERCENT -> true
                                 | _ -> false
        while keepGoing do
            expectToken state operator |> ignore
            let right = parseUnaryExpr state
            left <- AstExpr.Binary (AstType.Undef, left, operator, right)
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
            left <- AstExpr.Binary (AstType.Undef, left, operator, right)
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
            left <- AstExpr.Binary (AstType.Undef, left, operator, right)
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
            left <- AstExpr.Binary (AstType.Undef, left, operator, right)
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
            left <- AstExpr.Binary (AstType.Undef, left, operator, right)
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
            left <- AstExpr.Binary (AstType.Undef, left, operator, right)
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
            left <- AstExpr.Binary (AstType.Undef, left, operator, right)
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
            left <- AstExpr.Binary (AstType.Undef, left, operator, right)
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
            left <- AstExpr.Binary (AstType.Undef, left, operator, right)
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
            left <- AstExpr.Binary (AstType.Undef, left, operator, right)
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
                cond <- AstExpr.Conditional (AstType.Undef, cond, middle, (parseConditional state))
            | _ -> ()
        cond
    and parseAssign (state: ParserState): AstExpr =
        let mutable left = parseConditional state
        match left with
            | AstExpr.Ident (_) | AstExpr.Unary (_) ->
                match state.peek.Type with
                        | TokenType.EQUALS | TokenType.PLUS_EQUALS | TokenType.MINUS_EQUALS | TokenType.STAR_EQUALS | TokenType.SLASH_EQUALS
                        | TokenType.PERCENT_EQUALS | TokenType.AMPERSAND_EQUALS | TokenType.PIPE_EQUALS | TokenType.GREATER_GREATER_EQUALS
                        | TokenType. LESS_LESS_EQUALS ->
                            let op = state.pop
                            left <- AstExpr.Binary (AstType.Undef, left, op.Type, (parseAssign state))
                        | _ -> ()
            | _ -> ()
        left
    and parseExpr (state: ParserState): AstExpr =
        let mutable left = parseAssign state
        match state.peek.Type with
            | TokenType.COMMA -> expectToken state TokenType.COMMA |> ignore; left <- AstExpr.Binary (AstType.Undef, left, TokenType.COMMA, (parseExpr state))
            | _ -> ()
        left
        
    and parseReturn (state: ParserState): AstStmt =
        expectToken state TokenType.RETURN |> ignore
        if state.peek.Type=TokenType.SEMICOLON then
            AstStmt.Return (AstExpr.Const (AstType.SInt, AstConst.Int 0))
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
        
    type AstFrame =
        {prev: AstFrame option; vars: Map<string, AstType>}
        member this.getVar (name: string): AstType =
            match this.vars.TryFind name with
                | None -> match this.prev with
                            | Some prev -> prev.getVar name
                            | None -> raise UndefinedVar
                | Some t -> t
        member this.addVar (name: string) (t: AstType): AstFrame =
            {prev = this.prev; vars = this.vars.Add (name, t)}
        member this.newFrame: AstFrame =
            {prev = Some this; vars = Map.empty}
        
    let rec typifyE (frame: AstFrame) (expr: AstExpr): AstExpr =
        match expr with
            | AstExpr.Binary (_, l, op, r) ->
                let l' = typifyE frame l
                let r' = typifyE frame r
                if not ((getType l') = (getType r')) then raise (TypeMismatch (getType l', getType r'))
                AstExpr.Binary (getType l', l', op, r')
            | AstExpr.Conditional (_, cond, l, r) ->
                let l' = typifyE frame l
                let r' = typifyE frame r
                if not ((getType l') = (getType r')) then raise (TypeMismatch (getType l', getType r'))
                AstExpr.Conditional (getType l', cond, l', r')
            | AstExpr.Ident (_, n) ->
                AstExpr.Ident (frame.getVar n, n)
            | AstExpr.Postfix (_, op, e) ->
                let e' = typifyE frame e
                AstExpr.Postfix (getType e', op, e)
            | AstExpr.Unary (_, op, e) ->
                let e' = typifyE frame e
                AstExpr.Unary (getType e', op, e)
            | AstExpr.Const _ -> expr
            | AstExpr.Cast (t, e) -> AstExpr.Cast (t, typifyE frame e)
        
    let rec typifyS (frame: AstFrame) (stmt: AstStmt): AstFrame * AstStmt =
        match stmt with
            | AstStmt.Decl (t, n) -> (frame.addVar n t, stmt)
            | AstStmt.Expr e -> (frame, AstStmt.Expr (typifyE frame e))
            | AstStmt.Return e -> (frame, AstStmt.Return (typifyE frame e))
            | AstStmt.Block l ->
                let frame2 = frame.newFrame
                (frame, AstStmt.Block (fst (List.fold
                                        (fun fstate fstmt ->
                                            let flist, fframe = fstate
                                            let fframe, fstmt = typifyS fframe fstmt
                                            (flist @ [fstmt], fframe)
                                        ) ([], frame2) l)))
            | AstStmt.StructDecl _ -> (frame, stmt)
        
    let typify (f: AstFun): AstFun =
        let frame = {prev = None; vars = Map.empty}
        AstFun (f.ret, f.name, f.parameters, snd (typifyS frame f.body))
        
    let parseEnt (tokens: Token list) : AstFun list =
        parse {Tokens=tokens; Typedefs=(Dictionary<string, AstType>())} []
        |> List.map typify
