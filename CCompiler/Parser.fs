namespace CCompiler
open System
open System.Collections.Generic

module Parser =
    open Lexer

    exception NoSuchToken
    exception Unreachable
    
    exception UndefinedVar
    exception UndefinedFunction
    exception DerefNonPointer
    
 
    
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
    
    type ParserStateTypes =
        {mutable Typedefs: Dictionary<string, AstType>; mutable Structs: Dictionary<string, AstType>; Prev: ParserStateTypes Option}
        static member empty = {Typedefs = Dictionary(); Structs = Dictionary(); Prev = None}
        
        member this.isTypedef n =
            if this.Typedefs.ContainsKey n then
                true
            elif this.Prev.IsSome then
                this.Prev.Value.isTypedef n
            else
                false
        member this.getTypedef n =
            if this.Typedefs.ContainsKey n then
                this.Typedefs.Item n
            else
                this.Prev.Value.getTypedef n
        member this.isStruct n =
            if this.Structs.ContainsKey n then
                true
            elif this.Prev.IsSome then
                this.Prev.Value.isStruct n
            else
                false
        member this.getStruct n =
            if this.Structs.ContainsKey n then
                this.Structs.Item n
            else
                this.Prev.Value.getStruct n
        
    type ParserState =
        {mutable Tokens: Token list; mutable Types: ParserStateTypes}
        member this.isEnd = match this.Tokens with
                             | [] -> true
                             | _ -> false
        member this.peek = List.head this.Tokens
        member this.peek2 = List.head (List.tail this.Tokens)
        member this.pop = match this.Tokens with
                           | head::[] -> this.Tokens <- []; head
                           | head::tail -> this.Tokens <- tail; head
                           | [] -> raise NoSuchToken
        member this.isTypedef =
            this.Types.isTypedef
        member this.getTypedef =
            this.Types.getTypedef
        member this.addTypedef name typ =
            this.Types.Typedefs.Add(name, typ)
        member this.isStruct =
            this.Types.isStruct
        member this.getStruct =
            this.Types.getStruct
        member this.addStruct name typ =
            this.Types.Structs.Add(name, typ)
            
        member this.newFrame =
            this.Types <- {ParserStateTypes.empty with Prev = Some this.Types}
        member this.popFrame =
            this.Types <- this.Types.Prev.Value
        
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
        | FunCall of type_:AstType * name:string * args:AstExpr list
        
        
    //[<RequireQualifiedAccess>]
    type AstStmt =
        | Return of AstExpr
        | Expr of AstExpr
        | Block of AstStmt list
        | Decls of AstType * (string * AstExpr Option) list
        | StructDecl of string * AstType
        | Nop
        
    type AstFun(ret: AstType, name: string, parameters: (AstType*string) list, body: AstStmt) =
        member this.ret = ret
        member this.name = name
        member this.parameters = parameters
        member this.body = body
        override this.ToString() = ret.ToString()+" "+name.ToString()+"("+parameters.ToString()+") {\n"+body.ToString()+"\n}"
        
    exception UnexpectedToken of Token * string
        
    let rec expectType (state: ParserState): AstType =
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
                | TokenType.STRUCT ->
                    if state.peek.Type = TokenType.IDENT then
                        //named struct
                        let n = (expectToken state TokenType.IDENT).Lexeme
                        if state.peek.Type = TokenType.OPEN_CURLY then
                            //we have a definition, e.g. struct Name {int a;}
                            let ans = AstType.Struct (parseStructInner state)
                            state.addStruct n ans
                            ans
                        else
                            //we have no definition, so the struct type must already be defined
                            state.getStruct n
                    else
                        //anonymous struct e.g. struct Name {int a;}
                        AstType.Struct (parseStructInner state)
                | TokenType.IDENT when state.isTypedef t.Lexeme ->
                    state.getTypedef t.Lexeme
                | _ -> raise (UnexpectedToken (t, "type"))
        while state.peek.Type = TokenType.STAR do
            ty <- AstType.Pointer ty
            ignore state.pop
        ty
            
    and isType (state: ParserState): bool =
        let t = state.peek
        match t.Type with
            | TokenType.CHAR
            | TokenType.DOUBLE
            | TokenType.FLOAT
            | TokenType.INT
            | TokenType.LONG
            | TokenType.SHORT
            | TokenType.STRUCT
            | TokenType.VOID -> true
            | TokenType.IDENT -> state.isTypedef t.Lexeme
            | _ -> false
            
    and getType (expr: AstExpr): AstType =
        match expr with
            | AstExpr.Binary (t, _, _, _) | AstExpr.Conditional (t, _, _, _) | AstExpr.Const (t, _)
            | AstExpr.Ident (t, _) | AstExpr.Postfix (t, _, _) | AstExpr.Unary (t, _, _) | AstExpr.Cast(t, _)
            | AstExpr.FunCall (t, _, _) -> t
            
    and expectIdent (state: ParserState): string =
        let t = state.pop
        match t.Type with
            | TokenType.IDENT -> (t.Lexeme)
            | _ -> raise (UnexpectedToken (t, "identifier"))
    
    and expectToken (state: ParserState) (tokenType: TokenType): Token =
        let t = state.pop
        match t.Type with
            | x when x = tokenType -> t
            | _ -> raise (UnexpectedToken (t, tokenType.ToString()))
    
    and parseStructInner (state: ParserState): Tuple<AstType, string> list =
        let mutable ans = []
        expectToken state TokenType.OPEN_CURLY |> ignore
        while not (state.peek.Type = TokenType.CLOSE_CURLY) do
            let t = parseDecl state
            match t with
                | AstStmt.Decls(typ, [(name,None)]) -> ans <- ans@[(typ,name)]
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
            
    and parseFunCall (state: ParserState): AstExpr =
        if (state.peek).Type = TokenType.IDENT && (state.peek2).Type = TokenType.OPEN_PAREN then
            let fname = state.pop.Lexeme
            expectToken state TokenType.OPEN_PAREN |> ignore
            let mutable args = []
            if not ((state.peek).Type = TokenType.CLOSE_PAREN) then
                args <- [parseAssign state]
                while (state.peek).Type = TokenType.COMMA do
                    expectToken state TokenType.COMMA |> ignore
                    args <- args @ [parseAssign state]
            expectToken state TokenType.CLOSE_PAREN |> ignore
            AstExpr.FunCall (AstType.Undef, fname, args)
        else parseTerminal state
            
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
            | _ -> parseFunCall state
                
            
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
                    | TokenType.TYPEDEF ->
                        parseTypedef state
                        AstStmt.Nop
                    | _ when isType state -> parseDecl state
                    | _ -> AstStmt.Expr (parseExpr state)
        expectToken state TokenType.SEMICOLON |> ignore
        ans
    and parseDeclGivenType (state: ParserState) (t: AstType): AstStmt =
        //helper function to parse <name> = <value> where value may not be a comma expression
        let parseDeclInner _ =
            let name = (expectToken state TokenType.IDENT).Lexeme
            if state.peek.Type = TokenType.EQUALS then
                expectToken state TokenType.EQUALS |> ignore
                (name, Some (parseAssign state))
            else
                (name, None)
        
        let mutable ans = [parseDeclInner ()]
        while state.peek.Type = TokenType.COMMA do
            expectToken state TokenType.COMMA |> ignore
            ans <- ans @ [parseDeclInner ()]
        AstStmt.Decls (t, ans)
    and parseDecl (state: ParserState): AstStmt =
        let t = expectType state
        parseDeclGivenType state t
    and parseTypedef (state: ParserState) =
        expectToken state TokenType.TYPEDEF |> ignore
        let t = expectType state
        let n = (expectToken state TokenType.IDENT).Lexeme
        state.addTypedef n t
    and parseStruct (state: ParserState): AstStmt =
        expectToken state TokenType.STRUCT |> ignore
        let name = (expectToken state TokenType.IDENT).Lexeme
        let contents = parseStructInner state
        AstStmt.StructDecl(name, AstType.Struct(contents))
        
    and parseBlock (state: ParserState): AstStmt =
        expectToken state TokenType.OPEN_CURLY |> ignore
        state.newFrame
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
        state.popFrame
        AstStmt.Block ans
        
    let rec parse (state: ParserState) (soFar: AstFun list * AstStmt list): AstFun list * AstStmt list =
        if state.isEnd then
            soFar
        else
            match state.peek.Type with
                | TokenType.TYPEDEF ->
                    parseTypedef state
                    expectToken state TokenType.SEMICOLON |> ignore
                    parse state soFar
                | _ when isType state ->
                    let t = expectType state
                    if state.peek.Type = TokenType.SEMICOLON then
                        //struct declaration
                        expectToken state TokenType.SEMICOLON |> ignore
                        parse state soFar
                    elif state.peek.Type = TokenType.IDENT && state.peek2.Type = TokenType.OPEN_PAREN then
                        //function
                        let name = expectIdent state
                        expectToken state TokenType.OPEN_PAREN |> ignore
                        let parameters = match state.peek.Type with
                                          | TokenType.VOID -> state.pop |> ignore; []
                                          | TokenType.CLOSE_PAREN -> []
                                          | _ ->
                                              let mutable ans = [(expectType state, expectIdent state)]
                                              while not (state.peek.Type = TokenType.CLOSE_PAREN) do
                                                expectToken state TokenType.COMMA |> ignore
                                                ans <- ans @ [(expectType state, expectIdent state)]
                                              ans
                        expectToken state TokenType.CLOSE_PAREN |> ignore
                        let body = parseBlock state
                        let sf1, sf2 = soFar
                        parse state (sf1 @ [AstFun(t, name, parameters, body)], sf2)
                    else
                        //function
                        let funs, stmts = soFar
                        (funs, stmts @ [parseDeclGivenType state t])
                | _ ->
                    raise (UnexpectedToken (state.peek, ""))
                    
        
    type AstFrame =
        {prev: AstFrame option; vars: Map<string, AstType>; funcs: Map<string, AstType>}
        member this.getVar (name: string): AstType =
            match this.vars.TryFind name with
                | None -> match this.prev with
                            | Some prev -> prev.getVar name
                            | None -> raise UndefinedVar
                | Some t -> t
        member this.getFunc (name: string): AstType =
            match this.funcs.TryFind name with
                | None -> match this.prev with
                            | Some prev -> prev.getFunc name
                            | None -> raise UndefinedFunction
                | Some t -> t
        member this.addVar (name: string) (t: AstType): AstFrame =
            {this with vars = this.vars.Add (name, t)}
        member this.addFun (name: string) (t: AstType): AstFrame =
            {this with funcs = this.funcs.Add (name, t)}
        member this.newFrame: AstFrame =
            {this with prev = Some this; vars = Map.empty}
        
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
            | AstExpr.Unary (_, TokenType.STAR, e) ->
                let e = typifyE frame e
                let t = getType e
                match t with
                    | AstType.Pointer pt -> AstExpr.Unary (pt, TokenType.STAR, e)
                    | _ -> raise DerefNonPointer
            | AstExpr.Unary (_, op, e) ->
                let e = typifyE frame e
                AstExpr.Unary (getType e, op, e)
            | AstExpr.Const _ -> expr
            | AstExpr.Cast (t, e) -> AstExpr.Cast (t, typifyE frame e)
            | AstExpr.FunCall (_, n, ps) -> AstExpr.FunCall (frame.getFunc n, n, List.map (typifyE frame) ps)
        
    let rec typifyS (frame: AstFrame) (stmt: AstStmt): AstFrame * AstStmt =
        match stmt with
            | AstStmt.Decls (t, decls) ->
                let mutable ans = []
                let mutable frame = frame
                for decl in decls do
                    frame <- frame.addVar (fst decl) t
                    match decl with
                        | (_, None) -> ans <- ans @ [decl]
                        | (n, Some(e)) -> ans <- ans @ [(n, Some (typifyE frame e))]
                        
                (frame, AstStmt.Decls (t, ans))
            | AstStmt.Expr e -> (frame, AstStmt.Expr (typifyE frame e))
            | AstStmt.Return e -> (frame, AstStmt.Return (typifyE frame e))
            | AstStmt.Block l ->
                let frame2 = frame.newFrame
                (frame, AstStmt.Block (fst (List.fold
                                        (fun fstate fstmt ->
                                            let flist, fframe = fstate
                                            let fframe, fstmt = (typifyS fframe fstmt)
                                            (flist @ [fstmt], fframe)
                                        ) ([], frame2) l)))
            | AstStmt.StructDecl _ -> (frame, stmt)
            | AstStmt.Nop -> (frame, stmt)
        
    let typifyFun (f: AstFun) (frame: AstFrame): AstFun =
        let frame = frame.newFrame
        let frame =
            List.fold
                (fun (s: AstFrame) param -> s.addVar (snd param) (fst param))
                frame f.parameters
        AstFun (f.ret, f.name, f.parameters, snd (typifyS frame f.body))
    
    let typify (frame: AstFrame) (fs: AstFun list): AstFun list =
        let mutable frame = frame
        let mutable ans = []
        for f in fs do
            frame <- frame.addFun f.name f.ret
            ans <- ans @ [typifyFun f frame]
        ans
    
    let parseEnt (tokens: Token list) : AstFun list =
        let funs, globals = parse {Tokens=tokens; Types=ParserStateTypes.empty} ([], [])
        let mutable frame = {prev = None; vars = Map.empty; funcs = Map.empty}
        let globals =
            List.collect
              (fun g ->
                match g with
                  | AstStmt.Decls (t, l) -> List.map (fun (x, y) -> (t, x, y)) l
                  | _ -> []
              ) globals
        for (t, n, _) in globals do
            frame <- frame.addVar n t
        typify frame funs