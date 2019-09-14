namespace CCompiler
module Lexer =
    open System
    open System
    open System.IO
    open System.Text.RegularExpressions

    exception UnexpectedEOF
    exception UnexpectedCharacter of char

    type TokenType =
        //special characters
        | OPEN_CURLY
        | CLOSE_CURLY
        | OPEN_PAREN
        | CLOSE_PAREN
        | OPEN_SQUARE
        | CLOSE_SQUARE
        | SEMICOLON
        | COMMA
        | DOUBLE_QUOTE
        | SINGLE_QUOTE
        //operators
        | QUESTION
        | COLON
        | PERIOD
        | PERCENT
        | PERCENT_EQUALS
        | SLASH
        | SLASH_EQUALS
        | PIPE
        | PIPE_PIPE
        | PIPE_EQUALS
        | AMPERSAND
        | AMPERSAND_AMPERSAND
        | AMPERSAND_EQUALS
        | CARET
        | CARET_EQUALS
        | STAR
        | STAR_EQUALS
        | PLUS
        | PLUS_PLUS
        | PLUS_EQUALS
        | MINUS
        | MINUS_MINUS
        | MINUS_EQUALS
        | EQUALS
        | EQUALS_EQUALS
        | BANG
        | BANG_EQUALS
        | GREATER
        | GREATER_GREATER
        | GREATER_GREATER_EQUALS
        | GREATER_EQUALS
        | LESS
        | LESS_LESS
        | LESS_LESS_EQUALS
        | LESS_EQUALS
        | TILDE
        //keywords
        | AUTO
        | BREAK
        | CASE
        | CHAR
        | CONST
        | CONTINUE
        | DEFAULT
        | DO
        | DOUBLE
        | ELSE
        | ENUM
        | EXTERN
        | FLOAT
        | FOR
        | GOTO
        | IF
        | INT
        | LONG
        | REGISTER
        | RETURN
        | SHORT
        | SIGNED
        | SIZEOF
        | STATIC
        | STRUCT
        | SWITCH
        | TYPEDEF
        | UNION
        | UNSIGNED
        | VOID
        | VOLATILE
        | WHILE
        | INT_LITERAL
        | IDENT
        
    let getKeywordTokenType str =
        match str with
            | "auto" -> Some AUTO
            | "break" -> Some BREAK
            | "case" -> Some CASE
            | "char" -> Some CHAR
            | "const" -> Some CONST
            | "continue" -> Some CONTINUE
            | "default" -> Some DEFAULT
            | "do" -> Some DO
            | "double" -> Some DOUBLE
            | "else" -> Some ELSE
            | "enum" -> Some ENUM
            | "extern" -> Some EXTERN
            | "float" -> Some FLOAT
            | "for" -> Some FOR
            | "goto" -> Some GOTO
            | "if" -> Some IF
            | "int" -> Some INT
            | "long" -> Some LONG
            | "register" -> Some REGISTER
            | "return" -> Some RETURN
            | "short" -> Some SHORT
            | "signed" -> Some SIGNED
            | "sizeof" -> Some SIZEOF
            | "static" -> Some STATIC
            | "struct" -> Some STRUCT
            | "switch" -> Some SWITCH
            | "typedef" -> Some TYPEDEF
            | "union" -> Some UNION
            | "unsigned" -> Some UNSIGNED
            | "void" -> Some VOID
            | "volatile" -> Some VOLATILE
            | "while" -> Some WHILE
            | _ -> None
        
    type Token = {Pos:Tuple<int,int>; Type: TokenType; Lexeme:string}
    
    let rec printTokens (tokens: Token list) =
        match tokens with
            | token::rest -> printf "%O%s" token.Type (if not (rest = []) && (fst (List.head rest).Pos) > (fst token.Pos) then "\n" else " "); printTokens rest
            | [] -> printfn ""

    let (|Newline|Whitespace|Semicolon|Other|) ch =
        if ch = '\n' then Newline
        elif ch = ';' then Semicolon
        elif Char.IsWhiteSpace(ch) then Whitespace
        else Other
           
    let getTokenType (curr: String): TokenType =
        match curr with
            | "{" -> OPEN_CURLY
            | "}" -> CLOSE_CURLY
            | "(" -> OPEN_PAREN
            | ")" -> CLOSE_PAREN
            | "[" -> OPEN_SQUARE
            | "]" -> CLOSE_SQUARE
            | ";" -> SEMICOLON
            | "." -> PERIOD
            | "," -> COMMA
            | "?" -> QUESTION
            | ":" -> COLON
            | "\"" -> DOUBLE_QUOTE
            | "'" -> SINGLE_QUOTE
            | "|" -> PIPE
            | "||" -> PIPE_PIPE
            | "|=" -> PIPE_EQUALS
            | "~" -> TILDE
            | "%" -> PERCENT
            | "%=" -> PERCENT_EQUALS
            | "&" -> AMPERSAND
            | "&&" -> AMPERSAND_AMPERSAND
            | "&=" -> AMPERSAND_EQUALS
            | "^" -> CARET
            | "^=" -> CARET_EQUALS
            | "*" -> STAR
            | "*=" -> STAR_EQUALS
            | "+" -> PLUS
            | "++" -> PLUS_PLUS
            | "+=" -> PLUS_EQUALS
            | "-" -> MINUS
            | "--" -> MINUS_MINUS
            | "-=" -> MINUS_EQUALS
            | "=" -> EQUALS
            | "==" -> EQUALS_EQUALS
            | "!" -> BANG
            | "!=" -> BANG_EQUALS
            | ">" -> GREATER
            | ">>" -> GREATER_GREATER
            | ">=" -> GREATER_EQUALS
            | ">>=" -> GREATER_GREATER_EQUALS
            | "<" -> LESS
            | "<<" -> LESS_LESS
            | "<=" -> LESS_EQUALS
            | "<<=" -> LESS_LESS_EQUALS
            | "int" -> INT
            | "void" -> VOID
            | "return" -> RETURN
            | curr when Regex.IsMatch("^\d+$", curr) -> INT_LITERAL
            | _ -> IDENT
        
    let getToken (lexeme: string) (line: int) (linePos: int): Token =
        {Pos=(line, linePos); Type=getTokenType(lexeme); Lexeme=lexeme}
        
    let getIdentOrKeyword (first: char) (file: string) (pos: byref<int>) (linePos: byref<int>) (line: int) =
        let linePos' = linePos - 1
        let mutable str = string first
        while Char.IsLetterOrDigit (file.Chars pos) do
            str <- str + (string (file.Chars pos))
            pos <- pos + 1
            if pos = file.Length then raise UnexpectedEOF else ()
        match (getKeywordTokenType str) with
            | Some tt -> {Pos=(line, linePos'); Type=tt; Lexeme=str}
            | None -> {Pos=(line, linePos'); Type=IDENT; Lexeme=str}

    let getNumber (first: char) (file: string) (pos: byref<int>) (linePos: byref<int>) (line: int) =
        let linePos' = linePos - 1
        let mutable str = string first
        while Char.IsDigit (file.Chars pos) do
            str <- str + (string (file.Chars pos))
            pos <- pos + 1
            if pos = file.Length then raise UnexpectedEOF else ()
        {Pos=(line, linePos'); Type=INT_LITERAL; Lexeme=str}
        

    let rec lex (file: string) (pos: int) (line: int) (linePos: int) (prev_list: Token list): Token list =
        if pos = file.Length then prev_list
        else
            let mutable pos' = pos + 1
            let mutable line' = line
            let mutable linePos' = linePos + 1
            let now = prev_list @
                      match file.Chars pos with
                        | ' ' | '\t' -> []
                        | '\n' -> line' <- line + 1; linePos' <- 0; []
                        | '{' -> [getToken "{" line linePos]
                        | '}' -> [getToken "}" line linePos]
                        | '(' -> [getToken "(" line linePos]
                        | ')' -> [getToken ")" line linePos]
                        | ';' -> [getToken ";" line linePos]
                        | '.' -> [getToken "." line linePos]
                        | ',' -> [getToken "," line linePos]
                        | '\"' -> [getToken "\"" line linePos]
                        | '\'' -> [getToken "'" line linePos]
                        | '~' -> [getToken "~" line linePos]
                        | '|' ->
                            if (file.Chars pos') = '|' then pos' <- pos' + 1; linePos' <- linePos' + 1; [getToken "||" line linePos]
                            elif (file.Chars pos') = '=' then pos' <- pos' + 1; linePos' <- linePos' + 1; [getToken "&=" line linePos]
                            else [getToken "|" line linePos]
                        | '&' ->
                            if (file.Chars pos') = '&' then pos' <- pos' + 1; linePos' <- linePos' + 1; [getToken "&&" line linePos]
                            elif (file.Chars pos') = '=' then pos' <- pos' + 1; linePos' <- linePos' + 1; [getToken "&=" line linePos]
                            else [getToken "&" line linePos]
                        | '^' ->
                            if (file.Chars pos') = '=' then pos' <- pos' + 1; linePos' <- linePos' + 1; [getToken "^=" line linePos]
                            else [getToken "^" line linePos]
                        | '*' ->
                            if (file.Chars pos') = '=' then pos' <- pos' + 1; linePos' <- linePos' + 1; [getToken "*=" line linePos]
                            else [getToken "*" line linePos]
                        | '+' ->
                            if (file.Chars pos') = '+' then pos' <- pos' + 1; linePos' <- linePos' + 1; [getToken "++" line linePos]
                            elif (file.Chars pos') = '=' then pos' <- pos' + 1; linePos' <- linePos' + 1; [getToken "+=" line linePos]
                            else [getToken "+" line linePos]
                        | '-' ->
                            if (file.Chars pos') = '-' then pos' <- pos' + 1; linePos' <- linePos' + 1; [getToken "--" line linePos]
                            elif (file.Chars pos') = '=' then pos' <- pos' + 1; linePos' <- linePos' + 1; [getToken "-=" line linePos]
                            else [getToken "-" line linePos]
                        | '=' ->
                            if (file.Chars pos') = '=' then pos' <- pos' + 1; linePos' <- linePos' + 1; [getToken "==" line linePos]
                            else [getToken "=" line linePos]
                        | '!' ->
                            if (file.Chars pos') = '=' then pos' <- pos' + 1; linePos' <- linePos' + 1; [getToken "!=" line linePos]
                            else [getToken "!" line linePos]
                        | '/' ->
                            if (file.Chars pos') = '=' then pos' <- pos' + 1; linePos' <- linePos' + 1; [getToken "/=" line linePos]
                            else [getToken "/" line linePos]
                        | '%' ->
                            if (file.Chars pos') = '=' then pos' <- pos' + 1; linePos' <- linePos' + 1; [getToken "/=" line linePos]
                            else [getToken "/" line linePos]
                        | '>' ->
                            if (file.Chars pos') = '>' then
                                pos' <- pos' + 1; linePos' <- linePos' + 1; if (file.Chars pos') = '=' then
                                                                             pos' <- pos' + 1; linePos' <- linePos' + 1; [getToken ">>=" line linePos]
                                                                             else [getToken ">>" line linePos]
                            elif (file.Chars pos') = '=' then pos' <- pos' + 1; linePos' <- linePos' + 1; [getToken ">=" line linePos]
                            else [getToken ">" line linePos]
                        | '<' ->
                            if (file.Chars pos') = '<' then
                                pos' <- pos' + 1; linePos' <- linePos' + 1; if (file.Chars pos') = '=' then
                                                                             pos' <- pos' + 1; linePos' <- linePos' + 1; [getToken "<<=" line linePos]
                                                                             else [getToken "<" line linePos]
                            elif (file.Chars pos') = '=' then pos' <- pos' + 1; linePos' <- linePos' + 1; [getToken "<=" line linePos]
                            else [getToken "<" line linePos]
                        | c when Char.IsLetter(c) -> [getIdentOrKeyword c file &pos' &linePos' line]
                        | c when Char.IsDigit(c) -> [getNumber c file &pos' &linePos' line]
                        | c -> raise (UnexpectedCharacter c)
            lex file pos' line' linePos' now
               

    let lexEnt (file': string) =
        let file = file'.Replace("\r", "")
        printfn "%O" file
        let lexed = lex file 0 0 0 []
        lexed

    let fileToString (file:FileStream) =
        use reader = new StreamReader(file)
        reader.ReadToEnd ()

