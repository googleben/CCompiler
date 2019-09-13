namespace CCompiler
open System.Linq.Expressions

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
        | PERIOD
        | COMMA
        | DOUBLE_QUOTE
        | SINGLE_QUOTE
        | PIPE
        | DOUBLE_PIPE
        | AMPERSAND
        | DOUBLE_AMPERSAND
        | CARET
        | STAR
        | PLUS
        | MINUS
        | EQUALS
        | DOUBLE_EQUALS
        | EXCLAMATION
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
        
    type Token = {Pos:Tuple<int,int>; Type: TokenType; Src:string}
    
    let rec printTokens (tokens: Token list) =
        match tokens with
            | token::rest -> printf "%O%s" token.Type (if not (rest = []) && (fst (List.head rest).Pos) > (fst token.Pos) then "\n" else " "); printTokens rest
            | [] -> ()

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
            | "\"" -> DOUBLE_QUOTE
            | "'" -> SINGLE_QUOTE
            | "|" -> PIPE
            | "||" -> DOUBLE_PIPE
            | "&" -> AMPERSAND
            | "&&" -> DOUBLE_AMPERSAND
            | "^" -> CARET
            | "*" -> STAR
            | "+" -> PLUS
            | "-" -> MINUS
            | "=" -> EQUALS
            | "==" -> DOUBLE_EQUALS
            | "!" -> EXCLAMATION
            | "int" -> INT
            | "void" -> VOID
            | "return" -> RETURN
            | curr when Regex.IsMatch("^\d+$", curr) -> INT_LITERAL
            | _ -> IDENT
        
    let getToken (lexeme: string) (line: int) (linePos: int): Token =
        {Pos=(line, linePos); Type=getTokenType(lexeme); Src=lexeme}
        
    let getIdentOrKeyword (first: char) (file: string) (pos: byref<int>) (linePos: byref<int>) (line: int) =
        let linePos' = linePos - 1
        let mutable str = string first
        while Char.IsLetter (file.Chars pos) do
            str <- str + (string (file.Chars pos))
            pos <- pos + 1
            if pos = file.Length then raise UnexpectedEOF else ()
        match (getKeywordTokenType str) with
            | Some tt -> {Pos=(line, linePos'); Type=tt; Src=str}
            | None -> {Pos=(line, linePos'); Type=IDENT; Src=str}

    let getNumber (first: char) (file: string) (pos: byref<int>) (linePos: byref<int>) (line: int) =
        let linePos' = linePos - 1
        let mutable str = string first
        while Char.IsNumber (file.Chars pos) do
            str <- str + (string (file.Chars pos))
            pos <- pos + 1
            if pos = file.Length then raise UnexpectedEOF else ()
        {Pos=(line, linePos'); Type=INT_LITERAL; Src=str}
        

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
                        | '|' -> if (file.Chars pos') = '|' then pos' <- pos' + 1; linePos' <- linePos' + 1; [getToken "||" line linePos] else [getToken "|" line linePos]
                        | '&' -> if (file.Chars pos') = '&' then pos' <- pos' + 1; linePos' <- linePos' + 1; [getToken "&&" line linePos] else [getToken "&" line linePos]
                        | '^' -> [getToken "^" line linePos]
                        | '*' -> [getToken "*" line linePos]
                        | '+' -> [getToken "+" line linePos]
                        | '-' -> [getToken "-" line linePos]
                        | '=' -> if (file.Chars pos') = '=' then pos' <- pos' + 1; linePos' <- linePos' + 1; [getToken "==" line linePos] else [getToken "=" line linePos]
                        | '!' -> [getToken "!" line linePos]
                        | c when Char.IsLetter(c) -> [getIdentOrKeyword c file &pos' &linePos' line]
                        | c when Char.IsNumber(c) -> [getNumber c file &pos' &linePos' line]
                        | c -> raise (UnexpectedCharacter c)
            lex file pos' line' linePos' now
               

    let lexEnt (file': string) =
        let file = file'.Replace("\r", "")
        printfn "%O" file
        let lexed = lex file 0 0 0 []
        printTokens lexed

    let fileToString (file:FileStream) =
        use reader = new StreamReader(file)
        reader.ReadToEnd ()
        
    [<EntryPoint>]
    let main argv = 
        lexEnt ((File.OpenRead "in.c") |> fileToString)
        0 // return an integer exit code
        