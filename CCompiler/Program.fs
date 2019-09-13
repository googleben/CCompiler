namespace CCompiler
module Lexer = 
    open System
    open System
    open System.IO
    open System.Text.RegularExpressions


    type TokenType =
        | OPEN_CURLY
        | CLOSE_CURLY
        | OPEN_PAREN
        | CLOSE_PAREN
        | SEMICOLON
        | INT
        | VOID
        | RETURN
        | INT_LITERAL
        | IDENT
        
    let getKeywordTokenType str =
        match str with
            | "int" -> Some INT
            | "void" -> Some VOID
            | "return" -> Some RETURN
            | _ -> None
        
    type Token = {Pos:Tuple<int,int>; Type: TokenType; Src:string}

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
            | ";" -> SEMICOLON
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
        match (getKeywordTokenType str) with
            | Some tt -> {Pos=(line, linePos'); Type=tt; Src=str}
            | None -> {Pos=(line, linePos'); Type=IDENT; Src=str}

    let getNumber (first: char) (file: string) (pos: byref<int>) (linePos: byref<int>) (line: int) =
        let linePos' = linePos - 1
        let mutable str = string first
        while Char.IsNumber (file.Chars pos) do
            str <- str + (string (file.Chars pos))
            pos <- pos + 1
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
                        | c when Char.IsLetter(c) -> [getIdentOrKeyword c file &pos' &linePos' line]
                        | c when Char.IsNumber(c) -> [getNumber c file &pos' &linePos' line]
            lex file pos' line' linePos' now
               

    let lexEnt (file': string) =
        let file = file'.Replace("\r", "")
        printfn "%O" file
        let lexed = lex file 0 0 0 []
        printfn "%A" lexed

    let fileToString (file:FileStream) =
        use reader = new StreamReader(file)
        reader.ReadToEnd ()
        
    [<EntryPoint>]
    let main argv = 
        lexEnt ((File.OpenRead "in.c") |> fileToString)
        0 // return an integer exit code
        