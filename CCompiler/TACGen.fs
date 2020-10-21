module CCompiler.TACGen

//generates 3-address code

module TACGen =
    open Parser
    open Lexer
    
    exception TypePropagationFailed
    
    exception Unimplemented
    
    exception LValueExpected
    
    type TACType =
        | Int8 | Int16 | Int32 | Int64
        | UInt8 | UInt16 | UInt32 | UInt64
        | Float32 | Float64
        | Pointer of TACType
        | Struct of TACType list
        | Void
    
    type Address =
        | Name of TACType * string
        | Constant of TACType * AstConst
        | Temp of TACType * int
        
    type TAC =
        | Binary of dest:Address * left:Address * operator:TokenType * right:Address
        | Unary of dest:Address * operator:TokenType * value:Address
        | Const of dest:Address * value:AstConst
        | Copy of dest:Address * src:Address
        //copies the second argument to where the first argument points
        | CopyToDeref of destPtr:Address * src:Address
        //copies the value pointed at by the second argument to the first argument
        | GetDeref of dest:Address * srcPtr:Address
        | Jump of dest:int
        | CondJump of cond:Address * desired:bool * dest:int
        | Param of value:Address
        | FunCall of name:string
        | CopyFunCall of dest:Address * name:string
        | Return of value:Address
        //following instructions are pseudo-instructions which don't count as an extra "expr"
        //and aren't executed (they just provide information to following stages of compilation)
        | NewScope of varNames:string list
        | CloseScope
        
    type TACState =
        {temps: int; currExpr: int; pendingPostfix: TAC list}
        
        member this.newTemp = {this with temps = this.temps + 1}
        member this.newExpr = {this with currExpr = this.currExpr + 1}
        member this.newExprs n = {this with currExpr = this.currExpr + n}
        member this.newPostfix tac = {this with pendingPostfix = tac :: this.pendingPostfix}
    
    let rec getTacType (astType: AstType): TACType =
        match astType with
            | AstType.SByte -> TACType.Int8
            | AstType.UByte -> TACType.UInt8
            | AstType.SShort -> TACType.Int16
            | AstType.UShort -> TACType.UInt16
            | AstType.SInt -> TACType.Int32
            | AstType.UInt -> TACType.UInt32
            | AstType.SLong -> TACType.Int64
            | AstType.ULong -> TACType.UInt64
            | AstType.Float -> TACType.Float32
            | AstType.Double -> TACType.Float64
            | AstType.Void -> TACType.Void
            | AstType.Struct l -> TACType.Struct (List.map getTacType (List.map fst l))
            | AstType.Pointer t -> TACType.Pointer (getTacType t)
            | AstType.Typedef t -> getTacType t
            | AstType.Undef -> raise TypePropagationFailed
    
    let rec tacifyE (expr: AstExpr, state: TACState): TAC list * Address * TACState =
        match expr with
            | AstExpr.Const (t, v) ->
                ([], Address.Constant ((getTacType t), v), state)
            | AstExpr.Ident (t, s) ->
                ([], Address.Name ((getTacType t), s), state)
            | AstExpr.Unary (t, TokenType.STAR, e) ->
                let l, ret, state = tacifyE (e, state)
                let dest = (Address.Temp ((getTacType t), state.temps))
                (l @ [TAC.GetDeref(dest, ret)], dest, state.newTemp.newExpr)
            | AstExpr.Unary (t, o, e) ->
                let l, ret, state = tacifyE (e, state)
                let dest = (Address.Temp ((getTacType t), state.temps))
                (l @ [TAC.Unary(dest, o, ret)], dest, state.newTemp.newExpr)
            | AstExpr.Postfix (_, o, e) ->
                if o = TokenType.PLUS_PLUS || o = TokenType.MINUS_MINUS then
                    let op = if o = TokenType.PLUS_PLUS then TokenType.PLUS else TokenType.MINUS
                    match e with
                        | AstExpr.Ident (t2, s) ->
                            let t2 = getTacType t2
                            let l, ret, state = tacifyE (e, state)
                            (l, ret, state.newPostfix (TAC.Binary (Address.Name(t2, s), Address.Name(t2, s), op, Address.Constant (t2, AstConst.Int 1))))
                        | AstExpr.Unary (t2, TokenType.STAR, s) ->
                            let t2 = getTacType t2
                            //s is a pointer. evaluate it to get the address it points to, ptrVal.
                            let l, ptrVal, state = tacifyE (s, state)
                            //now deref the pointer to get the value we want
                            let ret = Address.Temp(t2, state.temps)
                            let l = l @ [TAC.GetDeref(ret, ptrVal)]
                            let state = state.newTemp.newExpr
                            //increment the deref'd value
                            let l = l @ [TAC.Binary(Address.Temp(t2, state.temps), ret, op, Address.Constant (t2, AstConst.Int 1))]
                            let ret2 = Address.Temp(t2, state.temps)
                            let state = state.newTemp.newExpr
                            (l, ret, state.newPostfix (TAC.CopyToDeref (ptrVal, ret2)))
                        | _ -> raise LValueExpected
                else raise Unimplemented //TODO: any other postfix like array deref
            | AstExpr.Binary (_, a, TokenType.EQUALS, b) ->
                let l, b, state = tacifyE (b, state)
                match a with
                    | AstExpr.Ident (t2, s) ->
                        let t2 = getTacType t2
                        (l @ [TAC.Copy (Address.Name (t2, s), b)], b, state.newExpr)
                    | AstExpr.Unary (_, TokenType.STAR, s) ->
                        //s is a pointer, get its address
                        let l2, ptrVal, state = tacifyE (s, state)
                        let l = l @ l2
                        (l @ [TAC.CopyToDeref (ptrVal, b)], b, state.newExpr)
                    | _ -> raise LValueExpected
            | AstExpr.Binary (t, a, o, b) ->
                let t = getTacType t
                let l, a, state = tacifyE (a, state)
                let l2, b, state = tacifyE (b, state)
                let l = l @ l2
                let dest = Address.Temp(t, state.temps)
                (l @ [TAC.Binary(dest, a, o, b)], dest, state.newTemp.newExpr)
            | AstExpr.Conditional (t, cond, a, b) ->
                //high level overview:
                
                //    compute condition, place in "cond"
                //    if "cond" is true, jump to a
                //    compute b
                //    place b's answer in ret
                //    jump to the end
                //a:  compute a
                //    place a's answer in ret
                //end:(the next statement, created after this function returns)
                
                let t = getTacType t
                //start by just computing the condition
                let l, cond, state = tacifyE(cond, state)
                //now create the temp variable which will be assigned to by one of the branches
                let ret = Address.Temp (t, state.temps)
                //we need to preemptively add an expr here for the conditional jump we add later
                let state = state.newTemp.newExpr
                let l2, b, state = tacifyE (b, state)
                let l = l @ l2
                //we need to copy the return value of both branches into ret
                //since by default they return to different locations, but
                //we need to have only one location by the end
                let l = l @ [TAC.Copy (ret, b)]
                //again, preparing for a jump we'll add later
                let state = state.newExpr.newExpr
                //now add the first (conditional) jump
                let l = [TAC.CondJump (cond, true, state.currExpr)] @ l
                
                
                let l2, a, state = tacifyE (a, state)
                let l2 = l2 @ [TAC.Copy (ret, a)]
                let state = state.newExpr
                //now we add in the second (unconditional) jump while merging everything
                let l = l @ [TAC.Jump state.currExpr] @ l2
                
                (l, ret, state)
            | AstExpr.Cast (t, e) ->
                let t = getTacType t
                let l, e, state = tacifyE (e, state)
                let ret = match e with
                            | Address.Constant (_, c) -> Address.Constant (t, c)
                            | Address.Name (_, s) -> Address.Name (t, s)
                            | Address.Temp (_, n) -> Address.Temp (t, n)
                (l, ret, state)
            | AstExpr.FunCall (t, fname, args) ->
                let t = getTacType t
                //compute each of the arguments
                //args will be a list of addresses, each being one argument
                let l, args, state = List.fold
                                         (fun fstate e ->
                                            let fl, frets, fstate = fstate
                                            let fl2, fret, fstate = tacifyE (e, fstate)
                                            (fl @ fl2, frets @ [fret], fstate))
                                         ([], [], state) args
                //now put each of the arguments into a Param expression
                let argsL = List.map (fun a -> TAC.Param a) args
                let l = l @ argsL
                let state = state.newExprs l.Length
                //now we just need to actually call the function
                
                //if it returns void, we'll return void
                //but if it return a value, we'll store that in a temporary
                match t with
                    | TACType.Void ->
                        (l @ [TAC.FunCall fname], Address.Constant (TACType.Void, AstConst.Void), state.newExpr)
                    | _ ->
                        let dest = Address.Temp (t, state.temps)
                        (l @ [TAC.CopyFunCall (dest, fname)], dest, state.newTemp.newExpr)
                
                
    let rec tacifyS (stmt: AstStmt, state: TACState): TAC list * TACState =
        match stmt with
            | AstStmt.Return e ->
                let l, ret, state = tacifyE (e, state)
                (l @ [TAC.Return ret], state.newExpr)
            | AstStmt.Expr e ->
                let l, _, state = tacifyE (e, state)
                (l, state)
            | AstStmt.Block sl ->
                //turn the list of statements into a list of TAC expressions
                let l, state =
                   List.fold (fun (fstatet) (fstmt: AstStmt) ->
                       let flist, fstate = fstatet
                       let flist2, fstate = tacifyS (fstmt, fstate)
                       (flist @ flist2, fstate)
                   ) ([], state) sl
                //get a list of variable names declared DIRECTLY in this scope
                //this does not include declarations in child scopes.
                //we need this to keep track of where things should be stored e.g. during
                //recursion where the same block can be entered more than once without
                //exiting, so simply determining which scope may not be good enough.
                //we're essentially simulating stack enter/exit instructions in TAC
                let varNames =
                    sl
                        |> List.choose
                               (fun s ->
                                    match s with
                                        | AstStmt.Decls (_,s) -> Some(s)
                                        | _ -> None
                                )
                        |> List.fold (@) []
                        |> List.map fst
                (TAC.NewScope (varNames) :: l @ [TAC.CloseScope], state)
            | AstStmt.Decls (t, decls) ->
                let t = getTacType t
                let l, state =
                    List.fold
                        (fun fstate decl ->
                            let l, state = fstate
                            match decl with
                                | (_, None) -> (l, state)
                                | (n, Some(e)) ->
                                    let l2, ret, state = tacifyE (e, state)
                                    let l = l @ l2 @ [TAC.Copy (Address.Name (t, n), ret)]
                                    (l, state.newExpr)
                        ) ([], state) decls
                (l, state)
            | AstStmt.StructDecl _ | AstStmt.Nop -> ([], state)
                
    let tacifyFun (f: AstFun, state: TACState): TAC list * TACState =
        let l, s = tacifyS (f.body, state)
        (TAC.NewScope (List.map snd f.parameters) :: l @ [TAC.CloseScope], s)
        
    type TACInfo = {functions: Map<string, int>; code: TAC list}
        
    let tacifyFuns (fs: AstFun list): TACInfo =
        let state = {temps = 0; currExpr = 0; pendingPostfix = []}
        let l, _, funcs =
           List.fold (fun (fstatet) (ffun: AstFun) ->
               let flist, fstate, funcs = fstatet
               let funcStart = fstate.currExpr
               let flist2, fstate = tacifyFun (ffun, fstate)
               (flist @ flist2, fstate, Map.add ffun.name funcStart funcs)
           ) ([], state, Map.empty) fs
        {functions = funcs; code = l}