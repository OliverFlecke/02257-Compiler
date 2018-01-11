namespace GuardedCommands.Backend
// Michael R. Hansen 05-01-2016, 04-01-2018
// This file is obtained by an adaption of the file MicroC/Comp.fs by Peter Sestoft
open System
open Machine

open GuardedCommands.Frontend.AST
open System
module CodeGeneration =


(* A global variable has an absolute address, a local one has an offset: *)
    type Var =
        | GloVar of int                   (* absolute address in stack           *)
        | LocVar of int                   (* address relative to bottom of frame *)

(* The variable environment keeps track of global and local variables, and
   keeps track of next available offset for local variables *)

    type varEnv = Map<string, Var*Typ> * int

(* The function environment maps function name to label and parameter decs *)
    type Name = string
    type ParamDecs = (Typ * string) list
    type funEnv = Map<Name, label * Typ option * ParamDecs> * Name option

    let allocateDecs vEnv decs = List.fold (fun env ->
        function
            | (VarDec (t, n))   -> (Map.add n (LocVar (snd env), t) <| fst env, snd env + 1)
            | _                 -> failwith "Not supported") (fst vEnv, 0) decs 

/// CE vEnv fEnv e gives the code for an expression e on the basis of a variable and a function environment
    let rec CE vEnv fEnv = function
        | N n                   -> [CSTI n]
        | B b                   -> [CSTI (if b then 1 else 0)]
        | Access acc            -> CA vEnv fEnv acc @ [LDI]
        | Apply("-", [e])       -> CE vEnv fEnv e @ [CSTI 0; SWAP; SUB]
        | Apply("!", [e])       ->
            let labelFalse = newLabel ()
            let labelEnd = newLabel ()
            CE vEnv fEnv e
            @ [IFZERO labelFalse; CSTI 0; GOTO labelEnd;
            Label labelFalse; CSTI 1; Label labelEnd]
        | Apply("&&",[b1;b2])   -> let labend   = newLabel()
                                   let labfalse = newLabel()
                                   CE vEnv fEnv b1 @ [IFZERO labfalse] @ CE vEnv fEnv b2
                                   @ [GOTO labend; Label labfalse; CSTI 0; Label labend]

        | Apply(o,[e1;e2]) when List.exists (fun x -> o=x) ["+";"*";"=";"-";">";"<";">=";"<="]
                             -> let ins = match o with
                                          | "+"     -> [ADD]
                                          | "*"     -> [MUL]
                                          | "="     -> [EQ]
                                          | "-"     -> [SUB]
                                          | "<"     -> [LT]
                                          | ">"     -> [SWAP; LT]
                                          | "<="    -> [CSTI 1; ADD; LT]
                                          | ">="    -> [CSTI 1; SUB; SWAP; LT]
                                          | _       -> failwith "CE: this case is not possible"
                                CE vEnv fEnv e1 @ CE vEnv fEnv e2 @ ins
        | Apply (f, es)     ->
            let (label, _, _) = Map.find f (fst fEnv)
            List.collect (CE vEnv fEnv) es @ [CALL ((es.Length), label)]
        | x                 -> failwith ("CE: not supported yet " + string x)


/// CA vEnv fEnv acc gives the code for an access acc on the basis of a variable and a function environment
    and CA vEnv fEnv = function
        | AVar x         ->
            match Map.find x (fst vEnv) with
                | (GloVar addr,_) -> [CSTI addr]
                | (LocVar addr,_) -> [GETBP; CSTI addr; ADD] //failwith "CA: Local variables not supported yet"
        | AIndex(acc, e) -> CA vEnv fEnv acc @ [LDI] @ CE vEnv fEnv e @ [ADD]
        | ADeref e       -> failwith "CA: pointer dereferencing not supported yet"


(* Bind declared variable in env and generate code to allocate it: *)
    let allocate (kind : int -> Var) (typ, x) (vEnv : varEnv)  =
        let (env, fdepth) = vEnv
        match typ with
            | ATyp (ATyp _, _) ->
                raise (Failure "allocate: array of arrays not permitted")
            | ATyp (_, Some n) ->
                let varKind = kind (fdepth + n)
                let env' = (Map.add x (varKind, typ) env, fdepth + n + 1)
                match varKind with 
                    | LocVar _ -> (env', [INCSP n; GETBP; CSTI fdepth; ADD])
                    | GloVar _ -> (env', [INCSP n; CSTI fdepth])
            | _ ->
                let env' = (Map.add x (kind fdepth, typ) env, fdepth+1)
                let code = [INCSP 1]
                (env', code)

    let decsLength = List.fold (+) 0 << List.map (function 
        | VarDec (ATyp (_, Some n), _)  -> n + 1
        | _                             -> 1)
/// CS vEnv fEnv s gives the code for a statement s on the basis of a variable and a function environment
    let rec CS (vEnv : varEnv) (fEnv : funEnv) = function
        | PrintLn e         -> CE vEnv fEnv e @ [PRINTI; INCSP -1]
        | Ass(acc,e)        -> CA vEnv fEnv acc @ CE vEnv fEnv e @ [STI; INCSP -1]
        | Block(decs, stms)    -> 
            let (vEnv', decsCode) = List.fold (fun (env, code) -> 
                function 
                    | VarDec (t,n)  -> 
                        let (env', code') = allocate LocVar (t, n) env
                        (env', code @ code')
                    | _             -> failwith "Cs: function not supported in local declaration") (vEnv, []) decs
            
            decsCode @ CSs vEnv' fEnv stms @ [INCSP -(decsLength decs)]
        | Alt (GC gc)       ->
            let labelEnd = newLabel ()
            guardStm labelEnd vEnv fEnv gc @ [Label labelEnd]
        | Do (GC gc)        ->
            let labelStart = newLabel ()
            [Label labelStart] @ guardStm labelStart vEnv fEnv gc
        | Return e ->
            let exprInst =
                match e with
                    | Some exp  -> CE vEnv fEnv exp
                    | None      -> []
            exprInst @ [RET (snd vEnv)]
        | Call (p, exprs)       -> 
            let (label, _, _) = Map.find p (fst fEnv)
            List.collect (CE vEnv fEnv) exprs @ [CALL ((exprs.Length), label); INCSP -1]
        // | x                 -> failwith ("CS: this statement is not supported yet " + string x)

    and CSs vEnv fEnv stms = List.collect (CS vEnv fEnv) stms
    and guardStm label vEnv fEnv =
            List.collect (fun x ->
                let labelNext = newLabel ()
                CE vEnv fEnv (fst x)
                @ [IFZERO labelNext]
                @ CSs vEnv fEnv (snd x)
                @ [GOTO label; Label labelNext])


(* ------------------------------------------------------------------- *)

(* Build environments for global variables and functions *)
    let allocateFunction label dec fEnv =
        match dec with
            | (FunDec (tyOpt, f, decs, _))  ->
                (Map.add f (label, tyOpt, List.map (function
                    | VarDec (t, n) -> (t, n)
                    | FunDec _      -> failwith "Unsupported function passing")
                decs) <| fst fEnv, snd fEnv)
            | _                             -> failwith "Not a function"


// Map<string, Var*Typ> * int
    let makeGlobalEnvs decs =
        let rec addv decs vEnv (fEnv : funEnv) =
            match decs with
                | []         -> (vEnv, fEnv, [])
                | dec::decr  ->
                    match dec with
                        | VarDec (typ, var) -> let (vEnv1, code1) = allocate GloVar (typ, var) vEnv
                                               let (vEnv2, fEnv2, code2) = addv decr vEnv1 fEnv
                                               (vEnv2, fEnv2, code1 @ code2)
                        | FunDec (tyOpt, f, xs, body) as func ->
                            let funLabel = newLabel ()
                            let endFunc = newLabel ()
                            let fEnv1 = allocateFunction funLabel func fEnv
                            let vEnvLocal = allocateDecs vEnv xs 
                            let codeStm = CS vEnvLocal (fst fEnv1, Some f) body
                            let (vEnv2, fEnv2, code2) = addv decr vEnv fEnv1
                            let procedureEnd = 
                                if tyOpt.IsNone 
                                    then [RET (xs.Length - 1)]
                                    else []
                            (vEnv2, fEnv2, [GOTO endFunc] @ [Label funLabel] 
                                @ codeStm @ procedureEnd
                                @ [Label endFunc] @ code2)
        addv decs (Map.empty, 0) (Map.empty, None)

/// CP prog gives the code for a program prog
    let CP (P(decs,stms)) =
        let _ = resetLabels ()
        // let decsEndLabel = newLabel ()
        let ((gvM,_) as gvEnv, fEnv, initCode) = makeGlobalEnvs decs
        initCode @ CSs gvEnv fEnv stms @ [STOP]



