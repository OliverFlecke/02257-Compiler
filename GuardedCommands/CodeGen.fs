﻿namespace GuardedCommands.Backend
// Michael R. Hansen 05-01-2016, 04-01-2018
// This file is obtained by an adaption of the file MicroC/Comp.fs by Peter Sestoft
open Machine
open GuardedCommands.Frontend.AST

module CodeGeneration =

// Optimizations
    let rec addINCSP m1 C : instr list =
        match C with
            | INCSP m2            :: C1 -> addINCSP (m1+m2) C1
            | RET m2              :: C1 -> RET (m2-m1) :: C1
            | Label lab :: RET m2 :: _  -> RET (m2-m1) :: C
            | _                         -> if m1=0 then C else INCSP m1 :: C

    let addLabel C : label * instr list =          (* Conditional jump to C *)
        match C with
            | Label lab :: _ -> (lab, C)
            | GOTO lab :: _  -> (lab, C)
            | _              -> let lab = newLabel()
                                (lab, Label lab :: C)

    let makeJump C : instr * instr list =          (* Unconditional jump to C *)
        match C with
            | RET m              :: _ -> (RET m, C)
            | Label _ :: RET m   :: _ -> (RET m, C)
            | Label lab          :: _ -> (GOTO lab, C)
            | GOTO lab           :: _ -> (GOTO lab, C)
            | _                       -> let lab = newLabel()
                                         (GOTO lab, Label lab :: C)

    let makeCall m lab C : instr list =
        match C with
            | RET n            :: C1 -> TCALL(m, n, lab) :: C1
            | Label _ :: RET n :: _  -> TCALL(m, n, lab) :: C
            | _                      -> CALL(m, lab) :: C

    let rec deadcode C =
        match C with
            | []              -> []
            | Label lab :: _  -> C
            | _         :: C1 -> deadcode C1

    let addNOT C =
        match C with
            | NOT        :: C1 -> C1
            | IFZERO lab :: C1 -> IFNZRO lab :: C1
            | IFNZRO lab :: C1 -> IFZERO lab :: C1
            | _                -> NOT :: C

    let addJump jump C =                    (* jump is GOTO or RET *)
        let C1 = deadcode C
        match (jump, C1) with
        | (GOTO lab1, Label lab2 :: _) when lab1 = lab2 ->         C1
        | _                                             -> jump :: C1

    let addGOTO lab C = addJump (GOTO lab) C

    let rec addCST i C =
        match (i, C) with
            | (0, ADD        :: C1) -> C1
            | (0, SUB        :: C1) -> C1
            | (0, NOT        :: C1) -> addCST 1 C1
            | (_, NOT        :: C1) -> addCST 0 C1
            | (1, MUL        :: C1) -> C1
            | (1, DIV        :: C1) -> C1
            | (0, EQ         :: C1) -> addNOT C1
            | (_, INCSP m    :: C1) -> if m < 0 then addINCSP (m+1) C1
                                       else CSTI i :: C
            | (0, IFZERO lab :: C1) -> addGOTO lab C1
            | (_, IFZERO _   :: C1) -> C1
            | (0, IFNZRO _   :: C1) -> C1
            | (_, IFNZRO lab :: C1) -> addGOTO lab C1
            | _                     -> CSTI i :: C


(* A global variable has an absolute address, a local one has an offset: *)
    type Var =
        | GloVar of int                   (* absolute address in stack           *)
        | LocVar of int                   (* address relative to bottom of frame *)

(* The variable environment keeps track of global and local variables, and
   keeps track of next available offset for local variables *)

    type VarEnv = Map<string, Var*Typ> * int

(* The function environment maps function name to label and parameter decs *)
    type Name = string
    type ParamDecs = (Typ * string) list
    type FunEnv = Map<Name, label * Typ option * ParamDecs> * Name option


    let allocateDecs vEnv decs = List.fold (fun env ->
        function
            | (VarDec (t, n))   -> (Map.add n (LocVar (snd env), t) <| fst env, snd env + 1)
            | _                 -> failwith "Not supported") (fst vEnv, 0) decs

    let binaryOperators = ["+";"*";"/";"%";"=";"-";">";"<";">=";"<="]
/// CE vEnv fEnv e gives the code for an expression e on the basis of a variable and a function environment
    let rec CE vEnv fEnv expr k =
        match expr with
            | N n                   -> addCST n k
            | B b                   -> addCST (if b then 1 else 0) k
            | Access acc            -> CA vEnv fEnv acc (LDI :: k)
            | Apply("-", [e])       -> CE vEnv fEnv e (addCST 0 (SWAP :: SUB :: k))
            | Apply("!", [e])       -> addNOT (CE vEnv fEnv e k)
            | Apply("&&",[b1;b2])   -> let labend   = newLabel()
                                       let labfalse = newLabel()
                                       CE vEnv fEnv b1 ([IFZERO labfalse]
                                       @ CE vEnv fEnv b2 ([GOTO labend; Label labfalse; CSTI 0; Label labend] @ k))
            | Apply(o,[e1;e2]) when List.exists ((=)o) binaryOperators ->
                let ins =
                    match o with
                        | "+"     -> [ADD]
                        | "*"     -> [MUL]
                        | "/"     -> [DIV]
                        | "%"     -> [MOD]
                        | "="     -> [EQ]
                        | "-"     -> [SUB]
                        | "<"     -> [LT]
                        | ">"     -> [SWAP; LT]
                        | "<="    -> [CSTI 1; ADD; LT]
                        | ">="    -> [CSTI 1; SUB; SWAP; LT]
                        | op      -> failwith ("CE: the operator '" + op + "' is not supported")
                CE vEnv fEnv e1 (CE vEnv fEnv e2 (ins @ k))
            | Apply (f, es)     ->
                let (label, _, _) = Map.find f (fst fEnv)
                List.fold (fun k' e -> CE vEnv fEnv e k') (makeCall es.Length label k) (List.rev es)
            | Addr x            -> CA vEnv fEnv x k
            | x                 -> failwith ("CE: not ssupported yet " + string x)


/// CA vEnv fEnv acc gives the code for an access acc on the basis of a variable and a function environment
    and CA vEnv fEnv acc k =
        match acc with
            | AVar x         ->
                match Map.tryFind x (fst vEnv) with
                    | Some (GloVar addr,_)  -> [CSTI addr] @ k
                    | Some (LocVar addr,_)  -> [GETBP; CSTI addr; ADD] @ k
                    | None                  -> failwith ("Unable to find " + x)
            | AIndex(acc, e) -> CA vEnv fEnv acc ([LDI] @ CE vEnv fEnv e ([ADD] @ k))
            | ADeref e       -> CE vEnv fEnv e k


(* Bind declared variable in env and generate code to allocate it: *)
    let rec allocate (kind : int -> Var) (typ, x) (vEnv : VarEnv)  =
        let (env, fdepth) = vEnv
        match typ with
            | ATyp (ATyp _, _) -> raise (Failure "allocate: array of arrays not permitted")
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
    let rec CS (vEnv : VarEnv) (fEnv : FunEnv) (stm : Stm) (k : instr list) =
        match stm with
            | PrintLn e         -> CE vEnv fEnv e ([PRINTI; INCSP -1] @ k)
            | Ass(acc,e)        -> CA vEnv fEnv acc (CE vEnv fEnv e ([STI; INCSP -1] @ k))
            | Block(decs, stms)    ->
                let (vEnv', decsCode) = List.fold (fun (env, code) ->
                    function
                        | VarDec (t,n)  ->
                            let kind = if (snd fEnv).IsNone then GloVar else LocVar
                            let (env', code') = allocate kind (t, n) env
                            (env', code @ code')
                        | _             -> failwith "Cs: function not supported in local declaration") (vEnv, []) decs
                decsCode @ CSs vEnv' fEnv stms ([INCSP -(decsLength decs)] @ k)
            | Alt (GC gc)       ->
                let labelEnd = newLabel ()
                guardStm labelEnd vEnv fEnv gc ([CSTI -1; PRINTI; STOP; Label labelEnd] @ k)
            | Do (GC gc)        ->
                let labelStart = newLabel ()
                [Label labelStart] @ guardStm labelStart vEnv fEnv gc k
            | Return e ->
                let k' = [RET (snd vEnv)] @ k
                match e with
                    | Some exp  -> CE vEnv fEnv exp k'
                    | None      -> k'
            | Call (p, exprs)       ->
                let (label, _, _) = Map.find p (fst fEnv)
                List.fold (fun k' e -> CE vEnv fEnv e k') ([CALL ((exprs.Length), label); INCSP -1] @ k) (List.rev exprs)

    and CSs vEnv fEnv stms k = List.fold (fun k' s -> CS vEnv fEnv s k') k (List.rev stms)
    and guardStm label vEnv fEnv gc k =
        List.fold (fun k' x ->
            let labelNext = newLabel ()
            CE vEnv fEnv (fst x) ([IFZERO labelNext] @ CSs vEnv fEnv (snd x) ([GOTO label; Label labelNext] @ k'))) k (List.rev gc)

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
        let rec addv decs vEnv (fEnv : FunEnv) =
            match decs with
                | []         -> (vEnv, fEnv, [])
                | dec::decr  ->
                    match dec with
                        | VarDec (typ, var) -> let (vEnv1, code1) = allocate GloVar (typ, var) vEnv
                                               let (vEnv2, fEnv2, code2) = addv decr vEnv1 fEnv
                                               (vEnv2, fEnv2, code1 @ code2)
                        | FunDec (tyOpt, f, decs', body) as func ->
                            let funLabel = newLabel ()
                            let endFunc = newLabel ()
                            let fEnv1 = allocateFunction funLabel func fEnv
                            let vEnvLocal = allocateDecs vEnv decs'
                            let codeStm = CS vEnvLocal (fst fEnv1, Some f) body []
                            let (vEnv2, fEnv2, code2) = addv decr vEnv fEnv1
                            let procedureEnd =
                                if tyOpt.IsNone
                                    then [RET (decs'.Length - 1)]
                                    else []
                            (vEnv2, fEnv2, [GOTO endFunc] @ [Label funLabel]
                                @ codeStm @ procedureEnd
                                @ [Label endFunc] @ code2)
        addv decs (Map.empty, 0) (Map.empty, None)

    let optionToList = function
        | Some a -> [a]
        | None   -> []

    type ConstantValue = Num of int | Bool of bool
    type VarState = UnAssigned | Mutable | Constant
    type EnvIsConst = Map<string, VarState>
    type Env = Map<string, ConstantValue>

    let rec checkExp (env : EnvIsConst) expr : bool =
        match expr with
            | N _ | B _         -> true
            | Access (AVar acc) ->
                match Map.tryFind acc env with
                    | None              -> true
                    | Some Constant     -> true
                    | _                 -> false
            | Apply(f,[e]) when List.exists ((=)f) ["-"; "!"]
                -> checkExp env e
            | Apply(f,[e1;e2]) when List.exists ((=)f) binaryOperators
                -> checkExp env e1 && checkExp env e2
            | _                 -> false
    and checkForAddr env =
        function
            | Apply (_, es)     -> List.fold checkForAddr env es
            | Addr (AVar acc)   -> Map.add acc Mutable env
            | Addr acc          -> checkForAddrAcccess env acc
            | Access acc        -> checkForAddrAcccess env acc
            | _                 -> env
    and checkForAddrAcccess env =
        function
            | AIndex (acc, e)       -> checkForAddr (checkForAddrAcccess env acc) e
            | ADeref e              -> checkForAddr env e
            | AVar _                -> env
    and checkStm (env :EnvIsConst) (stm : Stm) : EnvIsConst =
        match stm with
            | PrintLn e                     -> checkForAddr env e
            | Return (Some e)               -> checkForAddr env e
            | Call (_, es)                  -> List.fold checkForAddr env es
            | Do (GC gc)
            | Alt (GC gc)                   ->
                List.fold (fun env' (e, stms) -> checkStms (checkForAddr env' e) stms) env gc
            | Ass (AVar acc, e)             ->
                let env' = checkForAddr env e
                match Map.tryFind acc env' with
                    | None
                    | Some Mutable      -> env'
                    | Some Constant     -> Map.add acc Mutable env'
                    | Some UnAssigned   ->
                        if checkExp env' e
                            then Map.add acc Constant env'
                            else Map.add acc Mutable env'
            | Ass (acc, e)                  -> checkForAddrAcccess (checkForAddr env e) acc
            | Block (decs, stms)            ->
                let localEnv = createBlockEnv decs
                let globalEnv = Map.filter (fun k _ -> not <| Map.containsKey k localEnv) env
                checkStms globalEnv stms
            | Return None                   -> env

    and checkStms = List.fold checkStm
    and createBlockEnv =
        let folder env =
            function
                | VarDec (_, s)             -> Map.add s UnAssigned env
                | FunDec (_, _, ds, stm)    -> let env' = checkBlock ds [stm]
                                               Map.map (fun _ _ -> Mutable) env'
         in List.fold folder Map.empty
    and checkBlock decs stms =
        let env : EnvIsConst = createBlockEnv decs
        checkStms env stms

    let rec optBlock decs stms =
        let env = Map.filter (fun _ v -> v = Constant) (checkBlock decs stms)
        let envValue = List.fold (fun envValue' dec ->
            match dec with
                | VarDec (ty, s) ->
                    match Map.tryFind s env with
                        | Some Constant ->
                            match ty with
                                | ITyp  -> Map.add s (Num 0) envValue'
                                | BTyp  -> Map.add s (Bool false) envValue'
                                | _     -> failwith "Should not be possible"
                        | _             -> envValue'
                | _             -> envValue') Map.empty decs
        let (_, stms') = optimize envValue stms
        let predicate x = match x with
                            | VarDec (_, s)     -> not <| Map.containsKey s env
                            | _                 -> true
         in let decs' = List.filter predicate decs
            (decs', stms')
    and optStm env stm =
        match stm with
            | PrintLn e          -> (env, Some <| PrintLn (optExpr env e))
            | Return (Some e)    -> (env, Some <| Return (Some (optExpr env e)))
            | Return None        -> (env, Some <| Return None)
            | Ass (AVar a, e)    -> let e' = optExpr env e
                                    match Map.tryFind a env with
                                        | Some _         ->
                                            let env' =
                                                match e' with
                                                    | N n   -> Map.add a (Num n) env
                                                    | B b   -> Map.add a (Bool b) env
                                                    | x     -> failwith ("Impossible: Assumed checked environment. Expected constant, actual: " + string x)
                                            (env', None)
                                        | None           -> (env, Some <| Ass (AVar a, e'))
            | Ass (acc, e)       -> (env, Some <| Ass (optAcc env acc, optExpr env e))
            | Do (GC gc)         -> let (env', gc') = optGuard env gc
                                    (env', Some <| Do (GC gc')) 
            | Alt (GC gc)        -> let (env', gc') = optGuard env gc
                                    (env', Some <| Alt (GC gc'))
            | Block (decs, stms) -> let (env', stms') = optimize env stms
                                    (env', Some <| Block (decs, stms'))
            | Call (f, es)       -> let es' = List.map (optExpr env) es
                                    (env, Some <| Call (f, es'))
    and optGuard env gc = 
        let folder (env', gc') (e, stms) =
            let (env'', stms') = optimize env' stms
            let e'             = optExpr env'' e
            (env'', (e', stms') :: gc')
         in let (newEnv, newGc) = List.fold folder (env, []) (List.rev gc)
            (newEnv, newGc)
    and optAcc env acc =
        match acc with
            | AVar s            -> AVar s
            | AIndex (acc, e)   -> AIndex (optAcc env acc, optExpr env e)
            | ADeref e          -> ADeref (optExpr env e)


    and mapBinaryIntOp (operator : string) : int -> int -> int =
        match operator with
            | "+"   -> (+)
            | "*"   -> (*)
            | "/"   -> (/)
            | "%"   -> (%)
            | "-"   -> (-)
            | _     -> failwith "Impossible: Operator not supported"
    and mapBinaryIntToBoolOp =
        function
            | ">"   -> (>)
            | "<"   -> (<)
            | ">="  -> (>=)
            | "<="  -> (<=)
            | _     -> failwith ("Impossible: Operator not supported")
    and mapBinaryBoolOp (operator : string) =
        match operator with
            | "&&"  -> (&&)
            | "="   -> (=)
            | _     -> failwith ("Impossible: Operator " + operator + " is not supported on booleans")

    and optExpr env (expr : Exp) =
        match expr with
            | N n                -> N n
            | B b                -> B b
            | Access (AVar acc)  -> match Map.tryFind acc env with
                                        | Some (Bool b)     -> B b
                                        | Some (Num n)      -> N n
                                        | _                 -> Access (AVar acc)
            | Addr acc          -> Addr (optAcc env acc)
            | Apply(f,[e]) when List.exists ((=)f) ["-"; "!"] ->
                let e' = optExpr env e
                match e' with
                    | N n   -> N (-n)
                    | B b   -> B (not b)
                    | _     -> Apply(f, [e'])
            | Apply(f,[e1;e2]) when List.exists ((=)f) binaryOperators ->
                let e1' = optExpr env e1
                let e2' = optExpr env e2
                match f with
                    | "+" | "*" | "-" | "/" | "%" -> match (e1', e2') with
                                                        | (N n1, N n2)  -> N ((mapBinaryIntOp f) n1 n2)
                                                        | _             -> Apply(f, [e1';e2'])
                    | "<" | ">" | "<=" | ">="     -> match (e1', e2') with
                                                        | (N n1, N n2)  -> B ((mapBinaryIntToBoolOp f) n1 n2)
                                                        | _             -> Apply(f, [e1';e2'])
                    | "=" | "&&"                  -> match (e1', e2') with
                                                        | (B b1, B b2)  -> B ((mapBinaryBoolOp f) b1 b2)
                                                        | _             -> Apply(f, [e1';e2'])
                    | _                           -> failwith ("Impossible")
            | Apply (s, es)     -> Apply (s, List.map (optExpr env) es)
            | _                  -> expr

    and optimize env = function
            | Block (ds, ss) :: tailStms -> let (env', ss') = optimize env ss
                                            let (ds'', ss'') = optBlock ds ss'
                                            let (env'', tailStms') = optimize env' tailStms
                                            (env'', Block (ds'', ss'') :: tailStms')
            | a              :: tailStms -> let (env', s) = optStm env a
                                            let (env'', tailStms') = optimize env' tailStms
                                            (env'', optionToList s @ tailStms')
            | []                         -> (env, [])

/// CP prog gives the code for a program prog
    let CP (P(decs,stms)) =
        let _ = resetLabels ()
        let (decs', stms') = optBlock decs stms
        System.Console.WriteLine "Optimization done."
        let ((gvM,_) as gvEnv, fEnv, initCode) = makeGlobalEnvs decs'
        initCode @ CSs gvEnv fEnv stms' [STOP]
