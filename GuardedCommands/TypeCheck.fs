namespace GuardedCommands.Frontend
// Michael R. Hansen 06-01-2016 , 04-01-2018

open System
open Machine
open GuardedCommands.Frontend.AST

module TypeCheck =

  let matchTypesFunction =
    function
      | (ATyp (ty, _), ATyp (ty', _)) when ty = ty'   -> true
      | (a, b) when a = b                             -> true
      | _                                             -> false

/// tcE env e gives the type for expression e on the basis of type environments gtenv and ltenv
/// for global and local variables
  let rec tcE env = function
    | N _              -> ITyp
    | B _              -> BTyp
    | Access acc       -> tcA env acc
    | Apply(f,[e]) when List.exists (fun x ->  x=f) ["-"; "!"]
                       -> tcMonadic env f e
    | Apply(f,[e1;e2]) when List.exists (fun x ->  x=f) ["+";"*";"/";"%";"=";"&&";"-";"<";">";"<=";">="]
                       -> tcDyadic env f e1 e2
    | Apply (f, args)  ->
      let ts = List.map (tcE env) args
      match Map.tryFind f env with
        | Some (FTyp (decTs, Some funTy)) ->
          if List.forall matchTypesFunction (List.zip ts decTs)
            then funTy
            else failwith ("Argument types for the function '"
              + string f + "' does not match the function declaration. "
              + "Expected " + string decTs + " Actual: " + string ts)
        | _                           -> failwith ("Function " + string f + " is undefined")
    | Addr x           -> PTyp (tcA env x)
    | Access acc       -> tcA env acc
    | x                -> failwith ("tcE: not supported yet" + string x)

  and tcMonadic env f e =
    match (f, tcE env e) with
      | ("-", ITyp) -> ITyp
      | ("!", BTyp) -> BTyp
      | _           -> failwith "illegal/illtyped monadic expression"

  and tcDyadic env f e1 e2 =
    match (f, tcE env e1, tcE env e2) with
      | (o, ITyp, ITyp) when List.exists ((=)o) ["+";"*";"-";"/";"%"]    -> ITyp
      | (o, ITyp, ITyp) when List.exists ((=)o) ["=";">";"<";">=";"<="]  -> BTyp
      | (o, BTyp, BTyp) when List.exists ((=)o) ["&&";"="]               -> BTyp
      | _                      -> failwith("illegal/illtyped dyadic expression: " + f)

/// tcA env e gives the type for access acc on the basis of type environments gtenv and ltenv
/// for global and local variables
  and tcA env =
    function
      | AVar x         ->
        match Map.tryFind x env with
          | None   -> failwith ("no declaration for : " + x)
          | Some t -> t
      | AIndex(acc, e) ->
        match tcE env e with
          | ITyp      -> ()
          | ty        -> failwith ("Expression on array " + string acc + " is not the expected type int. Actual type: " + string ty)
        match tcA env acc with
          | ATyp (ty, _)    -> ty
          | _               -> failwith ("Not an array")
      | ADeref e       ->
        match tcE env e with
          | PTyp t    -> t
          | _         -> failwith (string e + " is not a pointer")


/// tcS env retOpt s checks the well-typeness of a statement s on the basis of type environments gtenv and ltenv
/// for global and local variables and the possible type of return expressions
  and tcS env ftyp = function
      | PrintLn e       -> ignore(tcE env e)
      | Ass(acc,e)      ->
        if tcA env acc = tcE env e
          then ()
          else failwith "illtyped assignment"

      | Block(decs, stms)           ->
        let env' = List.fold (fun e ->
          function
            | VarDec (t, n) -> Map.add n t e
            | _             -> failwith "tcS Block: Not supported") env decs
        List.iter (tcS env' ftyp) stms
      | Alt (GC gc) | Do (GC gc)    ->
        if List.forall (fst >> tcE env >> (=)BTyp) gc
          then List.iter (snd >> List.iter (tcS env ftyp)) gc
          else failwith "tcS: If is expression, expected boolean"
      | Return e        ->
        if Option.map (tcE env) e = ftyp
          then ()
          else failwith "Return type is different from function type"
      | Call (p, args)  ->
        let ts = List.map (tcE env) args
        match Map.tryFind p env with
          | Some (FTyp (decTs, None)) ->
            if List.forall matchTypesFunction (List.zip ts decTs)
              then ()
              else failwith ("Argument types for the procedure "
                        + string p + " does not match the procedure declaration" +
                        "Expeced: " + string decTs + ", Actual: " + string ts + " Args: " + string args)
          | _                     -> failwith ("Procedure " + string p + " is undefined")
      // | _               -> failwith "tcS: this statement is not supported yet"

  and tcGDec env = function
      | VarDec(t,s)                 -> Map.add s t env
      | FunDec(topt, f, decs, stm)  ->
        if allUnique (List.map (function
                                | VarDec (_, n)   -> n
                                | _               -> failwith "You are not allowed to define a function here") decs)
          then ()
          else failwith ("Function " + string f + " have duplicate arguments")
        let env' = addFuncToEnv f topt decs env
        let localEnv = List.fold (fun ev x ->
          match x with
          | VarDec (t, n) -> Map.add n t ev
          | _             -> failwith "You cannot define nested function" ) env' decs
        tcS localEnv topt stm |> ignore
        env'

  and allUnique ls : bool = Seq.length (Seq.distinct ls) = List.length ls
  and addFuncToEnv f topt decs = Map.add f (FTyp (List.map decsToTyps decs, topt))
  and decsToTyps =
    function
      | VarDec (t, _)         -> t
      | FunDec (t, _, ds, _)  -> FTyp (List.map decsToTyps ds, t)
  and allStatments stmt : Stm list =
    match stmt with
      | Block (_, stmts)      -> List.collect allStatments stmts
      | x                     -> [x]
  and tcGDecs env =
    function
      | dec::decs -> tcGDecs (tcGDec env dec) decs
      | _         -> env

/// tcP prog checks the well-typeness of a program prog
  and tcP(P(decs, stms)) =
    let env = tcGDecs Map.empty decs
    List.iter (tcS env None) stms
