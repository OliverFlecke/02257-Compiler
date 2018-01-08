namespace GuardedCommands.Frontend
// Michael R. Hansen 06-01-2016 , 04-01-2018

open System
open Machine
open GuardedCommands.Frontend.AST

module TypeCheck = 

/// tcE gtenv ltenv e gives the type for expression e on the basis of type environments gtenv and ltenv
/// for global and local variables 
   let rec tcE gtenv ltenv = function                            
         | N _              -> ITyp   
         | B _              -> BTyp   
         | Access acc       -> tcA gtenv ltenv acc     
                   
         | Apply(f,[e]) when List.exists (fun x ->  x=f) ["-"; "!"]  
                            -> tcMonadic gtenv ltenv f e        

         | Apply(f,[e1;e2]) when List.exists (fun x ->  x=f) ["+";"*"; "="; "&&"]        
                            -> tcDyadic gtenv ltenv f e1 e2   
         | Apply (f, vs)    -> 
            match Map.tryFind f gtenv with 
                | Some t    -> t
                | None      -> failwith ("Function " + string f + " is undefined")
         | x                -> failwith ("tcE: not supported yet" + string x)

   and tcMonadic gtenv ltenv f e = match (f, tcE gtenv ltenv e) with
                                   | ("-", ITyp) -> ITyp
                                   | ("!", BTyp) -> BTyp
                                   | _           -> failwith "illegal/illtyped monadic expression" 
   
   and tcDyadic gtenv ltenv f e1 e2 = match (f, tcE gtenv ltenv e1, tcE gtenv ltenv e2) with
                                      | (o, ITyp, ITyp) when List.exists (fun x ->  x=o) ["+";"*"]  -> ITyp
                                      | (o, ITyp, ITyp) when List.exists (fun x ->  x=o) ["="] -> BTyp
                                      | (o, BTyp, BTyp) when List.exists (fun x ->  x=o) ["&&";"="]     -> BTyp 
                                      | _                      -> failwith("illegal/illtyped dyadic expression: " + f)

   and tcNaryFunction gtenv ltenv f es = failwith "type check: functions not supported yet"
 
   and tcNaryProcedure gtenv ltenv f es = failwith "type check: procedures not supported yet"
      

/// tcA gtenv ltenv e gives the type for access acc on the basis of type environments gtenv and ltenv
/// for global and local variables 
   and tcA gtenv ltenv = 
         function 
         | AVar x         -> match Map.tryFind x ltenv with
                             | None   -> match Map.tryFind x gtenv with
                                         | None   -> failwith ("no declaration for : " + x)
                                         | Some t -> t
                             | Some t -> t            
         | AIndex(acc, e) -> failwith "tcA: array indexing not supported yes"
         | ADeref e       -> failwith "tcA: pointer dereferencing not supported yes"
 

/// tcS gtenv ltenv retOpt s checks the well-typeness of a statement s on the basis of type environments gtenv and ltenv
/// for global and local variables and the possible type of return expressions 
   and tcS gtenv ltenv = function                           
      | PrintLn e       -> ignore(tcE gtenv ltenv e)
      | Ass(acc,e)      -> 
         if tcA gtenv ltenv acc = tcE gtenv ltenv e 
            then ()
            else failwith "illtyped assignment"                                

      | Block([],stms)  -> List.iter (tcS gtenv ltenv) stms
      | Alt (GC gc) | Do (GC gc)    -> 
            if List.forall (fst >> tcE gtenv ltenv >> (=)BTyp) gc 
              then ()
              else failwith "tcS: If is expression, expected boolean"
      | Return e        -> Option.map (tcE gtenv ltenv) e |> ignore
      | _               -> failwith "tcS: this statement is not supported yet"

   and tcGDec gtenv = function  
      | VarDec(t,s)                 -> Map.add s t gtenv
      | FunDec(topt, f, decs, stm)  -> 
            if allUnique (List.map (function
                        | VarDec (_, n)   -> n
                        | _               -> failwith "You are not allowed to define a function here") decs) 
                  then ()
                  else failwith ("Function " + string f + " have duplicate arguments")
            let ltenv = List.fold (fun ev x -> 
                  match x with 
                        | VarDec (t, n) -> Map.add n t ev
                        | _             -> failwith "You cannot define nested function" ) gtenv decs
            let gtenv' = addFuncToEnv gtenv f topt
            tcS gtenv' ltenv stm |> ignore 
            let returnStm = List.filter (function 
                  | Return _  -> true 
                  | _         -> false) (allStatments stm)
            if (List.forall ((=)topt) (List.map (function 
                        | Return a  -> Option.map (tcE gtenv ltenv) a
                        | _         -> failwith "Impossible!") returnStm))
                  then gtenv' 
                  else failwith ("The return types in " + string f + " is not the same")
            
            
   and allUnique ls : bool = Seq.length (Seq.distinct ls) = List.length ls
   and addFuncToEnv env f = function
                        | Some ty   -> Map.add f ty env 
                        | None      -> Map.add f UnitTyp env
   and allStatments stmt : Stm list = 
      match stmt with 
            | Block (_, stmts)      -> List.collect allStatments stmts
            | x                     -> [x]
   and tcGDecs gtenv = function
                       | dec::decs -> tcGDecs (tcGDec gtenv dec) decs
                       | _         -> gtenv


/// tcP prog checks the well-typeness of a program prog
   and tcP(P(decs, stms)) = let gtenv = tcGDecs Map.empty decs
                            List.iter (tcS gtenv Map.empty) stms

  
