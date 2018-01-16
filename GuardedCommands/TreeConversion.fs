namespace GuardedCommands.Util

open GuardedCommands.Frontend.AST
open GuardedCommands.Util.TreeDrawing

module TreeConversion =

  let rec convertExpr = function
    | N n                   -> Node (string n, [])
    | B b                   -> Node (string b, [])
    | Access acc            -> Node ("Access", [convertAccess acc])
    | Addr acc              -> Node ("Addr", [convertAccess acc])
    | Apply (s, exps)       -> Node ("Apply " + s, convertExprs exps)
  and convertExprs = List.map convertExpr
  and convertAccess = function
      | AVar s          -> Node ("AVar " + s, [])
      | AIndex (acc, ex)-> Node ("AIndex", convertAccess acc :: [convertExpr ex])
      | ADeref ex       -> Node ("ADeref", [convertExpr ex])

  and convertStms = List.map convertStm
  and convertStm = function
        | PrintLn ex          -> Node ("Print", [convertExpr ex])
        | Ass (acc, ex)       -> Node ("Acc", convertAccess acc :: [convertExpr ex])
        | Return (Some ex)    -> Node ("Return", [convertExpr ex])
        | Return None         -> Node ("Return", [])
        | Alt (GC [])         -> Node ("Abort", [])
        | Alt (GC gc)         -> Node ("Alt", convertGuardedCommand gc)
        | Do (GC [])          -> Node ("Skip", [])
        | Do (GC gc)          -> Node ("Do", convertGuardedCommand gc)
        | Block (decs, stms)  -> Node ("Block", convertDecs decs @ convertStms stms)
        | Call (s, exps)      -> Node ("Call " + s, convertExprs exps)

  and convertGuardedCommand gc =
      match gc with
        | []                -> []
        | (ex, stms) :: gc' -> Node ("Guard", convertExpr ex :: convertStms stms) :: convertGuardedCommand gc'

  and convertDecs = List.map convertDec
  and convertDec = function
        | VarDec (ty, s)             -> Node ("VarDec " + s, [convertTyp ty])
        | FunDec (ty, f, decs, stm)  -> let tyNode =
                                          match ty with
                                            | None   -> Node ("None", [])
                                            | Some t -> convertTyp t
                                        Node ("FunDec " + f, tyNode :: convertDecs decs @ [convertStm stm])

  and convertTyps = List.map convertTyp
  and convertTyp = function
    | ITyp                 -> Node ("int", [])
    | BTyp                 -> Node ("bool", [])
    | ATyp (ty, n)         -> let lengthNode =
                                match n with
                                  | None     -> []
                                  | Some num -> [Node ("Length " + string num, [])]
                              Node ("Array", [convertTyp ty] @ lengthNode)
    | PTyp (ty)            -> Node ("Pointer", [convertTyp ty])
    | FTyp (tys, optTy)    -> let returnNode =
                                match optTy with
                                  | None    -> Node ("None", [])
                                  | Some t  -> convertTyp t
                              Node ("FTyp", convertTyps tys @ [returnNode])

  let convertProgram (P (decs, stms)) = Node ("Program", convertDecs decs @ convertStms stms)