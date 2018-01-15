namespace GuardedCommands.Util

open System.IO
open System

module TreeDrawing =

  let curry f a b = f (a, b)
  let uncurry f (a, b) = f a b

  type Tree<'a> = Node of 'a * Tree<'a> list

  type Extent = (float * float) list

  let moveTree (Node ((label, x), subtrees)) x' = 
    Node((label, x + x'), subtrees)

  let moveExtent (e : Extent) x = List.map (fun (l, r) -> (l + x, r + x)) e

  let rec merge = curry <| function 
      | ([], qs')                -> qs'
      | (ps', [])                -> ps'
      | ((p,_)::ps', (_,q)::qs') -> (p, q) :: merge ps' qs'

  let mergeList es = List.fold merge [] es

  let rmax (p : float) (q : float) = if p > q then p else q

  let rec fit ps qs =
    match (ps, qs) with
      | ((_,p) :: ps), ((q,_)::qs) -> rmax (fit ps qs) (p - q + 1.0)
      | _                          -> 0.0

  let fitListL es =
    let rec fitListL' acc ls = 
      match (acc, ls) with 
        | (_, [])        -> []
        | (acc, (e::es)) ->
          let x = fit acc e
           in x :: fitListL' (merge acc (moveExtent e x)) es
     in fitListL' [] es

  // let rec fitListR es =
  //   let rec fitListR' = curry <| function 
  //     | (_, [])        -> []
  //     | (acc, (e::es)) ->
  //     let x = -(fit e acc)
  //      in x :: fitListR' (merge (moveExtent e x) acc) es
  //    in List.rev (fitListR' [] (List.rev es))

  let flipExtent : Extent -> Extent = List.map (fun (p, q) -> (-q, -p))
  let neg x = -x
  let fitListR = List.rev << List.map neg << fitListL << List.map flipExtent << List.rev

  let mean (x, y) = (x + y) / 2.0
  let fitlist es = List.map mean (List.zip (fitListL es) (fitListR es))

  let rec design' (Node (label, subtrees)) =
    let (trees, extents) = List.unzip (List.map design' subtrees)
    let positions = fitlist extents
    let ptrees = List.map (uncurry moveTree) (List.zip trees positions)
    let pextents = List.map (uncurry moveExtent) (List.zip extents positions)
    let resultextent = (0.0, 0.0) :: mergeList pextents
    let resulttree = Node ((label, 0.0), ptrees)
    (resulttree, resultextent)

  let design tree = fst (design' tree)

  let rmoveto x y = string (100 * x) + " " + string -y + " rmoveto" 
  let rlineto x y = string (100 * x) + " " + string -y + " rlineto"

  let getPos =
    function
      | Node ((_, pos), _) -> pos
      | _                  -> failwith "BOOM"
  let drawTree (tree : Tree<string>) =
    let filename = "post.ps"
    let rec drawTree' t : string list = 
      match t with
        | Node ((l, v), ls) -> 
          let s = "(" + string l + ") show"
          let pos = int <| getPos (List.head ls)
          s :: rlineto 0 10 :: [rmoveto pos 0; rlineto (2 * -pos) 0]
    File.WriteAllText(filename, "%!PS
    /Courier
    20 selectfont
    300 750 moveto\n")
    File.AppendAllLines(filename, drawTree' <| design tree)
    File.AppendAllLines(filename, ["stroke"; "showpage"])
    ()