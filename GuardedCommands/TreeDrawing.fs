namespace GuardedCommands.Util

open System.IO

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

  let rmoveto (x : float) (y : float) = string (100.0 * x) + " " + string -y + " rmoveto"
  let rlineto (x : float) (y : float) = string (100.0 * x) + " " + string -y + " rlineto"

  let getPos (Node ((_, pos), _)) = pos

  let rec drawChild t = rlineto 0.0 20.0 :: drawNode t @ [rmoveto 0.0 -20.0]
  and nextChild x = [rmoveto x 0.0]

  and drawNode t : string list =
    match t with
      | Node ((l, v), ls) ->
        let s = "(" + string l + ") dup stringwidth pop 2 div neg dup 0 rmoveto exch show 0 rmoveto"
        let drawing =
          match ls with
            | []  -> []
            | _   ->
              let positions = List.map (float << getPos) ls
              let pos = List.head positions
              let diffs = List.map (abs << uncurry (-)) (List.pairwise positions)
              let children = drawChild (List.head ls) @ List.collect (fun (x, t) -> nextChild x @ drawChild t) (List.zip diffs (List.tail ls))
              rlineto 0.0 10.0 :: [rmoveto -pos 0.0; rlineto (2.0 * pos) 0.0;]
                @ children
                @ [rmoveto pos -10.0]
        s :: drawing

  and drawTree (tree : Tree<string>) =
    let filename = "post.ps"
    File.WriteAllText(filename, "%!PS
/Courier
20 selectfont
300 750 moveto\n")
    File.AppendAllLines(filename, drawNode <| design tree)
    File.AppendAllLines(filename, ["stroke"; "showpage"])
    ()