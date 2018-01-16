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

  let splitString (str : string) = Array.toList <| str.Split([|' '|], StringSplitOptions.None)

  // Compute depth
  type Depth = int
  type MaxMap = Map<Depth,int>

  let depthTree tree =
    let rec depthTree' tree =
      let mapper (Node((l, _), ns)) = Node (List.length (splitString l), depthTree' ns)
       in List.map mapper tree
    List.head <| depthTree' [tree]

  let rec fold f acc = function
    | Node (label, ts) ->
      let acc' = f acc (Node (label, ts))
      let acc'' = Seq.fold (fold f) acc' ts
      acc''

  // Alternative name: LayerwiseFold
  let rec depthawareFold f (acc, d) = function
    | Node (label, ts) ->
      let (acc', d') = f (acc, d) (Node (label, ts))
      let (acc'', _) = Seq.fold (depthawareFold f) (acc', d') ts
      (acc'', d)

  let layerWiseMax =
    let folder ((maxMap, d) : MaxMap * Depth) (Node (label, _)) =
      let maxMap' =
        match maxMap.TryFind d with
          | Some a when label > a -> maxMap.Add (d, label)
          | None                  -> maxMap.Add (d, label)
          | _                     -> maxMap
      (maxMap', d + 1)
    depthawareFold folder (Map.empty, 0)

  // Helper functions
  let rmoveto (x : float) (y : float) = string (100.0 * x) + " " + string -y + " rmoveto"
  let rlineto (x : float) (y : float) = string (100.0 * x) + " " + string -y + " rlineto"

  let getPos (Node ((_, pos), _)) = pos

  // Drawing functions
  let rec drawChild depthMap depth t = rlineto 0.0 20.0 :: drawNode depthMap (depth + 1) t @ [rmoveto 0.0 -20.0]
  and nextChild x = [rmoveto x 0.0]

  and drawNode depthMap depth t : string list =
    match t with
      | Node ((l : string, _), nodes) ->
        let lines = splitString l
        let spacing = (Map.find depth depthMap) - lines.Length
        let label = List.map (fun x -> "0 -20 rmoveto (" + string x + ") dup stringwidth pop 2 div neg dup 0 rmoveto exch show 0 rmoveto") lines
        let drawing =
          match nodes with
            | []  -> []
            | _   ->
              let positions = List.map (float << getPos) nodes
              let pos = List.head positions
              let diffs = List.map (abs << uncurry (-)) (List.pairwise positions)
              let children = drawChild depthMap depth (List.head nodes) @ List.collect (fun (x, t) -> nextChild x @ drawChild depthMap depth t) (List.zip diffs (List.tail nodes))
              rlineto 0.0 10.0 :: [rmoveto -pos 0.0; rlineto (2.0 * pos) 0.0;]
                @ children @ [rmoveto pos -10.0]
        label @ [rmoveto 0.0 8.0]
          @ if spacing > 0 && not nodes.IsEmpty then List.replicate spacing (rlineto 0.0 20.0) else []
          @ drawing
          @ if spacing > 0 && not nodes.IsEmpty then List.replicate spacing (rmoveto 0.0 -20.0) else []
          @ [rmoveto 0.0 (-8.0 + -20.0 * (float label.Length))]

  and drawTree (tree : Tree<string>) =
    let filename = "post.ps"
    let designTree = design tree
    let depthMap = layerWiseMax <| depthTree designTree
    // let left' = depthawareFold (fun (a, d) (Node ((_, v), _)) -> (min a (v + d), v + d)) (0.0, 0.0) designTree
    let left = computeBound min [designTree]
    // let right' = depthawareFold (fun (a, d) (Node ((_, v), _)) -> (max a (v + d), v + d)) (0.0, 0.0) designTree
    let right = computeBound max [designTree]
    let width = 55.0 * (right - left)
    let height = 100 * (depth designTree)
    File.WriteAllLines(filename, ["%!PS"])
    File.AppendAllText(filename, "% Compile to PDF with:\n")
    File.AppendAllText(filename, "% gs -sDEVICE=pdfwrite -dDEVICEWIDTHPOINTS=" + string (2.0 * width) + " -dDEVICEHEIGHTPOINTS=" + string height + " -dPDFFitPage -o output.pdf " + filename + "\n")
    File.AppendAllLines(filename, ["/Courier";"20 selectfont"])
    File.AppendAllText(filename, string width + " " + string height + " moveto\n")
    File.AppendAllLines(filename, drawNode (fst depthMap) 0 designTree)
    File.AppendAllLines(filename, ["stroke"; "showpage"])
    ()
  and computeBound f tree =
    match tree with
      | []                              -> 0.0
      | Node ((_, v), [])       :: rest -> f v (computeBound f rest)
      | Node ((_, v), children) :: rest -> f (v + computeBound f children) (computeBound f rest)
  and depth tree =
    let rec depth' d tree =
      match tree with
        | []                 -> d
        | Node (_, ns) :: rs -> max (depth' (d + 1) ns) (depth' d rs)
    depth' 0 [tree]
