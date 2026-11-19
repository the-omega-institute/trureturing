/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyTwoPairedPlacements
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyTwoPairedPlacements
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyTwoPairedExclusion.no_twenty_two_half; instance=D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyTwoPairedExclusion.no_twenty_two_half
   digest: Check all paired placements for an excess-degree vertex after parity reconstruction. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonPlacements

/-! Enumerate the rooted embeddings of the two complete bipartite
compressions joined by the three matched edges. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedPlacements

open private adjacent hasTwoSetBits moves toggle from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeBitMoves
open private labels middleOptions fillMiddles neighborMask from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonPlacements

private abbrev Vertex := BitVec 9
private abbrev Placement := Fin 10 → Vertex

private def solidEdges : List (Fin 10 × Fin 10) := [(0, 7), (3, 8), (4, 9)]

private def hollowEdges : List (Fin 10 × Fin 10) :=
  [(0, 1), (0, 2), (1, 3), (1, 4), (2, 3), (2, 4),
    (5, 7), (5, 8), (5, 9), (6, 7), (6, 8), (6, 9)]

private def valid (placed : List (Fin 10)) (p : Placement) : Bool :=
  placed.all fun i => placed.all fun j =>
    if i < j then
      p i != p j && (adjacent (p i) (p j) == solidEdges.contains (i, j)) &&
        (!hollowEdges.contains (i, j) ||
          (hasTwoSetBits (p i ^^^ p j) && !(middleOptions placed p i j).isEmpty))
    else true

private def seed (sameAxis : Bool) : Placement :=
  ![0, 18, if sameAxis then 20 else 36, 0, 0, 0, 0, 8, 0, 0]

private def searchOrder : List (Fin 10 × Fin 10 × Bool) :=
  [(3, 1, false), (4, 1, false), (8, 3, true), (5, 7, false), (9, 4, true), (6, 7, false)]

private def stepOptions (p : Vertex) (solid : Bool) : List Vertex :=
  if solid then (List.finRange 8).map fun a => toggle p a.succ else moves p

private def highPlacements (placed : List (Fin 10)) (p : Placement) :
    List (Fin 10 × Fin 10 × Bool) → List Placement
  | [] => [p]
  | (i, anchor, solid) :: rest =>
    (stepOptions (p anchor) solid).flatMap fun x =>
      let q := Function.update p i x
      if !x.getLsbD 0 && valid (i :: placed) q then
        highPlacements (i :: placed) q rest
      else []

private def highCandidates (sameAxis : Bool) : List Placement :=
  highPlacements [0, 1, 2, 7] (seed sameAxis) searchOrder

private def candidates (sameAxis : Bool) : List (List Vertex) :=
  (highCandidates sameAxis).flatMap fun p =>
    fillMiddles p [] hollowEdges |>.map fun mids => mids ++ labels.map p

private def reconstructedMask (half : List Vertex) : Nat :=
  half.foldl (fun mask x => mask ^^^ neighborMask x) 0

private def hasExcessDegree (half : List Vertex) : Bool :=
  let other := reconstructedMask half
  (List.range 256).any fun i =>
    let x := BitVec.ofNat 9 (2 * i)
    other.testBit i &&
      decide (3 < (half.contains x).toNat +
        (List.finRange 8).countP (fun a => other.testBit ((toggle x a.succ).toNat / 2)))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 18000000 in
-- The two seeds account for whether the second axes of the root paths agree.
-- All completed branches have an excess-degree vertex in the reconstructed half.
private theorem checked (sameAxis : Bool) :
    (candidates sameAxis).all hasExcessDegree = true := by
  cases sameAxis <;> decide +kernel

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedPlacements
