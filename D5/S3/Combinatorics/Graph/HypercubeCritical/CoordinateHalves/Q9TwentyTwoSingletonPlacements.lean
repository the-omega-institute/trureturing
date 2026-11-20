/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyTwoSingletonPlacements
   generality: G
   mirror-B: none(waiver:covered-by-q9-twenty-two-paired-exclusion-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.BitVec]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyTwoPairedExclusion.no_twenty_two_half; instance=D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyTwoPairedExclusion.no_twenty_two_half
   digest: Check the reconstructed sizes of normalized singleton placements. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeBitMoves

/-! Coordinate embeddings of the two six-cycle configurations with a singleton
parity class. The root and its three solid neighbors occupy 0, 2, 4, 8. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonPlacements

open private adjacent hasTwoSetBits moves toggle from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeBitMoves

private abbrev Vertex := BitVec 9
private abbrev Placement := Fin 10 → Vertex

private def attachment (opposite : Bool) (i : Fin 6) : Fin 10 :=
  (if opposite then ![1, 2, 3, 1, 2, 3] else ![1, 2, 1, 3, 2, 3]) i

private def solid (i j : Fin 10) : Bool :=
  (i == 0 && decide (1 ≤ j.val ∧ j.val ≤ 3)) ||
  (j == 0 && decide (1 ≤ i.val ∧ i.val ≤ 3))

private def hollow (opposite : Bool) (i j : Fin 10) : Bool :=
  if hi : 4 ≤ i.val then
    if hj : 4 ≤ j.val then
      let gap := max i.val j.val - min i.val j.val
      gap == 1 || gap == 5
    else attachment opposite ⟨i.val - 4, by omega⟩ == j
  else if hj : 4 ≤ j.val then attachment opposite ⟨j.val - 4, by omega⟩ == i else false

private def middleOptions (placed : List (Fin 10)) (p : Placement)
    (i j : Fin 10) : List Vertex :=
  ((List.finRange 8).map (fun a => toggle (p i) a.succ)).filter fun x =>
    placed.all fun k => adjacent x (p k) == (k == i || k == j)

private def valid (opposite : Bool) (placed : List (Fin 10)) (p : Placement) : Bool :=
  placed.all fun i => placed.all fun j =>
    if i < j then
      p i != p j && (adjacent (p i) (p j) == solid i j) &&
        (!hollow opposite i j ||
          (hasTwoSetBits (p i ^^^ p j) && !(middleOptions placed p i j).isEmpty))
    else true

private def root : Placement := ![0, 2, 4, 8, 0, 0, 0, 0, 0, 0]

private def cycleVertices : List (Fin 6) := List.finRange 6

-- Permutations of axes 4 through 8 fix all four initial vertices.
private def firstPointAxes (x : Vertex) : Bool :=
  [0, 1, 3].contains (x.toNat / 16)

private def highPlacements (opposite : Bool)
    (placed : List (Fin 10)) (p : Placement) : List (Fin 6) → List Placement
  | [] => [p]
  | c :: rest =>
    let i : Fin 10 := ⟨c.val + 4, by omega⟩
    (moves (p (attachment opposite c))).flatMap fun x =>
      let q := Function.update p i x
      if !x.getLsbD 0 && (c != 0 || firstPointAxes x) && valid opposite (i :: placed) q then
        highPlacements opposite (i :: placed) q rest
      else []

private def highCandidates (opposite : Bool) : List Placement :=
  highPlacements opposite [0, 1, 2, 3] root cycleVertices

private def labels : List (Fin 10) := List.finRange 10

private def hollowEdges (opposite : Bool) : List (Fin 10 × Fin 10) :=
  labels.flatMap fun i =>
    (labels.filter fun j => i < j && hollow opposite i j).map fun j => (i, j)

private def fillMiddles (p : Placement) (chosen : List Vertex) :
    List (Fin 10 × Fin 10) → List (List Vertex)
  | [] => [chosen]
  | (i, j) :: rest =>
    (middleOptions labels p i j).flatMap fun x =>
      if chosen.any (fun y => x == y || adjacent x y) then []
      else fillMiddles p (x :: chosen) rest

private def candidates (opposite : Bool) : List (List Vertex) :=
  (highCandidates opposite).flatMap fun p =>
    fillMiddles p [] (hollowEdges opposite) |>.map fun mids => mids ++ labels.map p

private def neighborMask (x : Vertex) : Nat :=
  (List.finRange 8).foldl
    (fun mask a => mask ||| (1 <<< ((toggle x a.succ).toNat / 2)))
    (1 <<< (x.toNat / 2))

private def reconstructionSize (half : List Vertex) : Nat :=
  let mask := half.foldl (fun mask x => mask ^^^ neighborMask x) 0
  (List.range 256).countP mask.testBit

set_option maxRecDepth 8192 in
set_option maxHeartbeats 18000000 in
-- Enumerate two placements of the three pairs on the cycle and check the
-- corresponding lists of unsigned opposite halves.
private theorem checked (opposite : Bool) :
    (candidates opposite).all (fun half => reconstructionSize half != 50) = true := by
  cases opposite <;> decide +kernel

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonPlacements
