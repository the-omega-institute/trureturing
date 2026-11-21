/- GID: D5/S3/Topology/FourBraidKhovanovCube
   generality: I
   mirror-B: D5/B/S3/Topology/FourBraidKhovanovCube
   mirror-E: none(waiver:algebraically-proved)
   anchors: [lake/module/Mathlib.Logic.Relation]
   utility: none
   digest: Signed integral Khovanov cube of a closed eleven-crossing four-braid. -/

import D5.S3.Topology.FiniteMatchingClosure

/-!
The ordinary unreduced Frobenius algebra over the integers, with circle labels
`1` and `X`, for the four-braid witness to Przytycki–Silvero, arXiv:2305.18648v1,
§9.1. A resolution mask records the crossings smoothed as ones.
-/

set_option autoImplicit false

namespace D5.S3.Topology.FourBraidKhovanovCube

open FiniteMatchingClosure

/-- The sign and zero-based location of each braid generator. -/
def braid : List (Bool × Fin 3) :=
  [(true, 0), (true, 1), (true, 0), (true, 0), (false, 2), (true, 1),
   (true, 1), (false, 2), (true, 1), (true, 0), (true, 1)]

def crossings : Nat := braid.length

private def positions : List Nat := List.range crossings

private def vertexCount : Nat := 4 * crossings

private def vertices : List Nat := List.range vertexCount

private def vertex (k : Nat) (x : Boundary 4) : Nat :=
  (4 * (if x.1 then k + 1 else k) + x.2.val) % vertexCount


private def matching (s k : Nat) (x : Boundary 4) : Boundary 4 :=
  let (positive, j) := braid[k]!
  if s.testBit k == positive then cupcapMate j.val (by have := j.isLt; omega) x
  else (identityMatching 4).mate x

/-- Close the braid by identifying level eleven with level zero. A negative
crossing interchanges the vertical and cup-cap matchings. -/
def edges (s : Nat) : List (Nat × Nat) :=
  positions.flatMap fun k =>
    [false, true].flatMap fun side =>
      ([0, 1, 2, 3] : List (Fin 4)).filterMap fun i =>
        let x : Boundary 4 := (side, i)
        let y := matching s k x
        let u := vertex k x
        let v := vertex k y
        if (side == y.1 && i.val < y.2.val) || (!side && y.1) then
          some (u, v)
        else none

private def mark (mask v : Nat) : Nat := mask ||| (1 <<< v)

private abbrev Dart := Nat × Boundary 4

/-- Follow the crossing matching, then pass across the seam to the other
incidence at that vertex. The last bottom seam meets the first top seam. -/
private def nextDart (s : Nat) (dart : Dart) : Dart :=
  let y := matching s dart.1 dart.2
  if y.1 then ((dart.1 + 1) % crossings, false, y.2)
  else ((dart.1 + crossings - 1) % crossings, true, y.2)

private def walk (s : Nat) : Nat → Dart → Nat → Nat
  | 0, _, visited => visited
  | fuel + 1, dart, visited =>
    let v := vertex dart.1 dart.2
    if visited.testBit v then visited
    else walk s fuel (nextDart s dart) (mark visited v)

/-- Each circle is stored as its least vertex and its set of vertices. -/
abbrev Partition := List (Nat × Nat)

private def collect (s : Nat) (seen : Nat) : List Nat → Partition
  | [] => []
  | v :: vs =>
    if seen.testBit v then collect s seen vs
    else
      let circle := walk s vertexCount (v / 4, false, Fin.ofNat 4 v) 0
      (v, circle) :: collect s (seen ||| circle) vs

/-- Follow alternating crossing and seam edges around each resolution circle. -/
def resolve (s : Nat) : Partition := collect s 0 vertices

def circles (parts : Partition) : List Nat := parts.map Prod.fst

private def representative (parts : Partition) (v : Nat) : Nat :=
  ((parts.find? fun p => p.2.testBit v).getD (v, 0)).1

def weight (s : Nat) : Nat :=
  (positions.filter s.testBit).length

def upperQuantum (s : Nat) (roots : Partition) : Nat :=
  weight s + 5 + (circles roots).length

/-- A mask with exactly `n` marked circles represents the tensors with `n`
labels `X`; all remaining circles carry `1`. -/
private def labelMasks : Nat → List Nat → List Nat
  | 0, _ => [0]
  | _ + 1, [] => []
  | n + 1, v :: vs =>
    labelMasks (n + 1) vs ++ (labelMasks n vs).map (fun mask => mark mask v)

/-- Enhanced resolutions, with one bit at the representative of each
circle carrying the label `X`. -/
abbrev Enhanced := Nat × Nat

def labels (j s : Nat) (roots : Partition) : List Enhanced :=
  let reps := circles roots
  let upper := weight s + 5 + reps.length
  if j ≤ upper && (upper - j) % 2 == 0 then
    (labelMasks ((upper - j) / 2) reps).map (s, ·)
  else []

/-- The actual basis with `k` one-smoothings and normalized quantum degree
`j`. The normalized cohomological degree is `(k : Int) - 2`. -/
def basis (roots : Nat → Partition) (j k : Nat) : List Enhanced :=
  (List.range (2 ^ crossings)).flatMap fun s =>
    if weight s == k then labels j s (roots s) else []

private def transfer (source : Partition) (mask : Nat) (targetCircles : List Nat) : Nat :=
  targetCircles.foldl (fun acc v => if mask.testBit (representative source v) then mark acc v else acc) 0

/-- For a merge, transport the union of the `X`-circles unless two labels
`X` merge. For a split, transport labels and apply
`Δ(1) = 1 ⊗ X + X ⊗ 1` or `Δ(X) = X ⊗ X`. -/
def saddle (source target : Partition) (mask : Nat) : List Nat :=
  let before := circles source
  let after := circles target
  if before.length == after.length + 1 then
    let marked := before.filter (fun v => mask.testBit v)
    let output := marked.foldl (fun acc v => mark acc (representative target v)) 0
    if (after.filter output.testBit).length == marked.length then [output] else []
  else if after.length == before.length + 1 then
    let output := transfer source mask after
    let split := after.filter fun v => (after.filter fun u => representative source u == representative source v).length == 2
    match split with
    | [a, b] => if mask.testBit (representative source a) then [output]
      else [mark output a, mark output b]
    | _ => []
  else []

/-- Signed coefficients in the enhanced-resolution basis. The sign uses
the number of one-smoothings preceding the changed crossing. -/
def differential (roots : Nat → Partition) (x : Enhanced) : List (Enhanced × Int) :=
  positions.flatMap fun k =>
    if x.1.testBit k then []
    else
      let t := mark x.1 k
      let sign : Int := if ((List.range k).filter x.1.testBit).length % 2 == 0 then 1 else -1
      (saddle (roots x.1) (roots t) x.2).map fun label => ((t, label), sign)

end D5.S3.Topology.FourBraidKhovanovCube
