import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayPlacementNormalForm
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9OrbitCertificateProbe
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.List.Sublists

/-! The normalized Gray54 extension certificate. The local charges are the
15 representative polynomials of the 25 signed transfers averaged over block
and within-block coordinate permutations. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9Gray54ResidualCertificate

open Finset
open Q9GrayPlacementNormalForm (Fits placement origin)
open Q9TriplePartitionOrbits (standardLabels)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

private abbrev Vertex := BitVec 9

private def vertices : List Vertex := (List.finRange 512).map BitVec.ofFin

private theorem mem_vertices (x : Vertex) : x ∈ vertices :=
  List.mem_map.mpr ⟨x.toFin, List.mem_finRange _, rfl⟩

private def tripleWeight (v : Nat) : Nat :=
  (v % 2) + (v / 2 % 2) + (v / 4 % 2)

private def blockWeight (x : Vertex) (i : Nat) : Nat :=
  tripleWeight (x.toNat >>> (3 * i))

private def weight (x : Vertex) : Nat :=
  blockWeight x 0 + blockWeight x 1 + blockWeight x 2

private def isGray (x : Vertex) : Bool :=
  decide (blockWeight x 0 ≤ 1 ∧ blockWeight x 1 ≤ 1 ∧
    blockWeight x 2 ≤ 1 ∧ 2 ≤ weight x)

private def toggle (x : Vertex) (i : Fin 9) : Vertex :=
  x ^^^ BitVec.ofNat 9 (2 ^ i.val)

private def isResidual (x : Vertex) : Bool :=
  !isGray x && (List.finRange 9).all fun i => !isGray (toggle x i)

private def residualVertices : List Vertex := vertices.filter isResidual

/-- The standard three-block Gray54 placement in little-endian coordinates. -/
def normalizedGray : Finset (BitVec 9) := (vertices.filter isGray).toFinset

/-- The vertices outside the closed neighborhood of the standard placement. -/
def residual : Finset (BitVec 9) := residualVertices.toFinset

@[simp] private theorem mem_gray (x : Vertex) : x ∈ normalizedGray ↔ isGray x = true := by
  simp [normalizedGray, mem_vertices]

@[simp] private theorem mem_residual (x : Vertex) : x ∈ residual ↔ isResidual x = true := by
  simp [residual, residualVertices, mem_vertices]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- Compare the block-weight calculation with the placement on every cube vertex.
private theorem gray_checked : ∀ x : Fin 512,
    isGray (BitVec.ofFin x) = true ↔
      Fits standardLabels origin (cubeBitVec 9 (BitVec.ofFin x)) := by
  decide +kernel

/-- The certificate uses the image of the standard placement under the
inverse of the repository's little-endian cube equivalence. -/
theorem normalizedGray_eq_placement :
    normalizedGray = (placement standardLabels origin).map (cubeBitVec 9).symm.toEmbedding := by
  ext x
  rw [mem_gray, gray_checked x.toFin]
  constructor
  · intro hx
    exact mem_map.mpr ⟨cubeBitVec 9 x, Q9GrayPlacementNormalForm.mem_placement.mpr hx,
      (cubeBitVec 9).symm_apply_apply x⟩
  · intro hx
    obtain ⟨y, hy, he⟩ := mem_map.mp hx
    have he' : y = cubeBitVec 9 x := by simpa using congrArg (cubeBitVec 9) he
    exact Q9GrayPlacementNormalForm.mem_placement.mp (he' ▸ hy)

private theorem toggle_adj (x : Vertex) (i : Fin 9) :
    hammingDist (cubeBitVec 9 x) (cubeBitVec 9 (toggle x i)) = 1 := by
  change (hypercube 9).Adj (cubeBitVec 9 x) (cubeBitVec 9 (toggle x i))
  rw [toggle, cubeBitVec_xor_single]
  exact BalancedCriticalSpectrum.flip_adj _ _

private theorem exists_toggle {x y : Vertex}
    (h : hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) = 1) :
    ∃ i, y = toggle x i := by
  obtain ⟨i, hi⟩ := adjacent_exists_flip h
  refine ⟨i, (cubeBitVec 9).injective ?_⟩
  simpa only [toggle, cubeBitVec_xor_single, BalancedCriticalSpectrum.flip] using hi

/-- Residual membership is exactly distance at least two from every Gray vertex. -/
theorem mem_residual_iff (x : BitVec 9) :
    x ∈ residual ↔ ∀ y ∈ normalizedGray, 1 < hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) := by
  have hmem : x ∈ residual ↔ x ∉ normalizedGray ∧
      ∀ i : Fin 9, toggle x i ∉ normalizedGray := by
    simp [isResidual, List.all_eq_true]
  rw [hmem]
  constructor
  · rintro ⟨hx, htoggle⟩ y hy
    by_contra! h
    have hd : hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) = 0 ∨
        hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) = 1 := by omega
    rcases hd with h0 | h1
    · exact hx (((cubeBitVec 9).injective (hammingDist_eq_zero.mp h0)) ▸ hy)
    · obtain ⟨i, rfl⟩ := exists_toggle h1
      exact htoggle i hy
  · intro h
    exact ⟨fun hx => by simpa using h x hx, fun i hi => by
      have hd := h (toggle x i) hi
      rw [toggle_adj] at hd
      omega⟩

private def inReference (x : Vertex) : Bool :=
  (weight x % 2 == 1) == (blockWeight x 0 != 0 && blockWeight x 1 != 0 &&
    blockWeight x 2 != 0)

private def reference : Finset Vertex := residual.filter (fun x => inReference x = true)

private abbrev Monomial := Vertex × Vertex
private abbrev Term := Monomial × Int

private structure Orbit where
  center : Vertex
  neighborhood : List Vertex
  terms : List Term
  bound : Int
  deriving Inhabited

-- A repeated vertex encodes a linear monomial. The other terms are quadratic.
private def orbits : Array Orbit := #[
  ⟨0, [0], [
  ], 0⟩,
  ⟨3, [3, 7], [
    ((3, 7), 1008)
  ], 0⟩,
  ⟨7, [3, 5, 6, 7, 15, 23, 39, 71, 135, 263], [
    ((3, 7), -1008), ((5, 7), -1008), ((6, 7), -1008), ((15, 15), -648),
    ((23, 23), -648), ((39, 39), -648), ((71, 71), -648), ((135, 135), -648),
    ((263, 263), -648)
  ], 0⟩,
  ⟨15, [7, 15, 31, 47, 79, 143, 271], [
    ((15, 15), 936), ((15, 31), 1476), ((15, 47), 1476)
  ], 0⟩,
  ⟨27, [27, 31, 59, 91, 155, 283], [
    ((27, 27), 3792)
  ], 0⟩,
  ⟨31, [15, 23, 27, 29, 30, 31, 63, 95, 159, 287], [
    ((15, 15), -144), ((15, 31), -1476), ((15, 95), 36), ((15, 159), 36),
    ((15, 287), 36), ((23, 23), -144), ((23, 31), -1476), ((23, 95), 36),
    ((23, 159), 36), ((23, 287), 36), ((27, 27), -1632), ((29, 29), -1632),
    ((30, 30), -1632), ((31, 63), -648)
  ], 0⟩,
  ⟨63, [31, 47, 55, 59, 61, 62, 63, 127, 191, 319], [
    ((31, 63), 648), ((47, 63), 648), ((55, 63), 648), ((59, 63), 648),
    ((61, 63), 648), ((62, 63), 648)
  ], 0⟩,
  ⟨79, [15, 71, 79, 95, 111, 207, 335], [
    ((15, 95), -36), ((15, 111), -36), ((71, 207), -36), ((71, 335), -36),
    ((79, 95), 936), ((79, 111), 936), ((79, 207), 936), ((79, 335), 936),
    ((95, 207), 36), ((95, 335), 36), ((111, 207), 36), ((111, 335), 36)
  ], 0⟩,
  ⟨91, [27, 91, 95, 123, 219, 347], [
    ((27, 27), -176), ((91, 95), 936), ((91, 123), 936), ((91, 219), 800),
    ((91, 347), 800), ((95, 123), 16), ((95, 219), 156), ((95, 347), 156),
    ((123, 219), 156), ((123, 347), 156), ((219, 219), -144), ((219, 347), 80),
    ((347, 347), -144)
  ], 16⟩,
  ⟨95, [31, 79, 87, 91, 93, 94, 95, 127, 223, 351], [
    ((79, 95), -936), ((87, 95), -936), ((91, 95), -936), ((93, 95), -936),
    ((94, 95), -936), ((95, 127), -144), ((95, 223), -540), ((95, 351), -540),
    ((127, 223), -396), ((127, 351), -396)
  ], 0⟩,
  ⟨127, [63, 95, 111, 119, 123, 125, 126, 127, 255, 383], [
    ((95, 123), -16), ((95, 125), -16), ((95, 126), -16), ((95, 127), 144),
    ((111, 123), -16), ((111, 125), -16), ((111, 126), -16), ((111, 127), 144),
    ((119, 123), -16), ((119, 125), -16), ((119, 126), -16), ((119, 127), 144),
    ((123, 127), 144), ((125, 127), 144), ((126, 127), 144), ((127, 255), 1584),
    ((127, 383), 1584)
  ], 0⟩,
  ⟨219, [91, 155, 203, 211, 217, 218, 219, 223, 251, 475], [
    ((91, 219), -800), ((155, 219), -800), ((203, 219), -800), ((211, 219), -800),
    ((217, 219), -800), ((218, 219), -800), ((219, 219), 864), ((219, 223), -784),
    ((219, 251), -784), ((219, 475), -784)
  ], 0⟩,
  ⟨223, [95, 159, 207, 215, 219, 221, 222, 223, 255, 479], [
    ((95, 207), -36), ((95, 215), -36), ((95, 219), -156), ((95, 221), -156),
    ((95, 222), -156), ((95, 223), 540), ((159, 207), -36), ((159, 215), -36),
    ((159, 219), -156), ((159, 221), -156), ((159, 222), -156), ((159, 223), 540),
    ((207, 219), -156), ((207, 221), -156), ((207, 222), -156), ((207, 223), 540),
    ((215, 219), -156), ((215, 221), -156), ((215, 222), -156), ((215, 223), 540),
    ((219, 221), -80), ((219, 222), -80), ((219, 223), 784), ((221, 222), -80),
    ((221, 223), 784), ((222, 223), 784), ((223, 223), 1632)
  ], 0⟩,
  ⟨255, [127, 191, 223, 239, 247, 251, 253, 254, 255, 511], [
    ((127, 223), 396), ((127, 239), 396), ((127, 247), 396), ((127, 251), 396),
    ((127, 253), 396), ((127, 254), 396), ((127, 255), -1584), ((191, 223), 396),
    ((191, 239), 396), ((191, 247), 396), ((191, 251), 396), ((191, 253), 396),
    ((191, 254), 396), ((191, 255), -1584), ((223, 223), -816), ((239, 239), -816),
    ((247, 247), -816), ((251, 251), -816), ((253, 253), -816), ((254, 254), -816),
    ((255, 255), -576)
  ], 72⟩,
  ⟨511, [255, 383, 447, 479, 495, 503, 507, 509, 510, 511], [
    ((255, 255), 576), ((383, 383), 576), ((447, 447), 576), ((479, 479), 576),
    ((495, 495), 576), ((503, 503), 576), ((507, 507), 576), ((509, 509), 576),
    ((510, 510), 576)
  ], 1728⟩
]

-- Entry at x encodes 15 * permutationIndex + representativeIndex.
private def normalizations : Array Nat := #[
  0, 0, 0, 1, 0, 541, 1621, 2, 0, 0, 0, 0, 0, 0, 0, 3,
  0, 0, 0, 0, 0, 0, 0, 183, 6481, 0, 0, 4, 0, 544, 1624, 5,
  0, 0, 0, 0, 0, 0, 0, 363, 7021, 0, 0, 94, 0, 634, 1714, 95,
  8101, 0, 0, 274, 0, 814, 1894, 275, 6482, 6483, 6663, 6485, 6843, 6575, 6755, 6,
  0, 0, 0, 0, 0, 0, 0, 3243, 0, 0, 0, 0, 0, 0, 0, 7,
  0, 0, 0, 0, 0, 0, 0, 187, 0, 0, 0, 8, 0, 548, 1628, 9,
  0, 0, 0, 0, 0, 0, 0, 367, 0, 0, 0, 98, 0, 638, 1718, 99,
  0, 0, 0, 278, 0, 818, 1898, 279, 9723, 6487, 6667, 6489, 6847, 6579, 6759, 10,
  0, 0, 0, 0, 0, 0, 0, 3423, 0, 0, 0, 0, 0, 0, 0, 37,
  0, 0, 0, 0, 0, 0, 0, 217, 0, 0, 0, 38, 0, 578, 1658, 39,
  0, 0, 0, 0, 0, 0, 0, 397, 0, 0, 0, 128, 0, 668, 1748, 129,
  0, 0, 0, 308, 0, 848, 1928, 309, 9903, 6517, 6697, 6519, 6877, 6609, 6789, 40,
  12961, 0, 0, 3244, 0, 3784, 4864, 3245, 0, 0, 0, 3248, 0, 3788, 4868, 3249,
  0, 0, 0, 3278, 0, 3818, 4898, 3279, 9724, 9728, 9758, 11, 9788, 551, 1631, 12,
  0, 0, 0, 3308, 0, 3848, 4928, 3309, 10264, 10268, 10298, 101, 10328, 641, 1721, 102,
  11344, 11348, 11378, 281, 11408, 821, 1901, 282, 9725, 9729, 9759, 6492, 9789, 6582, 6762, 13,
  0, 0, 0, 0, 0, 0, 0, 3603, 0, 0, 0, 0, 0, 0, 0, 67,
  0, 0, 0, 0, 0, 0, 0, 247, 0, 0, 0, 68, 0, 608, 1688, 69,
  0, 0, 0, 0, 0, 0, 0, 427, 0, 0, 0, 158, 0, 698, 1778, 159,
  0, 0, 0, 338, 0, 878, 1958, 339, 10083, 6547, 6727, 6549, 6907, 6639, 6819, 70,
  13501, 0, 0, 3334, 0, 3874, 4954, 3335, 0, 0, 0, 3338, 0, 3878, 4958, 3339,
  0, 0, 0, 3368, 0, 3908, 4988, 3369, 9814, 9818, 9848, 26, 9878, 566, 1646, 27,
  0, 0, 0, 3398, 0, 3938, 5018, 3399, 10354, 10358, 10388, 116, 10418, 656, 1736, 117,
  11434, 11438, 11468, 296, 11498, 836, 1916, 297, 9815, 9819, 9849, 6507, 9879, 6597, 6777, 28,
  14581, 0, 0, 3514, 0, 4054, 5134, 3515, 0, 0, 0, 3518, 0, 4058, 5138, 3519,
  0, 0, 0, 3548, 0, 4088, 5168, 3549, 9994, 9998, 10028, 56, 10058, 596, 1676, 57,
  0, 0, 0, 3578, 0, 4118, 5198, 3579, 10534, 10538, 10568, 146, 10598, 686, 1766, 147,
  11614, 11618, 11648, 326, 11678, 866, 1946, 327, 9995, 9999, 10029, 6537, 10059, 6627, 6807, 58,
  12962, 12963, 13143, 12965, 13323, 13055, 13235, 3246, 16203, 12967, 13147, 12969, 13327,
  13059, 13239, 3250,
  16383, 12997, 13177, 12999, 13357, 13089, 13269, 3280, 16205, 16209, 16239, 12972, 16269,
  13062, 13242, 3253,
  16563, 13027, 13207, 13029, 13387, 13119, 13299, 3310, 16295, 16299, 16329, 12987, 16359,
  13077, 13257, 3268,
  16475, 16479, 16509, 13017, 16539, 13107, 13287, 3298, 9726, 9730, 9760, 9733, 9790, 9748,
  9778, 14
]

private def permutations : Array (Array Nat) :=
  #[#[0, 1, 2], #[0, 2, 1], #[1, 0, 2], #[1, 2, 0], #[2, 0, 1], #[2, 1, 0]]

private def permuteTriple (p bits : Nat) : Nat :=
  let axes := permutations[p]!
  (if bits.testBit 0 then 2 ^ axes[0]! else 0) +
    (if bits.testBit 1 then 2 ^ axes[1]! else 0) +
    (if bits.testBit 2 then 2 ^ axes[2]! else 0)

-- The four base-six digits specify the block permutation followed by the
-- three within-block permutations.
private def relabel (action : Nat) (x : Vertex) : Vertex :=
  let blocks := permutations[action / 216]!
  let a := permuteTriple (action / 36 % 6) x.toNat
  let b := permuteTriple (action / 6 % 6) (x.toNat >>> 3)
  let c := permuteTriple (action % 6) (x.toNat >>> 6)
  BitVec.ofNat 9 ((a <<< (3 * blocks[0]!)) + (b <<< (3 * blocks[1]!)) +
                 (c <<< (3 * blocks[2]!)))

private def normalization (x : Vertex) : Nat := normalizations[x.toNat]!
private def localOrbit (x : Vertex) : Orbit := orbits[normalization x % 15]!
private def transport (x : Vertex) : Vertex → Vertex := relabel (normalization x / 15)

private def monomial (u v : Vertex) : Monomial :=
  if u.toNat ≤ v.toNat then (u, v) else (v, u)

private def evalTerm (changed : Vertex → Bool) (t : Term) : Int :=
  if changed t.1.1 && changed t.1.2 then t.2 else 0

private def eval (changed : Vertex → Bool) (terms : List Term) : Int :=
  (terms.map (evalTerm changed)).sum

private def relabelTerm (f : Vertex → Vertex) (t : Term) : Term :=
  (monomial (f t.1.1) (f t.1.2), t.2)

private def localTerms (x : Vertex) : List Term :=
  (localOrbit x).terms.map (relabelTerm (transport x))

private def bit (b : Bool) : Int := if b then 1 else 0

private def charge (selected : Vertex → Bool) (center : Vertex) (terms : List Term) : Int :=
  3888 * (bit (selected center) - bit (inReference center)) +
    eval (fun u => selected u != inReference u) terms

private def admissible (o : Orbit) : List (List Vertex) :=
  o.neighborhood.sublists.filter fun l => !l.contains o.center || decide (l.length ≤ 4)

private def verifyOrbit (o : Orbit) : Bool :=
  o.neighborhood.contains o.center &&
  o.terms.all (fun t => o.neighborhood.contains t.1.1 && o.neighborhood.contains t.1.2) &&
  (admissible o).all fun l => decide (charge (fun u => l.contains u) o.center o.terms ≤ o.bound)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
-- Enumerate the admissible local selections on the fifteen representatives.
private theorem orbits_checked : ∀ i : Fin 15, verifyOrbit orbits[i.val]! = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
-- Check cardinalities, the local assignment count, and the weighted sum of the bounds.
private theorem counts_checked :
    normalizedGray.card = 54 ∧ residual.card = 314 ∧ reference.card = 203 ∧
    ((orbits.toList.map fun o => (admissible o).length).sum = 6112) ∧
    (∑ x ∈ residual, (localOrbit x).bound) = 3672 := by
  decide +kernel

private def verifyTransport (x : Vertex) : Bool :=
  let o := localOrbit x
  let f := transport x
  f o.center == x && decide ((o.neighborhood.map f).Nodup) &&
    o.neighborhood.all fun u =>
      (inReference (f u) == inReference u) &&
      (f u == x || decide (hammingDist (cubeBitVec 9 x) (cubeBitVec 9 (f u)) = 1))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
-- Check the coordinate permutation and local incidence at every residual vertex.
private theorem transport_checked : ∀ x : Fin 512,
    isResidual (BitVec.ofFin x) = true → verifyTransport (BitVec.ofFin x) = true := by
  decide +kernel

private def key (t : Term) : Nat := 512 * t.1.1.toNat + t.1.2.toNat

private def allTerms : List Term := residualVertices.flatMap localTerms

-- Split the sparse monomials by key bits. Each occupied leaf must have one
-- monomial and zero total coefficient.
private def verifyCoefficients : Nat → List Term → Bool
  | _, [] => true
  | 0, t :: ts => ts.all (fun u => u.1 == t.1) && ((t :: ts).map Prod.snd).sum == 0
  | n + 1, t :: ts =>
    verifyCoefficients n ((t :: ts).filter fun u => (key u).testBit n) &&
    verifyCoefficients n ((t :: ts).filter fun u => !(key u).testBit n)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
-- Check sparse coefficients across all residual centers in the kernel.
private theorem coefficients_checked : verifyCoefficients 18 allTerms = true := by
  decide +kernel

private theorem eval_append (changed : Vertex → Bool) (l r : List Term) :
    eval changed (l ++ r) = eval changed l + eval changed r := by
  simp [eval, List.sum_append]

private theorem eval_partition (changed : Vertex → Bool) (p : Term → Bool) (l : List Term) :
    eval changed (l.filter p) + eval changed (l.filter fun u => !p u) = eval changed l := by
  induction l with
  | nil => rfl
  | cons t ts ih =>
    cases hp : p t <;> simp [hp, eval] at ih ⊢ <;> omega

private theorem eval_same_monomial (changed : Vertex → Bool) (m : Monomial) (l : List Term)
    (hl : ∀ t ∈ l, t.1 = m) :
    eval changed l = if changed m.1 && changed m.2 then (l.map Prod.snd).sum else 0 := by
  induction l with
  | nil => simp [eval]
  | cons t ts ih =>
    have ht := hl t List.mem_cons_self
    have hts := ih fun t ht => hl t (List.mem_cons_of_mem _ ht)
    change evalTerm changed t + eval changed ts = _
    rw [hts]
    simp only [evalTerm, ht, List.map_cons, List.sum_cons]
    split <;> simp_all

private theorem verifyCoefficients_sound (changed : Vertex → Bool) (n : Nat) (l : List Term)
    (h : verifyCoefficients n l = true) : eval changed l = 0 := by
  induction n generalizing l with
  | zero =>
    cases l with
    | nil => rfl
    | cons t ts =>
      simp only [verifyCoefficients, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
      have hm : ∀ u ∈ t :: ts, u.1 = t.1 := by
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · rfl
        · exact h.1 u hu
      rw [eval_same_monomial changed t.1 _ hm, h.2]
      simp
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons t ts =>
      simp only [verifyCoefficients, Bool.and_eq_true] at h
      rw [← eval_partition changed (fun u => (key u).testBit n), ih _ h.1, ih _ h.2, add_zero]

private theorem eval_allTerms (changed : Vertex → Bool) : eval changed allTerms = 0 :=
  verifyCoefficients_sound changed 18 allTerms coefficients_checked

private theorem eval_flatMap (changed : Vertex → Bool) (f : Vertex → List Term)
    (l : List Vertex) : eval changed (l.flatMap f) = (l.map fun x => eval changed (f x)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, eval_append, ih]
    rfl

private theorem sum_transfers (changed : Vertex → Bool) :
    (∑ x ∈ residual, eval changed (localTerms x)) = 0 := by
  have hdistinct : residualVertices.Nodup :=
    ((List.nodup_finRange _).map (f := BitVec.ofFin) (fun a b h =>
      congrArg BitVec.toFin h)).filter _
  rw [residual, List.sum_toFinset _ hdistinct, ← eval_flatMap]
  exact eval_allTerms changed

private theorem evalTerm_relabel (changed : Vertex → Bool) (f : Vertex → Vertex) (t : Term) :
    evalTerm changed (relabelTerm f t) = evalTerm (changed ∘ f) t := by
  unfold evalTerm relabelTerm monomial
  split <;> simp [Bool.and_comm]

private def selected (S : Finset Vertex) (x : Vertex) : Bool := decide (x ∈ S)

private theorem local_bound (S : Finset Vertex)
    (hdeg : ∀ x ∈ S,
      (S.filter (fun y => hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) = 1)).card ≤ 3)
    (x : Vertex) (hx : x ∈ residual) :
    charge (selected S) x (localTerms x) ≤ (localOrbit x).bound := by
  let o := localOrbit x
  let f := transport x
  have hcheck : verifyOrbit o = true :=
    orbits_checked ⟨normalization x % 15, Nat.mod_lt _ (by decide)⟩
  have htransport : verifyTransport x = true :=
    transport_checked x.toFin ((mem_residual x).mp hx)
  simp only [verifyOrbit, Bool.and_eq_true, and_assoc, List.contains_iff_mem, List.all_eq_true,
    decide_eq_true_eq] at hcheck
  have ⟨hcenter, hterms, hmax⟩ := hcheck
  simp only [verifyTransport, Bool.and_eq_true, and_assoc, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, Bool.or_eq_true_iff] at htransport
  have ⟨hfx, hn, hneigh⟩ := htransport
  change f o.center = x at hfx
  change (o.neighborhood.map f).Nodup at hn
  change ∀ u ∈ o.neighborhood, inReference (f u) = inReference u ∧
    (f u = x ∨ hammingDist (cubeBitVec 9 x) (cubeBitVec 9 (f u)) = 1) at hneigh
  let l := o.neighborhood.filter (fun u => selected S (f u))
  have hsub : List.Sublist l o.neighborhood := List.filter_sublist
  have hagree (u : Vertex) (hu : u ∈ o.neighborhood) : l.contains u = selected S (f u) := by
    simp [l, List.mem_filter, hu]
  have hlen (hc : l.contains o.center = true) : l.length ≤ 4 := by
    rw [hagree o.center hcenter, hfx] at hc
    have hxS : x ∈ S := of_decide_eq_true hc
    have hmap : (l.map f).toFinset ⊆
        insert x (S.filter (fun y => hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) = 1)) := by
      intro y hy
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
      obtain ⟨huc, huS⟩ := List.mem_filter.mp hu
      rcases (hneigh u huc).2 with heq | hadj
      · exact mem_insert.mpr (Or.inl heq)
      · exact mem_insert.mpr (Or.inr (mem_filter.mpr ⟨by simpa [selected] using huS, hadj⟩))
    have hnodup := (hsub.map f).nodup hn
    have hc1 := card_le_card hmap
    rw [List.toFinset_card_of_nodup hnodup, List.length_map] at hc1
    have hc2 := card_insert_le x (S.filter (fun y =>
      hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) = 1))
    exact hc1.trans (hc2.trans (Nat.add_le_add_right (hdeg x hxS) 1))
  have ha : l ∈ admissible o := by
    refine List.mem_filter.mpr ⟨List.mem_sublists.mpr hsub, ?_⟩
    cases hc : l.contains o.center with
    | false => rfl
    | true => exact Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true (hlen hc)))
  have heval :
      eval (fun u => selected S u != inReference u) (localTerms x) =
        eval (fun u => l.contains u != inReference u) o.terms := by
    change List.sum (List.map _ (o.terms.map (relabelTerm f))) =
      List.sum (List.map _ o.terms)
    rw [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    change evalTerm _ (relabelTerm f t) = _
    rw [evalTerm_relabel]
    obtain ⟨h1, h2⟩ := hterms t ht
    simp only [evalTerm, Function.comp_def, hagree _ h1, hagree _ h2,
      (hneigh _ h1).1, (hneigh _ h2).1]
  have hs : l.contains o.center = selected S x := (hagree o.center hcenter).trans
    (congrArg (selected S) hfx)
  have hr : inReference x = inReference o.center := hfx ▸ (hneigh o.center hcenter).1
  change 3888 * (bit (selected S x) - bit (inReference x)) +
    eval _ (localTerms x) ≤ o.bound
  rw [heval, ← hs, hr]
  exact hmax l ha

/-- The normalized placement contains 54 vertices. -/
theorem normalizedGray_card : normalizedGray.card = 54 := counts_checked.1

/-- Every induced subcubic subset of the normalized Gray54 residual has at most 203 vertices. -/
theorem residual_card_le (S : Finset (BitVec 9)) (hSR : S ⊆ residual)
    (hdeg : ∀ x ∈ S,
      (S.filter (fun y => hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) = 1)).card ≤ 3) :
    S.card ≤ 203 := by
  have hbound := sum_le_sum (fun x hx => local_bound S hdeg x hx)
  have hchange := sum_transfers (fun u => selected S u != inReference u)
  have hS : (∑ x ∈ residual, bit (selected S x)) = (S.card : Int) := by
    have hfilter : residual.filter (fun x => x ∈ S) = S := by
      apply Finset.ext
      intro x
      exact mem_filter.trans ⟨And.right, fun hx => ⟨hSR hx, hx⟩⟩
    change (∑ x ∈ residual, if decide (x ∈ S) = true then (1 : Int) else 0) = _
    simp only [decide_eq_true_eq, sum_boole, hfilter]
  have hR : (∑ x ∈ residual, bit (inReference x)) = (reference.card : Int) :=
    sum_boole _ _
  rw [counts_checked.2.2.2.2] at hbound
  simp only [charge, sum_add_distrib, ← mul_sum, sum_sub_distrib, hchange, add_zero,
    hS, hR, counts_checked.2.2.1] at hbound
  omega

private def referenceDirections (x : Vertex) : List (Fin 9) :=
  (List.finRange 9).filter fun i =>
    isResidual (toggle x i) && inReference (toggle x i)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
-- Check the reference degree against the nine possible flips at each vertex.
private theorem referenceDegree_checked : ∀ x : Fin 512,
    isResidual (BitVec.ofFin x) = true → inReference (BitVec.ofFin x) = true →
    (referenceDirections (BitVec.ofFin x)).length ≤ 3 := by
  decide +kernel

/-- The parity reference set attains the residual bound. -/
theorem residual_bound_attained :
    ∃ S : Finset (BitVec 9), S ⊆ residual ∧ S.card = 203 ∧
      ∀ x ∈ S, (S.filter (fun y => hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) = 1)).card ≤ 3 := by
  refine ⟨reference, filter_subset _ _, counts_checked.2.2.1, ?_⟩
  intro x hx
  obtain ⟨hxR, hxref⟩ := mem_filter.mp hx
  have hsubset : (reference.filter (fun y => hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) = 1)) ⊆
      (referenceDirections x).toFinset.image (toggle x) := by
    intro y hy
    obtain ⟨hyref, hyadj⟩ := mem_filter.mp hy
    obtain ⟨hyR, hyref⟩ := mem_filter.mp hyref
    obtain ⟨i, rfl⟩ := exists_toggle hyadj
    refine mem_image.mpr ⟨i, List.mem_toFinset.mpr (List.mem_filter.mpr ?_), rfl⟩
    refine ⟨List.mem_finRange _, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨(mem_residual _).mp hyR, hyref⟩
  calc
    _ ≤ ((referenceDirections x).toFinset.image (toggle x)).card := card_le_card hsubset
    _ ≤ (referenceDirections x).toFinset.card := card_image_le
    _ ≤ (referenceDirections x).length := List.toFinset_card_le _
    _ ≤ 3 := referenceDegree_checked x.toFin ((mem_residual x).mp hxR) hxref

#print axioms normalizedGray_eq_placement
#print axioms mem_residual_iff
#print axioms normalizedGray_card
#print axioms residual_card_le
#print axioms residual_bound_attained

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9Gray54ResidualCertificate
