/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BalancedHalfCardinality
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BalancedHalfCardinality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Bounds and determines the parity of coordinate halves in Huang-balanced cubic nine-cube supports. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction

/-! The crossing count controls both the lower bound and the parity of every
coordinate half of a Huang-balanced cubic support. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BalancedHalfCardinality

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced directionEdges direction_edge_count)
open BalancedCubeLowerBound (coordinateSlice)
open GirthSliceCounting (degreeTwo degreeThree)
open private coordinate_slice_degree_cases coordinate_slice_low_independent low_slice_card_eq_q
  parts_card sum_degrees_parts twice_low_le_three_high paritySide parity_bipartite parity_union from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private reindex reindex_regular reindex_balanced reindex_slice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction

attribute [local instance] Classical.propDecidable

/-- Write the support order as `6 * q`. Each coordinate half has at least
`⌈5q/3⌉` vertices and has the parity of `q`. Independence of the cut
endpoints supplies the lower bound. Equality of the two bipartite degree sums supplies parity. -/
theorem half_cardinality {C : Finset (Q 9)} {q : ℕ} (hC : C.card = 6 * q)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (j : Fin 9) (b : Bool) :
    let N := (C.filter (fun x => x j = b)).card
    5 * q ≤ 3 * N ∧ N % 2 = q % 2 := by
  let p := Equiv.swap j (0 : Fin 9)
  let T := C.image (reindex p)
  let S := coordinateSlice T b
  let G := (hypercube 9).induce (S : Set (Q 9))
  have hreg := reindex_regular hr p
  have hbal := reindex_balanced hb p
  have hdeg : ∀ x, G.degree x = 2 ∨ G.degree x = 3 :=
    fun x => coordinate_slice_degree_cases x.property hreg
  have hind {x y} (hxy : G.Adj x y) (hx : G.degree x = 2) (hy : G.degree y = 2) : False :=
    coordinate_slice_low_independent hreg hbal hxy hx hy
  have hT : T.card = 6 * q := by
    simpa [T, Finset.card_image_of_injective _ (reindex p).injective] using hC
  have hcross : 6 * directionEdges T 0 = T.card := by
    simpa using direction_edge_count (d := 3) T hreg hbal 0
  have hlow : (degreeTwo G Finset.univ).card = q := by
    have he : (degreeTwo G Finset.univ).card = directionEdges T 0 := low_slice_card_eq_q hreg
    omega
  have hsize : Fintype.card (S : Set (Q 9)) = (C.filter (fun x => x j = b)).card := by
    rw [show Fintype.card (S : Set (Q 9)) = S.card by simp]
    dsimp [S, T, p]
    rw [reindex_slice, Finset.card_image_of_injective _ (reindex _).injective]
  have hparts := parts_card G hdeg Finset.univ
  have hdouble := twice_low_le_three_high G hdeg hind
  let L := paritySide S false
  let R := paritySide S true
  have hpart : G.IsBipartiteWith (L : Set _) (R : Set _) := parity_bipartite S
  have hcover : L ∪ R = Finset.univ := parity_union S
  have hpartition (P : ↥(S : Set (Q 9)) → Prop) [DecidablePred P] :
      (L.filter P).card + (R.filter P).card = (Finset.univ.filter P).card := by
    have hd : Disjoint (L.filter P) (R.filter P) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact Set.disjoint_left.mp hpart.disjoint (Finset.mem_filter.mp hx).1
        (Finset.mem_filter.mp hy).1
    rw [← Finset.card_union_of_disjoint hd, ← Finset.filter_union, hcover]
  have hlowParts : (degreeTwo G L).card + (degreeTwo G R).card = q := by
    calc
      _ = (degreeTwo G Finset.univ).card := hpartition (fun v => G.degree v = 2)
      _ = q := hlow
  have hhighParts : (degreeThree G L).card + (degreeThree G R).card =
      (degreeThree G Finset.univ).card := hpartition (fun v => G.degree v = 3)
  have hsum : 2 * (degreeTwo G L).card + 3 * (degreeThree G L).card =
      2 * (degreeTwo G R).card + 3 * (degreeThree G R).card := by
    exact (sum_degrees_parts G hdeg L).symm.trans
      ((SimpleGraph.isBipartiteWith_sum_degrees_eq (s := L) (t := R) hpart).trans
        (sum_degrees_parts G hdeg R))
  rw [hlow, Finset.card_univ, hsize] at hparts
  rw [hlow] at hdouble
  dsimp
  omega

#print axioms half_cardinality

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BalancedHalfCardinality
