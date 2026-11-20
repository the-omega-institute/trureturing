import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyHalfExclusion
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwoGrayComponents
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BalancedHalfCardinality
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedExclusion
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourHalfEmbedding
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixHalfEmbedding

/-! The surviving large component in a hypothetical 258-vertex candidate
has coordinate halves of even cardinality between 24 and 48 when its order is 72. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeLowerBound (coordinateSlice)
open TwoBalancedComponents (componentFinset)
open private componentFinset_subset componentFinset_neighbor_closed from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents
open private selected_neighbor_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation
open private reindex reindex_adj reindex_regular reindex_balanced reindex_slice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
attribute [local instance] Classical.propDecidable

private theorem no_twenty_two_half {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (j : Fin 9) (b : Bool) (hs : (C.filter (fun x => x j = b)).card = 22) : False := by
  classical
  let p := Equiv.swap j (0 : Fin 9)
  let g := reindex p
  have hC' : (C.image g).card = 72 := by rw [Finset.card_image_of_injective _ g.injective, hC]
  have hs' : (coordinateSlice (C.image g) b).card = 22 := by
    change (coordinateSlice (C.image (reindex (Equiv.swap j 0))) b).card = 22
    rw [reindex_slice, Finset.card_image_of_injective _ g.injective, hs]
  exact CoordinateHalves.Q9TwentyTwoPairedExclusion.no_twenty_two_half hC'
    (reindex_regular hr p) (reindex_balanced hb p) b hs'

/-- A 258-vertex induced subcubic set has a Huang-balanced cubic component
of order at least 72. If that component has order 72, every coordinate
half has even cardinality between 24 and 48, inclusive. -/
theorem exists_large_component_without_thin_half (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ v : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree v ≤ 3) :
    ∃ K : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent,
      let C := componentFinset U K
      ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3 ∧
        IsBalanced C ∧ 72 ≤ C.card ∧ (C.card = 72 → ∀ (j : Fin 9) (b : Bool),
          let N := (C.filter (fun x => x j = b)).card
          24 ≤ N ∧ N ≤ 48 ∧ N % 2 = 0) := by
  classical
  obtain ⟨K, hr, hb, hc⟩ := Q9TwoGrayComponents.exists_large_balanced_component U hU hdeg
  refine ⟨K, hr, hb, hc, fun heq j b => ?_⟩
  have hdegree (x : Q 9) (hx : x ∈ U) : (U.filter ((hypercube 9).Adj x)).card ≤ 3 := by
    have he : U.filter ((hypercube 9).Adj x) = (hypercube 9).neighborFinset x ∩ U := by
      ext y
      simp [SimpleGraph.mem_neighborFinset, and_comm]
    rw [he, selected_neighbor_card hx]
    exact hdeg ⟨x, hx⟩
  let C := componentFinset U K
  have h72 : C.card = 6 * 12 := heq
  have half_min (side : Bool) : 24 ≤ (C.filter (fun x => x j = side)).card := by
    obtain ⟨hbound, hparity⟩ :=
      CoordinateHalves.BalancedHalfCardinality.half_cardinality h72 hr hb j side
    have htwenty := no_twenty_half hU heq hr hb (componentFinset_subset U K)
      (componentFinset_neighbor_closed U K) hdegree j side
    have htwentyTwo : (C.filter (fun x => x j = side)).card ≠ 22 :=
      no_twenty_two_half heq hr hb j side
    change 5 * 12 ≤ 3 * (C.filter (fun x => x j = side)).card at hbound
    change (C.filter (fun x => x j = side)).card % 2 = 12 % 2 at hparity
    change (C.filter (fun x => x j = side)).card ≠ 20 at htwenty
    omega
  have hsum : (C.filter (fun x => x j = b)).card +
      (C.filter (fun x => x j = !b)).card = C.card := by
    have hd : Disjoint (C.filter (fun x => x j = b)) (C.filter (fun x => x j = !b)) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      have hf := (Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hy).2
      cases b <;> simp at hf
    have hu : C.filter (fun x => x j = b) ∪ C.filter (fun x => x j = !b) = C := by
      ext x
      cases b <;> cases hx : x j <;> simp [hx]
    rw [← Finset.card_union_of_disjoint hd, hu]
  obtain ⟨_, hp⟩ :=
    CoordinateHalves.BalancedHalfCardinality.half_cardinality h72 hr hb j b
  change (C.filter (fun x => x j = b)).card % 2 = 12 % 2 at hp
  have hmin := half_min b
  have hother := half_min (!b)
  change C.card = 72 at heq
  change 24 ≤ (C.filter (fun x => x j = b)).card ∧
    (C.filter (fun x => x j = b)).card ≤ 48 ∧
    (C.filter (fun x => x j = b)).card % 2 = 0
  omega

#print axioms exists_large_component_without_thin_half

/-- At order 72 the balanced cubic component has even coordinate halves
of sizes 26 through 46. -/
theorem exists_large_component_coordinate_halves_twenty_six_to_forty_six
    (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ v : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree v ≤ 3) :
    ∃ K : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent,
      let C := componentFinset U K
      ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3 ∧ IsBalanced C ∧
        72 ≤ C.card ∧ (C.card = 72 → ∀ (j : Fin 9) (b : Bool),
          let N := (C.filter (fun x => x j = b)).card
          26 ≤ N ∧ N ≤ 46 ∧ N % 2 = 0) := by
  classical
  obtain ⟨K, hr, hb, hc, hbounds⟩ := exists_large_component_without_thin_half U hU hdeg
  let C := componentFinset U K
  refine ⟨K, hr, hb, hc, fun h72 j b => ?_⟩
  let p := Equiv.swap j (0 : Fin 9)
  let g := reindex p
  have hC' : (C.image g).card = 72 := by rw [Finset.card_image_of_injective _ g.injective, h72]
  have hne (side : Bool) : (C.filter (fun x => x j = side)).card ≠ 24 := by
    have hn := CoordinateHalves.Q9TwentyFourHalfEmbedding.no_twenty_four_half hC'
      (reindex_regular hr p) (reindex_balanced hb p) side
    change (coordinateSlice (C.image (reindex (Equiv.swap j 0))) side).card ≠ 24 at hn
    rwa [reindex_slice, Finset.card_image_of_injective _ g.injective] at hn
  have hsum : (C.filter (fun x => x j = b)).card +
      (C.filter (fun x => x j = !b)).card = C.card := by
    have he : (C.filter (fun x => x j = !b)) = C.filter (fun x => ¬x j = b) := by
      ext x
      cases b <;> cases hx : x j <;> simp [hx]
    rw [he]
    exact Finset.card_filter_add_card_filter_not (s := C) (fun x => x j = b)
  have hx := hbounds h72 j b
  have hy := hbounds h72 j (!b)
  change 24 ≤ (C.filter (fun x => x j = b)).card ∧
    (C.filter (fun x => x j = b)).card ≤ 48 ∧
    (C.filter (fun x => x j = b)).card % 2 = 0 at hx
  change 24 ≤ (C.filter (fun x => x j = !b)).card ∧
    (C.filter (fun x => x j = !b)).card ≤ 48 ∧
    (C.filter (fun x => x j = !b)).card % 2 = 0 at hy
  change C.card = 72 at h72
  have hxb := hne b
  have hyb := hne (!b)
  change 26 ≤ (C.filter (fun x => x j = b)).card ∧
    (C.filter (fun x => x j = b)).card ≤ 46 ∧
    (C.filter (fun x => x j = b)).card % 2 = 0
  omega

#print axioms exists_large_component_coordinate_halves_twenty_six_to_forty_six

/-- At order 72 the balanced cubic component has even coordinate halves
of sizes 28 through 44. -/
theorem exists_large_component_coordinate_halves_twenty_eight_to_forty_four
    (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ v : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree v ≤ 3) :
    ∃ K : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent,
      let C := componentFinset U K
      ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3 ∧ IsBalanced C ∧
        72 ≤ C.card ∧ (C.card = 72 → ∀ (j : Fin 9) (b : Bool),
          let N := (C.filter (fun x => x j = b)).card
          28 ≤ N ∧ N ≤ 44 ∧ N % 2 = 0) := by
  classical
  obtain ⟨K, hr, hb, hc, hbounds⟩ :=
    exists_large_component_coordinate_halves_twenty_six_to_forty_six U hU hdeg
  let C := componentFinset U K
  refine ⟨K, hr, hb, hc, fun h72 j b => ?_⟩
  let p := Equiv.swap j (0 : Fin 9)
  let g := reindex p
  have hC' : (C.image g).card = 72 := by
    rw [Finset.card_image_of_injective _ g.injective, h72]
  have hne (side : Bool) : (C.filter (fun x => x j = side)).card ≠ 26 := by
    intro he
    have hcut : (coordinateSlice (C.image g) side).card = 26 := by
      change (coordinateSlice (C.image (reindex (Equiv.swap j 0))) side).card = 26
      rwa [reindex_slice, Finset.card_image_of_injective _ g.injective]
    obtain ⟨k, color, hk⟩ :=
      CoordinateHalves.Q9TwentySixHalfEmbedding.exists_twenty_cut_of_twenty_six hC'
        (reindex_regular hr p) (reindex_balanced hb p) side hcut
    rw [Finset.filter_image, Finset.card_image_of_injective _ g.injective] at hk
    change (C.filter (fun x => x (p.symm k) = color)).card = 20 at hk
    have hmin : 26 ≤ (C.filter (fun x => x (p.symm k) = color)).card :=
      (hbounds h72 (p.symm k) color).1
    omega
  have hsum : (C.filter (fun x => x j = b)).card +
      (C.filter (fun x => x j = !b)).card = C.card := by
    have he : (C.filter (fun x => x j = !b)) = C.filter (fun x => ¬x j = b) := by
      ext x
      cases b <;> cases hx : x j <;> simp [hx]
    rw [he]
    exact Finset.card_filter_add_card_filter_not (s := C) (fun x => x j = b)
  have hx := hbounds h72 j b
  have hy := hbounds h72 j (!b)
  have hxb := hne b
  have hyb := hne (!b)
  change C.card = 72 at h72
  change 26 ≤ (C.filter (fun x => x j = b)).card ∧
    (C.filter (fun x => x j = b)).card ≤ 46 ∧
    (C.filter (fun x => x j = b)).card % 2 = 0 at hx
  change 26 ≤ (C.filter (fun x => x j = !b)).card ∧
    (C.filter (fun x => x j = !b)).card ≤ 46 ∧
    (C.filter (fun x => x j = !b)).card % 2 = 0 at hy
  change 28 ≤ (C.filter (fun x => x j = b)).card ∧
    (C.filter (fun x => x j = b)).card ≤ 44 ∧
    (C.filter (fun x => x j = b)).card % 2 = 0
  omega

#print axioms exists_large_component_coordinate_halves_twenty_eight_to_forty_four

end D5.S3.Combinatorics.Graph.HypercubeCritical
