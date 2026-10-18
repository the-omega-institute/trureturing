/- GID: D5/S3/Quantum/Fibers/BipartiteBlockade/DiagonalResidual
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/BipartiteBlockade/DiagonalResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two distinct nonlinear neighborhoods admit a nonzero diagonal correlation direction obeying the bipartite compatibility equation. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Fibers.BipartiteBlockade.GeneralCommutator
import D5.S3.Quantum.Fibers.BipartiteBlockade.NeighborhoodIndependence

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators Classical

namespace D5.S3.Quantum.Fibers.BipartiteBlockade.DiagonalResidual

open private alternating_powerset_sum blocking_difference singleton_difference from
  D5.S3.Quantum.Fibers.BipartiteBlockade.NeighborhoodIndependence

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The blocking expectation of a signed diagonal perturbation. -/
def blockMoment (G : SimpleGraph V) (δ : Configuration G → ℝ) (v : V) : ℝ :=
  ∑ S, δ S * (if clear G v S then 1 else 0)

/-- The alternating signed measure on all subconfigurations of N. -/
def subsetDifference (G : SimpleGraph V) (N : Finset V) (S : Configuration G) : ℝ :=
  if S.val ⊆ N then (-1 : ℝ) ^ S.val.card else 0

private theorem subset_configuration_sum (G : SimpleGraph V) (N : Finset V)
    (independent : ∀ u ∈ N, ∀ v ∈ N, ¬G.Adj u v) (f : Finset V → ℝ) :
    (∑ S : Configuration G, if S.val ⊆ N then f S.val else 0) =
      ∑ S ∈ N.powerset, f S := by
  let e : N.powerset → Configuration G := fun S => ⟨S.val, by
    intro u hu v hv
    have hs := Finset.mem_powerset.mp S.property
    exact independent u (hs hu) v (hs hv)⟩
  have he : Function.Injective e := by
    intro S T h
    exact Subtype.ext (congrArg (fun X : Configuration G => X.val) h)
  have hout : ∀ S : Configuration G, S ∉ Set.range e →
      (if S.val ⊆ N then f S.val else 0) = 0 := by
    intro S hS
    split_ifs with hs
    · exact (hS ⟨⟨S.val, Finset.mem_powerset.mpr hs⟩, Subtype.ext rfl⟩).elim
    · rfl
  have hval : ∀ S : N.powerset, f S.val =
      (if (e S).val ⊆ N then f (e S).val else 0) := by
    intro S
    simp only [e, Finset.mem_powerset.mp S.property, ite_true]
  have hsum := Fintype.sum_of_injective e he (fun S => f S.val)
    (fun S : Configuration G => if S.val ⊆ N then f S.val else 0) hout hval
  rw [← hsum, Finset.sum_coe_sort]

private theorem difference_trace (G : SimpleGraph V) (N : Finset V)
    (independent : ∀ u ∈ N, ∀ v ∈ N, ¬G.Adj u v) (large : 2 ≤ N.card) :
    (∑ S, subsetDifference G N S) = 0 := by
  have hn : N ≠ ∅ := by intro h; simp [h] at large
  change (∑ S : Configuration G, if S.val ⊆ N then (-1 : ℝ) ^ S.val.card else 0) = 0
  rw [subset_configuration_sum G N independent (fun S => (-1 : ℝ) ^ S.card),
    alternating_powerset_sum, if_neg hn]

private theorem difference_mean (G : SimpleGraph V) (N : Finset V)
    (independent : ∀ u ∈ N, ∀ v ∈ N, ¬G.Adj u v) (large : 2 ≤ N.card) (v : V) :
    (∑ S, subsetDifference G N S * (if v ∈ S.val then 1 else 0)) = 0 := by
  have hsum : (∑ S, subsetDifference G N S * (if v ∈ S.val then 1 else 0)) =
      ∑ S : Configuration G,
        if S.val ⊆ N then (-1 : ℝ) ^ S.val.card * (if v ∈ S.val then 1 else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro S _
    simp only [subsetDifference, ite_mul, zero_mul]
  rw [hsum, subset_configuration_sum G N independent
    (fun S => (-1 : ℝ) ^ S.card * (if v ∈ S then 1 else 0)),
    singleton_difference N large v]

private theorem difference_block (G : SimpleGraph V) (N : Finset V)
    (independent : ∀ u ∈ N, ∀ v ∈ N, ¬G.Adj u v) (v : V) :
    blockMoment G (subsetDifference G N) v =
      if N ⊆ G.neighborFinset v then 1 else 0 := by
  have hc : ∀ S : Configuration G, clear G v S ↔ Disjoint (G.neighborFinset v) S.val := by
    intro S
    constructor
    · intro h
      rw [Finset.disjoint_left]
      intro u hu hS
      exact h u hS (by simpa using hu)
    · intro h u hu huv
      exact Finset.disjoint_left.mp h (by simpa using huv) hu
  have hsum : blockMoment G (subsetDifference G N) v =
      ∑ S : Configuration G, if S.val ⊆ N then
        (-1 : ℝ) ^ S.val.card * (if Disjoint (G.neighborFinset v) S.val then 1 else 0)
        else 0 := by
    unfold blockMoment
    apply Finset.sum_congr rfl
    intro S _
    rw [hc S]
    by_cases hs : S.val ⊆ N <;> by_cases hd : Disjoint (G.neighborFinset v) S.val <;>
      simp [subsetDifference, hs, hd]
  rw [hsum, subset_configuration_sum G N independent
    (fun S => (-1 : ℝ) ^ S.card * (if Disjoint (G.neighborFinset v) S then 1 else 0)),
    blocking_difference]

private theorem neighborhood_independent (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v) (v : V) :
    ∀ u ∈ G.neighborFinset v, ∀ w ∈ G.neighborFinset v, ¬G.Adj u w := by
  intro u hu w hw huw
  have h₁ := proper v u (by simpa using hu)
  have h₂ := proper v w (by simpa using hw)
  have h₃ := proper u w huw
  cases hv : color v <;> cases hu' : color u <;> cases hw' : color w <;> simp_all

private theorem same_color_of_common_neighbor (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v)
    {u v w : V} (huw : G.Adj u w) (hvw : G.Adj v w) : color u = color v := by
  have h₁ := proper u w huw
  have h₂ := proper v w hvw
  cases hu : color u <;> cases hv : color v <;> cases hw : color w <;> simp_all

private def signedWeight (color : V → Bool) (Ω : V → ℝ) (v : V) : ℝ :=
  (if color v then 1 else -1) * Ω v ^ 2

private def coefficient (G : SimpleGraph V) (color : V → Bool) (Ω : V → ℝ)
    (N : Finset V) : ℝ :=
  ∑ v, signedWeight color Ω v * (if N ⊆ G.neighborFinset v then 1 else 0)

private theorem coefficient_ne_zero (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v)
    (Ω : V → ℝ) (nonzero : ∀ v, Ω v ≠ 0) (base : V)
    (large : 2 ≤ (G.neighborFinset base).card) :
    coefficient G color Ω (G.neighborFinset base) ≠ 0 := by
  have hne : (G.neighborFinset base).Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨w, hw⟩ := hne
  have hsign : ∀ v, G.neighborFinset base ⊆ G.neighborFinset v → color base = color v := by
    intro v hv
    exact same_color_of_common_neighbor G color proper (by simpa using hw)
      (by simpa using hv hw)
  have hfactor : coefficient G color Ω (G.neighborFinset base) =
      (if color base then 1 else -1) *
        ∑ v, Ω v ^ 2 * (if G.neighborFinset base ⊆ G.neighborFinset v then 1 else 0) := by
    unfold coefficient
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : G.neighborFinset base ⊆ G.neighborFinset v
    · simp [signedWeight, hv, ← hsign v hv]
    · simp [signedWeight, hv]
  rw [hfactor]
  apply mul_ne_zero
  · cases hb : color base <;> norm_num [hb]
  · apply ne_of_gt
    apply Finset.sum_pos'
    · intro v _
      split_ifs <;> positivity
    · exact ⟨base, Finset.mem_univ _, by simpa using sq_pos_of_ne_zero (nonzero base)⟩

private theorem ordered_diagonal_residual (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v)
    (Ω : V → ℝ) (nonzero : ∀ v, Ω v ≠ 0) (u w : V)
    (largeU : 2 ≤ (G.neighborFinset u).card)
    (largeW : 2 ≤ (G.neighborFinset w).card)
    (not_subset : ¬G.neighborFinset w ⊆ G.neighborFinset u) :
    ∃ δ : Configuration G → ℝ,
      (∑ S, δ S) = 0 ∧
      (∀ v, (∑ S, δ S * (if v ∈ S.val then 1 else 0)) = 0) ∧
      (∑ v, (if color v then 1 else -1) * Ω v ^ 2 * blockMoment G δ v) = 0 ∧
      ∃ v, blockMoment G δ v ≠ 0 := by
  let N := G.neighborFinset u
  let M := G.neighborFinset w
  let L := coefficient G color Ω
  let δ : Configuration G → ℝ := fun S =>
    L M * subsetDifference G N S - L N * subsetDifference G M S
  have hN := neighborhood_independent G color proper u
  have hM := neighborhood_independent G color proper w
  have hblock : ∀ v, blockMoment G δ v =
      L M * (if N ⊆ G.neighborFinset v then 1 else 0) -
      L N * (if M ⊆ G.neighborFinset v then 1 else 0) := by
    intro v
    unfold blockMoment
    simp only [δ, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [show (∑ S, subsetDifference G N S * (if clear G v S then 1 else 0)) =
      blockMoment G (subsetDifference G N) v from rfl,
      show (∑ S, subsetDifference G M S * (if clear G v S then 1 else 0)) =
      blockMoment G (subsetDifference G M) v from rfl,
      difference_block G N hN v, difference_block G M hM v]
  refine ⟨δ, ?_, ?_, ?_, ?_⟩
  · simp only [δ, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [difference_trace G N hN largeU, difference_trace G M hM largeW]
    ring
  · intro v
    simp only [δ, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [difference_mean G N hN largeU v, difference_mean G M hM largeW v]
    ring
  · simp_rw [hblock, mul_sub]
    rw [Finset.sum_sub_distrib]
    have h₁ : ∀ v, (if color v then (1 : ℝ) else -1) * Ω v ^ 2 *
        (L M * (if N ⊆ G.neighborFinset v then 1 else 0)) =
        L M * (signedWeight color Ω v * (if N ⊆ G.neighborFinset v then 1 else 0)) := by
      intro v
      unfold signedWeight
      ring
    have h₂ : ∀ v, (if color v then (1 : ℝ) else -1) * Ω v ^ 2 *
        (L N * (if M ⊆ G.neighborFinset v then 1 else 0)) =
        L N * (signedWeight color Ω v * (if M ⊆ G.neighborFinset v then 1 else 0)) := by
      intro v
      unfold signedWeight
      ring
    simp_rw [h₁, h₂, ← Finset.mul_sum]
    change L M * L N - L N * L M = 0
    ring
  · refine ⟨u, ?_⟩
    rw [hblock]
    have hn : N ⊆ G.neighborFinset u := Finset.Subset.refl _
    have hm : ¬M ⊆ G.neighborFinset u := not_subset
    simp only [hn, hm, ite_true, ite_false, mul_one, mul_zero, sub_zero]
    exact coefficient_ne_zero G color proper Ω nonzero w largeW

/-- Any two distinct open neighborhoods of size at least two yield an actual
signed diagonal direction preserving trace, every single-site mean, and the
unique bipartite compatibility functional, while changing a blocking mean. -/
theorem diagonal_residual_of_distinct_neighborhoods
    (G : SimpleGraph V) (color : V → Bool)
    (proper : ∀ u v, G.Adj u v → color u ≠ color v)
    (Ω : V → ℝ) (nonzero : ∀ v, Ω v ≠ 0) (u w : V)
    (largeU : 2 ≤ (G.neighborFinset u).card)
    (largeW : 2 ≤ (G.neighborFinset w).card)
    (distinct : G.neighborFinset u ≠ G.neighborFinset w) :
    ∃ δ : Configuration G → ℝ,
      (∑ S, δ S) = 0 ∧
      (∀ v, (∑ S, δ S * (if v ∈ S.val then 1 else 0)) = 0) ∧
      (∑ v, (if color v then 1 else -1) * Ω v ^ 2 * blockMoment G δ v) = 0 ∧
      ∃ v, blockMoment G δ v ≠ 0 := by
  by_cases h : G.neighborFinset w ⊆ G.neighborFinset u
  · have h' : ¬G.neighborFinset u ⊆ G.neighborFinset w := by
      intro hu
      exact distinct (Finset.Subset.antisymm hu h)
    exact ordered_diagonal_residual G color proper Ω nonzero w u largeW largeU h'
  · exact ordered_diagonal_residual G color proper Ω nonzero u w largeU largeW h

/-- info: 'D5.S3.Quantum.Fibers.BipartiteBlockade.DiagonalResidual.diagonal_residual_of_distinct_neighborhoods' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diagonal_residual_of_distinct_neighborhoods

end D5.S3.Quantum.Fibers.BipartiteBlockade.DiagonalResidual
