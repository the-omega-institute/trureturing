/- GID: D5/S3/Quantum/Fibers/BipartiteBlockade/NeighborhoodIndependence
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/BipartiteBlockade/NeighborhoodIndependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Distinct independent blocking neighborhoods are linearly independent modulo the vacuum and single-site occupations. -/

import Mathlib

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

namespace D5.S3.Quantum.Fibers.BipartiteBlockade.NeighborhoodIndependence

variable {V : Type*} [DecidableEq V]

private theorem alternating_powerset_sum (N : Finset V) :
    (∑ S ∈ N.powerset, (-1 : ℝ) ^ S.card) = if N = ∅ then 1 else 0 := by
  exact_mod_cast (Finset.sum_powerset_neg_one_pow_card (x := N))

private theorem blocking_difference (N M : Finset V) :
    (∑ S ∈ N.powerset,
      (-1 : ℝ) ^ S.card * (if Disjoint M S then 1 else 0)) =
        if N ⊆ M then 1 else 0 := by
  have hfilter : N.powerset.filter (fun S => Disjoint M S) = (N \ M).powerset := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_sdiff]
    exact and_congr_right fun _ => disjoint_comm
  calc
    (∑ S ∈ N.powerset, (-1 : ℝ) ^ S.card * (if Disjoint M S then 1 else 0)) =
        ∑ S ∈ N.powerset.filter (fun S => Disjoint M S), (-1 : ℝ) ^ S.card := by
      simp only [Finset.sum_filter, mul_ite, mul_one, mul_zero]
    _ = ∑ S ∈ (N \ M).powerset, (-1 : ℝ) ^ S.card := by rw [hfilter]
    _ = if N ⊆ M then 1 else 0 := by
      rw [alternating_powerset_sum]
      simp only [Finset.sdiff_eq_empty_iff_subset]

private theorem singleton_difference (N : Finset V) (large : 2 ≤ N.card) (v : V) :
    (∑ S ∈ N.powerset,
      (-1 : ℝ) ^ S.card * (if v ∈ S then 1 else 0)) = 0 := by
  have hn : N ≠ ∅ := by intro h; simp [h] at large
  have hnot : ¬N ⊆ {v} := by
    intro h
    have := Finset.card_le_card h
    simp only [Finset.card_singleton] at this
    omega
  have h := blocking_difference N {v}
  rw [if_neg hnot] at h
  have hrewrite : ∀ S : Finset V,
      (if v ∈ S then (1 : ℝ) else 0) = 1 - (if Disjoint ({v} : Finset V) S then 1 else 0) := by
    intro S
    by_cases hv : v ∈ S <;> simp [hv]
  simp_rw [hrewrite, mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [alternating_powerset_sum, if_neg hn, h]
  ring

private theorem affine_difference (N : Finset V) (large : 2 ≤ N.card)
    (constant : ℝ) (single : V → ℝ) :
    (∑ S ∈ N.powerset,
      (-1 : ℝ) ^ S.card * (constant + ∑ v ∈ S, single v)) = 0 := by
  have hn : N ≠ ∅ := by intro h; simp [h] at large
  have hrewrite : ∀ S ∈ N.powerset, (∑ v ∈ S, single v) =
      ∑ v ∈ N, (if v ∈ S then (1 : ℝ) else 0) * single v := by
    intro S hS
    have hs := Finset.mem_powerset.mp hS
    have heq : N.filter (· ∈ S) = S := by
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hs h, h⟩⟩
    simp only [ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter, heq]
  calc
    _ = ∑ S ∈ N.powerset, (-1 : ℝ) ^ S.card *
        (constant + ∑ v ∈ N, (if v ∈ S then (1 : ℝ) else 0) * single v) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [hrewrite S hS]
    _ = 0 := by
      simp_rw [mul_add, Finset.mul_sum]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, alternating_powerset_sum, if_neg hn]
      simp only [zero_mul, zero_add]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro v _
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul, singleton_difference N large v, zero_mul]

/-- A relation between distinct blocking functions on all independent
configurations cannot be hidden in the constant and single-site occupations.
The neighborhoods need only be independent sets of size at least two;
connectedness and bipartiteness are not required for this algebraic statement. -/
theorem blocking_independent_mod_singletons
    (G : SimpleGraph V) (F : Finset (Finset V))
    (independent : ∀ N ∈ F, ∀ u ∈ N, ∀ v ∈ N, ¬G.Adj u v)
    (large : ∀ N ∈ F, 2 ≤ N.card)
    (coefficient : Finset V → ℝ) (constant : ℝ) (single : V → ℝ)
    (relation : ∀ S : Finset V, (∀ u ∈ S, ∀ v ∈ S, ¬G.Adj u v) →
      (∑ N ∈ F, coefficient N * (if Disjoint N S then 1 else 0)) =
        constant + ∑ v ∈ S, single v) :
    ∀ N ∈ F, coefficient N = 0 := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨K, hK, hcK⟩ := h
  let support := F.filter (fun N => coefficient N ≠ 0)
  have hsupport : support.Nonempty := ⟨K, by simp [support, hK, hcK]⟩
  obtain ⟨N, hN, hmax⟩ := Finset.exists_max_image support Finset.card hsupport
  have hNF : N ∈ F := (Finset.mem_filter.mp hN).1
  have hcN : coefficient N ≠ 0 := (Finset.mem_filter.mp hN).2
  have hrelation :
      (∑ S ∈ N.powerset, (-1 : ℝ) ^ S.card *
        ∑ M ∈ F, coefficient M * (if Disjoint M S then 1 else 0)) = 0 := by
    calc
      _ = ∑ S ∈ N.powerset, (-1 : ℝ) ^ S.card *
          (constant + ∑ v ∈ S, single v) := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [relation S]
        intro u hu v hv
        have hs := Finset.mem_powerset.mp hS
        exact independent N hNF u (hs hu) v (hs hv)
      _ = 0 := affine_difference N (large N hNF) constant single
  have hsum :
      (∑ S ∈ N.powerset, (-1 : ℝ) ^ S.card *
        ∑ M ∈ F, coefficient M * (if Disjoint M S then 1 else 0)) =
      ∑ M ∈ F, coefficient M * (if N ⊆ M then 1 else 0) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro M hM
    rw [← blocking_difference N M, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    ring
  rw [hsum] at hrelation
  have hisolate : (∑ M ∈ F, coefficient M * (if N ⊆ M then 1 else 0)) = coefficient N := by
    rw [Finset.sum_eq_single N]
    · simp
    · intro M hM hne
      by_cases hcM : coefficient M = 0
      · simp [hcM]
      · have hMS : M ∈ support := by simp [support, hM, hcM]
        have hnot : ¬N ⊆ M := by
          intro hsub
          exact hne (Finset.eq_of_subset_of_card_le hsub (hmax M hMS)).symm
        simp [hnot]
    · exact fun h => (h hNF).elim
  exact hcN (hisolate.symm.trans hrelation)

/-- info: 'D5.S3.Quantum.Fibers.BipartiteBlockade.NeighborhoodIndependence.blocking_independent_mod_singletons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms blocking_independent_mod_singletons

end D5.S3.Quantum.Fibers.BipartiteBlockade.NeighborhoodIndependence
