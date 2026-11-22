/- GID: D5/S1/Words/Patterns/Separable/EndpointSimultaneousLiteralHits
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/EndpointSimultaneousLiteralHits
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Every fixed finite set of offsets is hit with asymptotic probability one. -/

import D5.S1.Words.Patterns.Separable.EndpointCycleHazardAccumulation
import D5.S1.Words.Patterns.Separable.EndpointFiniteLiteralHit

/-! A finite union of failures vanishes without any independence assumption. -/

open Filter MeasureTheory Topology
open scoped BigOperators ENNReal

namespace D5.S1.Words.Patterns.Separable.EndpointSimultaneousLiteralHits

open ActualCycleLaw CutFactorization MinimumCutKernel EndpointCycleHazard
open EndpointCycleHazardAccumulation EndpointPredictableHazard EndpointFiniteLiteralHit
open EndpointFirstCycleHitLimit OccupiedComparison
open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)

private theorem singleton_limit (e : ℤ) :
    Tendsto (literalHitProbability e) atTop (𝓝 1) := by
  apply (finite_avoider_literal_hit_limit_of_stream_hit e).2
  filter_upwards [actual_hazard_accumulation_and_recurrence e] with ω hω
  obtain ⟨k, _, hk⟩ := hω.2 0
  exact ⟨k, hk⟩

/-- Actual probability of a literal hit at each specified offset in the same permutation. -/
noncomputable def simultaneousLiteralHitProbability (S : Finset ℤ) (n : ℕ) : ℝ :=
  actualMass n (fun π : Avoider n => ∀ e ∈ S, hitsDiagonal π.val e)

private theorem pmf_outer_total {α : Type*} (p : PMF α) :
    p.toOuterMeasure Set.univ = 1 :=
  (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)

private theorem pmf_outer_ne_top {α : Type*} (p : PMF α) (T : Set α) :
    p.toOuterMeasure T ≠ ∞ := by
  have h : p.toOuterMeasure T ≤ 1 :=
    (p.toOuterMeasure.mono (Set.subset_univ T)).trans_eq (pmf_outer_total p)
  exact ne_of_lt (h.trans_lt ENNReal.one_lt_top)

private theorem pmf_outer_real_compl {α : Type*} (p : PMF α) (T : Set α) :
    (p.toOuterMeasure Tᶜ).toReal = 1 - (p.toOuterMeasure T).toReal := by
  classical
  have h : p.toOuterMeasure Tᶜ + p.toOuterMeasure T = 1 := by
    rw [p.toOuterMeasure_apply, p.toOuterMeasure_apply, ← ENNReal.tsum_add, ← p.tsum_coe]
    exact tsum_congr fun i => by by_cases hi : i ∈ T <;> simp [hi]
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (pmf_outer_ne_top p _) (pmf_outer_ne_top p _), ENNReal.toReal_one] at hr
  linarith only [hr]

private theorem failure_union_bound (S : Finset ℤ) (n : ℕ) :
    1 - simultaneousLiteralHitProbability S n ≤ ∑ e ∈ S, (1 - literalHitProbability e n) := by
  classical
  let : Nonempty (Avoider n) := ⟨identityAvoider n⟩
  let p := uniformPmf (Avoider n)
  let H (e : ℤ) : Set (Avoider n) := {π | hitsDiagonal π.val e}
  let G : Set (Avoider n) := {π | ∀ e ∈ S, hitsDiagonal π.val e}
  change 1 - (p.toOuterMeasure G).toReal ≤ ∑ e ∈ S, (1 - (p.toOuterMeasure (H e)).toReal)
  simp_rw [← pmf_outer_real_compl]
  have hG : Gᶜ = ⋃ e ∈ S, (H e)ᶜ := by
    ext π
    simp [G, H]
  rw [hG, ← ENNReal.toReal_sum (fun i _ => pmf_outer_ne_top p (H i)ᶜ)]
  apply ENNReal.toReal_mono
  · exact ENNReal.sum_ne_top.mpr (fun i _ => pmf_outer_ne_top p (H i)ᶜ)
  exact measure_biUnion_finset_le (μ := p.toOuterMeasure) S (fun i => (H i)ᶜ)

private theorem simultaneous_le_one (S : Finset ℤ) (n : ℕ) :
    simultaneousLiteralHitProbability S n ≤ 1 := by
  classical
  let : Nonempty (Avoider n) := ⟨identityAvoider n⟩
  let p := uniformPmf (Avoider n)
  let G : Set (Avoider n) := {π | ∀ e ∈ S, hitsDiagonal π.val e}
  change (p.toOuterMeasure G).toReal ≤ 1
  rw [← sub_nonneg, ← pmf_outer_real_compl]
  exact ENNReal.toReal_nonneg

/-- For every fixed finite set of integer offsets, the probability of simultaneous
literal hits in the original uniform separable permutation tends to one. -/
theorem simultaneous_literal_hits_limit (S : Finset ℤ) :
    Tendsto (simultaneousLiteralHitProbability S) atTop (𝓝 1) := by
  have hsum : Tendsto (fun n => ∑ e ∈ S, (1 - literalHitProbability e n)) atTop (𝓝 0) := by
    have hterm (e : ℤ) : Tendsto (fun n => 1 - literalHitProbability e n) atTop (𝓝 0) := by
      simpa only [sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub (singleton_limit e)
    have h := tendsto_finsetSum S (fun e _ => hterm e)
    change Tendsto _ atTop (𝓝 (∑ _e ∈ S, (0 : ℝ))) at h
    rw [Finset.sum_const_zero] at h
    exact h
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [(tendsto_order.1 hsum).2 (1 - a) (sub_pos.mpr ha)] with n hn
    linarith only [hn, failure_union_bound S n]
  · intro a ha
    exact Filter.Eventually.of_forall fun n => (simultaneous_le_one S n).trans_lt ha

#print axioms simultaneous_literal_hits_limit

end D5.S1.Words.Patterns.Separable.EndpointSimultaneousLiteralHits
