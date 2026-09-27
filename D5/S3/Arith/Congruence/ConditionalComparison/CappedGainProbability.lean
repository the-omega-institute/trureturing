/- GID: D5/S3/Arith/Congruence/ConditionalComparison/CappedGainProbability
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: CappedGainProbability. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/CappedGainProbability.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.FiniteProbability

namespace Erdos7.FiniteLaw

variable {Ω ι : Type*} [Fintype Ω]

theorem prob_mono (μ : FiniteLaw Ω) (A B : Ω → Prop)
    [DecidablePred A] [DecidablePred B] (h : ∀ ω, A ω → B ω) : μ.prob A ≤ μ.prob B := by
  apply μ.expect_mono
  intro ω
  by_cases hA : A ω
  · simp [hA, h ω hA]
  · simp only [hA, if_false]
    positivity

theorem prob_exists_finset_le_sum (μ : FiniteLaw Ω) (S : Finset ι)
    (A : ι → Ω → Prop) [∀ i, DecidablePred (A i)] :
    μ.prob (fun ω ↦ ∃ i ∈ S, A i ω) ≤ ∑ i ∈ S, μ.prob (A i) := by
  classical
  have hpoint : ∀ ω, (if ∃ i ∈ S, A i ω then (1 : ℚ) else 0) ≤
      ∑ i ∈ S, if A i ω then 1 else 0 := by
    intro ω
    by_cases h : ∃ i ∈ S, A i ω
    · obtain ⟨i, hi, hAi⟩ := h
      rw [if_pos ⟨i, hi, hAi⟩]
      have hsum := Finset.single_le_sum (f := fun j ↦ if A j ω then (1 : ℚ) else 0)
        (fun j _ ↦ by positivity) hi
      simpa only [hAi, if_true] using hsum
    · rw [if_neg h]
      exact Finset.sum_nonneg fun i _ ↦ by positivity
  have h := μ.expect_mono hpoint
  rw [μ.expect_finset_sum] at h
  exact h

theorem one_le_sum_prob_of_cover (μ : FiniteLaw Ω) (S : Finset ι)
    (A : ι → Ω → Prop) [∀ i, DecidablePred (A i)]
    (hcover : ∀ ω, ∃ i ∈ S, A i ω) : 1 ≤ ∑ i ∈ S, μ.prob (A i) := by
  classical
  have h := μ.prob_exists_finset_le_sum S A
  have he : μ.prob (fun ω ↦ ∃ i ∈ S, A i ω) = 1 := by
    unfold prob
    simp only [hcover, if_true, expect_const]
  rwa [he] at h

end Erdos7.FiniteLaw
