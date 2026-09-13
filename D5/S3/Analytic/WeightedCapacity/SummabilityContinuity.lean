/- GID: D5/S3/Analytic/WeightedCapacity/SummabilityContinuity
   generality: G
   mirror-B: D5/B/S3/Analytic/WeightedCapacity/SummabilityContinuity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuity of finite-support dyadic readout at zero forces finite total capacity. -/
import D5.S3.Analytic.WeightedCapacity.DyadicTailFilling
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Constructions
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace D5.S3.Analytic.WeightedCapacity.SummabilityContinuity

open Set Filter
open scoped Topology BigOperators
open D5.S3.Analytic.WeightedCapacity.DyadicTailFilling

/-- Divergent capacity leaves a finite tail carrying one unit of dyadic mass. -/
theorem divergent_capacity_tail_mass (A : ℕ → ℕ) (hM : M A = ⊤) (I : Finset ℕ) :
    ∃ F : Finset ℕ, (∀ n ∈ F, n ∉ I) ∧
      1 ≤ ∑ n ∈ F, (A n : ℝ) / 2 ^ n := by
  classical
  have hunbounded (R : ℝ) : ∃ k, R < prefixSum k A := by
    by_contra hn
    push Not at hn
    have hh : M A ≤ ENNReal.ofReal R := by
      unfold M
      apply iSup_le
      intro N
      apply ENNReal.ofReal_le_ofReal
      exact hn (N + 1)
    rw [hM] at hh
    exact (ne_of_lt ENNReal.ofReal_lt_top) (top_le_iff.mp hh)
  let mass : ℕ → ℝ := fun n => (A n : ℝ) / 2 ^ n
  obtain ⟨k, hk⟩ := hunbounded (1 + ∑ n ∈ I, mass n)
  let F := (Finset.range k).filter (fun n => n ∉ I)
  refine ⟨F, ?_, ?_⟩
  · intro n hn
    exact (Finset.mem_filter.mp hn).2
  · have hsplit :
    (∑ n ∈ Finset.range k, mass n) =
          (∑ n ∈ F, mass n) + (∑ n ∈ (Finset.range k).filter (fun n => n ∈ I), mass n) := by
      have hs := Finset.sum_filter_add_sum_filter_not (Finset.range k) (fun n => n ∈ I) mass
      simpa [F, add_comm] using hs.symm
    have hinter :
        (∑ n ∈ (Finset.range k).filter (fun n => n ∈ I), mass n) ≤ ∑ n ∈ I, mass n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact (Finset.mem_filter.mp hn).2
      · intro n _ _
        dsimp [mass]
        positivity
    have hsum : 1 + ∑ n ∈ I, mass n < ∑ n ∈ Finset.range k, mass n := by
      simpa [prefixSum, mass] using hk
    rw [hsplit] at hsum
    linarith

#print axioms divergent_capacity_tail_mass

end D5.S3.Analytic.WeightedCapacity.SummabilityContinuity
