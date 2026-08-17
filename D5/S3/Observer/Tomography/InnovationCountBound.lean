/- GID: D5/S3/Observer/Tomography/InnovationCountBound
   generality: G
   mirror-B: D5/B/S3/Observer/Tomography/InnovationCountBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixed-size innovations are bounded in count by the total information budget. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Real

/- Library-search audit trail (2026-08-17):
   * Repository searches for innovation counts, threshold budgets, and superlevel sets found no
     equivalent D5 declaration.
   * Two natural-language `smart_search.sh` queries found no declaration-name match in pinned
     Mathlib. Local type-and-name search found `Finset.card_nsmul_le_sum`,
     `Summable.sum_le_tsum`, and `Summable.tendsto_atTop_zero`; all three are applied below.
-/

namespace D5.S3.Observer.Tomography.InnovationCountBound

/-- For a nonnegative summable innovation sequence with total budget at most `H`, the number of
levels carrying innovation at least `ε` is at most `H / ε`. -/
theorem large_innovation_count_le_budget_div
    (innovation : ℕ → ℝ) (H ε : ℝ)
    (hNonneg : ∀ k, 0 ≤ innovation k)
    (hSummable : Summable innovation)
    (hBudget : ∑' k, innovation k ≤ H)
    (hε : 0 < ε) :
    (({k | ε ≤ innovation k} : Set ℕ).ncard : ℝ) ≤ H / ε := by
  have hZero := hSummable.tendsto_atTop_zero
  simp only [Metric.tendsto_atTop, Real.dist_eq, sub_zero] at hZero
  obtain ⟨N, hN⟩ := hZero ε hε
  have hFinite : ({k | ε ≤ innovation k} : Set ℕ).Finite := by
    apply (Set.finite_Iio N).subset
    intro k hk
    simp only [Set.mem_setOf_eq] at hk
    by_contra hkN
    have hNk : N ≤ k := Nat.le_of_not_gt hkN
    have hAbs : |innovation k| < ε := hN k hNk
    exact (not_lt_of_ge hk) ((le_abs_self (innovation k)).trans_lt hAbs)
  rw [Set.ncard_eq_toFinset_card _ hFinite]
  apply (le_div_iff₀ hε).2
  calc
    (hFinite.toFinset.card : ℝ) * ε ≤ hFinite.toFinset.sum innovation := by
      simpa [nsmul_eq_mul] using
        Finset.card_nsmul_le_sum hFinite.toFinset innovation ε fun k hk =>
          (hFinite.mem_toFinset.mp hk)
    _ ≤ ∑' k, innovation k :=
      hSummable.sum_le_tsum hFinite.toFinset fun k _ => hNonneg k
    _ ≤ H := hBudget

#print axioms large_innovation_count_le_budget_div

end D5.S3.Observer.Tomography.InnovationCountBound
