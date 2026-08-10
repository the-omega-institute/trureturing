/- GID: D5/S3/Analytic/PrimeCashflowCost
   generality: G
   mirror-B: D5/B/S3/Analytic/PrimeCashflowCost
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The cumulative cashflow cost of a signed prime-event stream strictly increases at every nonzero event, giving a total-variation time arrow. -/

import Mathlib

namespace D5.S3.Analytic.PrimeCashflowCost

abbrev PrimeIndex := {p : ℕ // Nat.Prime p}
abbrev PrimeEvent := PrimeIndex →₀ ℤ

noncomputable def eventLength (u : PrimeEvent) : ℝ :=
  ∑ p ∈ u.support, |(u p : ℝ)| * Real.log p.1

noncomputable def cashflowCost (events : ℕ → PrimeEvent) (t : ℕ) : ℝ :=
  ∑ tau ∈ Finset.range t, eventLength (events tau)

theorem eventLength_pos {u : PrimeEvent} (hu : u ≠ 0) : 0 < eventLength u := by
  classical
  obtain ⟨p, hp⟩ := Finsupp.ne_iff.mp hu
  have hp_mem : p ∈ u.support := Finsupp.mem_support_iff.mpr hp
  have hlog_nonneg : ∀ q ∈ u.support, 0 ≤ Real.log q.1 := by
    intro q _
    exact Real.log_nonneg (by exact_mod_cast q.property.one_le)
  have hp_cast : (u p : ℝ) ≠ 0 := by exact_mod_cast hp
  have hp_log : 0 < Real.log p.1 := Real.log_pos (by exact_mod_cast p.property.one_lt)
  apply Finset.sum_pos'
  · exact fun q hq => mul_nonneg (abs_nonneg _) (hlog_nonneg q hq)
  · exact ⟨p, hp_mem, mul_pos (abs_pos.mpr hp_cast) hp_log⟩

theorem cashflow_cost_strict_at_event
    (events : ℕ → PrimeEvent) (t : ℕ) (ht : events t ≠ 0) :
    cashflowCost events t < cashflowCost events (t + 1) := by
  rw [cashflowCost, cashflowCost, Finset.sum_range_succ]
  exact lt_add_of_pos_right _ (eventLength_pos ht)

end D5.S3.Analytic.PrimeCashflowCost
