/- GID: D5/S3/Analytic/Toroidal/InnernessSelfImprovement
   generality: G
   mirror-B: D5/B/S3/Analytic/Toroidal/InnernessSelfImprovement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Iterated strict innerness improvement reaching zero yields innerness at every positive width. -/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Topology.Order.Real

/- Library-search audit trail (2026-09-02):
   * Repository searches found `ToroidalInnerThresholdIdentity`, which identifies
     the inner and toroidal thresholds and characterizes their vanishing. It
     does not provide an iterative self-improvement principle.
   * Searches for innerness improvement, threshold iteration, semantic
     generalizations, and arbitrary predicates stable under a decreasing map
     found no equivalent D5 declaration.
   * Pinned Mathlib supplies `Function.iterate_succ_apply'` and
     `Filter.Tendsto.eventually_lt_const`; both are used directly.
   * Strict decrease alone does not force iterates to tend to zero for a
     discontinuous map. The convergence of the orbit from one half is therefore
     an explicit hypothesis rather than an invalid consequence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Toroidal.InnernessSelfImprovement

open Filter

/-- If eventual innerness at each positive threshold improves to a strictly
smaller positive threshold and the iterated thresholds converge to zero, then
innerness holds at every positive width. -/
theorem innerness_self_improvement
    (innerAt : ℝ → Prop) (F : ℝ → ℝ)
    (hInitial : ∀ omega : ℝ, (1 : ℝ) / 2 < omega → innerAt omega)
    (hPositive : ∀ a : ℝ, 0 < a → a ≤ (1 : ℝ) / 2 → 0 < F a)
    (hDecrease : ∀ a : ℝ, 0 < a → a ≤ (1 : ℝ) / 2 → F a < a)
    (hImprove : ∀ a : ℝ, 0 < a → a ≤ (1 : ℝ) / 2 →
      (∀ omega : ℝ, a < omega → innerAt omega) →
      ∀ omega : ℝ, F a < omega → innerAt omega)
    (hConverges : Tendsto
      (fun n : ℕ => (F^[n]) ((1 : ℝ) / 2)) atTop (nhds 0)) :
    ∀ omega : ℝ, 0 < omega → innerAt omega := by
  have hOrbit : ∀ n : ℕ,
      0 < (F^[n]) ((1 : ℝ) / 2) ∧
        (F^[n]) ((1 : ℝ) / 2) ≤ (1 : ℝ) / 2 ∧
        ∀ omega : ℝ,
          (F^[n]) ((1 : ℝ) / 2) < omega → innerAt omega := by
    intro n
    induction n with
    | zero =>
        simp only [Function.iterate_zero_apply]
        exact ⟨by norm_num, le_rfl, hInitial⟩
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        have hNextPositive := hPositive _ ih.1 ih.2.1
        have hNextLt := hDecrease _ ih.1 ih.2.1
        exact ⟨hNextPositive, hNextLt.le.trans ih.2.1,
          hImprove _ ih.1 ih.2.1 ih.2.2⟩
  intro omega hOmega
  obtain ⟨n, hn⟩ := (hConverges.eventually_lt_const hOmega).exists
  exact (hOrbit n).2.2 omega hn

#print axioms innerness_self_improvement

end D5.S3.Analytic.Toroidal.InnernessSelfImprovement
