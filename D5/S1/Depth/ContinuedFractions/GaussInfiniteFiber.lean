/- GID: D5/S1/Depth/ContinuedFractions/GaussInfiniteFiber
   generality: G
   mirror-B: D5/B/S1/Depth/ContinuedFractions/GaussInfiniteFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every interior value of the real Gauss map has infinitely many inverse branches. -/

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Set.Finite.Basic

/- Library-search audit trail (2026-08-17):
   * Repository searches for Gauss-map fibers, preimages, and inverse branches found no matching
     theorem; `GaussInverseStep.gauss_inverse_step_recovers_quotient` covers only quotient recovery.
   * Pinned Mathlib and two `smart_search.sh` queries found no full infinite-fiber theorem.
   * Loogle returned zero exact matches; LeanSearch `/api/search` returned HTTP 404.
   * Pinned Mathlib supplies `Int.fract_natCast_add` and
     `Set.infinite_range_of_injective`, which are applied directly below. -/

namespace D5.S1.Depth.ContinuedFractions.GaussInfiniteFiber

/-- For every `y` strictly between zero and one, the real Gauss map `x ↦ fract (1 / x)`
has infinitely many preimages in the open unit interval. -/
theorem gauss_map_interior_fiber_infinite (y : ℝ) (hy : y ∈ Set.Ioo 0 1) :
    {x : ℝ | x ∈ Set.Ioo 0 1 ∧ Int.fract (1 / x) = y}.Infinite := by
  let branch : ℕ → ℝ := fun n => ((n : ℝ) + 1 + y)⁻¹
  have hbranch (n : ℕ) :
      branch n ∈ {x : ℝ | x ∈ Set.Ioo 0 1 ∧ Int.fract (1 / x) = y} := by
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hden : (1 : ℝ) < (n : ℝ) + 1 + y := lt_add_of_le_of_pos hn hy.1
    constructor
    · exact ⟨inv_pos.mpr (zero_lt_one.trans hden), inv_lt_one_of_one_lt₀ hden⟩
    · change Int.fract (1 / (((n : ℝ) + 1 + y)⁻¹)) = y
      rw [show 1 / (((n : ℝ) + 1 + y)⁻¹) = (n : ℝ) + 1 + y by
        simp only [one_div, inv_inv]]
      rw [show (n : ℝ) + 1 + y = (((n + 1 : ℕ) : ℝ) + y) by norm_num]
      rw [Int.fract_natCast_add]
      exact Int.fract_eq_self.2 ⟨hy.1.le, hy.2⟩
  have hinjective : Function.Injective branch := by
    intro n m hnm
    change ((n : ℝ) + 1 + y)⁻¹ = ((m : ℝ) + 1 + y)⁻¹ at hnm
    have hden : (n : ℝ) + 1 + y = (m : ℝ) + 1 + y := inv_inj.mp hnm
    have hcast : (n : ℝ) = (m : ℝ) := by
      exact add_right_cancel (by simpa only [add_assoc] using hden)
    exact_mod_cast hcast
  apply (Set.infinite_range_of_injective hinjective).mono
  rintro x ⟨n, rfl⟩
  exact hbranch n

#print axioms gauss_map_interior_fiber_infinite

end D5.S1.Depth.ContinuedFractions.GaussInfiniteFiber
