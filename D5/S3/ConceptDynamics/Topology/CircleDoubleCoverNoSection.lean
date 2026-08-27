/- GID: D5/S3/ConceptDynamics/Topology/CircleDoubleCoverNoSection
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Topology/CircleDoubleCoverNoSection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The circle squaring double cover has no continuous global section. -/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/- Library-search audit trail (2026-08-27):
   * No exact no-section theorem was found in D5 or Mathlib.
   * The exact Mathlib primitives used below are `Circle.exp`, `Circle.exp_eq_exp`,
     `Circle.exp_two_pi`, `Circle.exp_pi_ne_one`, `IsPreconnected.constant_of_mapsTo`,
     `Set.Finite.isDiscrete`, and `Circle.neg_ne_self`.
   * The proof keeps the source carrier `Circle` and the source map `z ↦ z ^ 2`
     explicit. It composes a putative section with `Circle.exp`, divides by the
     half-angle exponential, and uses connectedness of `ℝ` to force the resulting
     finite-valued sign to be constant.
   * A body-shape search for section and circle primitives found no existing D5
     construction to import; no new `def` or `abbrev` is introduced here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Topology.CircleDoubleCoverNoSection

/-- The squaring map on the unit circle has no continuous global section. -/
theorem no_continuous_global_section :
    ¬ ∃ s : Circle → Circle, Continuous s ∧ ∀ z : Circle, s z ^ 2 = z := by
  rintro ⟨s, hs, hsec⟩
  let q : ℝ → Circle := fun t => s (Circle.exp t)
  let r : ℝ → Circle := fun t => q t / Circle.exp (t / 2)
  have hr : Continuous r := by
    dsimp [r, q]
    fun_prop
  have hr_sq : ∀ t : ℝ, r t ^ 2 = 1 := by
    intro t
    dsimp [r, q]
    rw [div_pow, hsec, ← Circle.exp_natCast_mul]
    have hhalf : (↑(2 : ℕ) : ℝ) * (t / 2) = t := by norm_num; ring
    rw [hhalf]
    simp
  have hr_sign : ∀ t : ℝ, r t = 1 ∨ r t = -1 := by
    intro t
    have hcoerce : ((r t : Circle) : ℂ) ^ 2 = 1 := by
      exact congrArg (fun z : Circle => (z : ℂ)) (hr_sq t)
    rcases (sq_eq_one_iff.mp hcoerce) with h | h
    · exact Or.inl (Circle.ext h)
    · exact Or.inr (Circle.ext h)
  have hdisc : IsDiscrete ({(1 : Circle), -1} : Set Circle) := by
    exact (Set.finite_singleton (-1 : Circle)).insert 1 |>.isDiscrete
  have hr_const : ∀ t : ℝ, r t = r 0 := by
    intro t
    apply isPreconnected_univ.constant_of_mapsTo hdisc hr.continuousOn
    · intro x _
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hr_sign x
    · trivial
    · trivial
  have hexp_pi : Circle.exp Real.pi = -1 := by
    have hsquare : Circle.exp Real.pi ^ 2 = 1 := by
      rw [← Circle.exp_natCast_mul]
      convert Circle.exp_two_pi using 1
      norm_num
    have hcoerce : ((Circle.exp Real.pi : Circle) : ℂ) ^ 2 = 1 := by
      exact congrArg (fun z : Circle => (z : ℂ)) hsquare
    rcases (sq_eq_one_iff.mp hcoerce) with h | h
    · exact (Circle.exp_pi_ne_one (Circle.ext h)).elim
    · exact Circle.ext h
  have hsign_endpoint : r (2 * Real.pi) = -r 0 := by
    dsimp [r, q]
    rw [Circle.exp_two_pi]
    have hhalf : (2 * Real.pi) / 2 = Real.pi := by ring
    rw [hhalf, hexp_pi]
    simp [Circle.exp_zero, div_neg]
  have hcontra : r (2 * Real.pi) = r 0 := hr_const (2 * Real.pi)
  exact Circle.neg_ne_self (r 0) (hcontra.symm.trans hsign_endpoint).symm

#print axioms no_continuous_global_section

end D5.S3.ConceptDynamics.Topology.CircleDoubleCoverNoSection
