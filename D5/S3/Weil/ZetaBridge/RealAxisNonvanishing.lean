/- GID: D5/S3/Weil/ZetaBridge/RealAxisNonvanishing
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaBridge/RealAxisNonvanishing
   mirror-E: none(waiver:pure-mathlib-zero-classification)
   anchors: []
   digest: Real zeta zeros outside the open unit interval are negative even integers. -/

/- Library-search audit trail (2026-09-03):
   * Neither pinned Mathlib nor D5 contains the target theorem or its
     existential real-zero classification.
   * Mathlib supplies zeta nonvanishing for real part at least one, its
     completed-zeta quotient formula, and the zero set of `Gammaℝ`.
   * The frozen `completedRiemannZeta_ne_zero_of_re_nonpos` theorem supplies
     the only D5 dependency used below. -/

import D5.S3.Weil.ZetaRvm.CountByIntegral

open Complex

namespace D5.S3.Weil.ZetaBridge.RealAxisNonvanishing

noncomputable section

/-- Every real Riemann-zeta zero outside `(0, 1)` is a negative even integer. -/
theorem riemannZeta_real_zero_outside_Ioo
    (x : ℝ) (hout : ¬ (0 < x ∧ x < 1)) (hz : riemannZeta (x : ℂ) = 0) :
    ∃ n : ℕ, x = -2 * (n + 1) := by
  by_cases hxpos : 0 < x
  · have hxone : 1 ≤ x := by
      by_contra h
      exact hout ⟨hxpos, lt_of_not_ge h⟩
    exact absurd hz (riemannZeta_ne_zero_of_one_le_re (by simpa using hxone))
  · have hxnonpos : x ≤ 0 := le_of_not_gt hxpos
    have hx0 : x ≠ 0 := by
      intro hx
      subst x
      norm_num [riemannZeta_zero] at hz
    have hxc0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0
    rw [riemannZeta_def_of_ne_zero hxc0] at hz
    have hGamma : Complex.Gammaℝ (x : ℂ) = 0 := by
      by_contra hGamma
      have hcompleted : completedRiemannZeta (x : ℂ) = 0 :=
        (div_eq_zero_iff.mp hz).resolve_right hGamma
      exact Zeta23.RvM.completedRiemannZeta_ne_zero_of_re_nonpos
        (by simpa using hxnonpos) hcompleted
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hGamma
    have hn0 : n ≠ 0 := by
      intro hnzero
      subst n
      apply hxc0
      simpa using hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    refine ⟨m, ?_⟩
    exact_mod_cast hn

example :
    ¬ (0 < (-2 : ℝ) ∧ (-2 : ℝ) < 1) ∧
      riemannZeta ((-2 : ℝ) : ℂ) = 0 := by
  constructor
  · norm_num
  · simpa using riemannZeta_neg_two_mul_nat_add_one 0

example : Nonempty ℝ := ⟨0⟩

#print axioms riemannZeta_real_zero_outside_Ioo

end

end D5.S3.Weil.ZetaBridge.RealAxisNonvanishing
