/- GID: D5/S3/Midline/CayleyCriticalLine
   generality: G
   mirror-B: D5/B/S3/Midline/CayleyCriticalLine
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Cayley ratio has unit norm exactly on the critical line. -/

import Mathlib.Analysis.Complex.Basic

/- Library-search and duplication audit (2026-09-04):
   * Repository searches covered Cayley ratios, unit modulus, critical-line
     criteria, and the more general zero-space unitarity packages. The closest
     result is a private zero-coordinate lemma in `CayleyUnitarityDefect`; no
     public theorem states the equivalence for an arbitrary complex point.
   * The digestion receipt index has no receipt for the source atom, and the
     in-flight branch scan found no competing generic Cayley-line deposit.
   * Pinned Mathlib supplies `Complex.normSq_div`, `Complex.normSq_sub`, and
     `Complex.sq_norm`; they are used directly below.
   * Division is total in Lean. The proof therefore handles `s = 0` separately
     before using the nonzero-denominator norm-square formula. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Midline.CayleyCriticalLine

open scoped ComplexConjugate

/-- The scalar Cayley ratio attached to a complex spectral parameter. -/
noncomputable def cayleyRatio (s : ℂ) : ℂ :=
  (s - 1) / s

private theorem cayley_ratio_norm_sq_sub_one {s : ℂ} (hs : s ≠ 0) :
    ‖cayleyRatio s‖ ^ 2 - 1 =
      (1 - 2 * s.re) / Complex.normSq s := by
  have hnormSq : Complex.normSq s ≠ 0 :=
    mt Complex.normSq_eq_zero.mp hs
  rw [cayleyRatio, Complex.sq_norm, Complex.normSq_div,
    Complex.normSq_sub]
  simp only [map_one, mul_one]
  field_simp [hnormSq]
  ring

/-- The Cayley ratio `(s - 1) / s` lies on the unit circle exactly when `s`
lies on the critical line. The totalized division case `s = 0` is included. -/
theorem cayley_ratio_norm_one_iff_critical_line (s : ℂ) :
    ‖cayleyRatio s‖ = 1 ↔ s.re = (1 : ℝ) / 2 := by
  by_cases hs : s = 0
  · subst s
    norm_num [cayleyRatio]
  · have hnormSq : Complex.normSq s ≠ 0 :=
      mt Complex.normSq_eq_zero.mp hs
    constructor
    · intro hnorm
      have hdefect : ‖cayleyRatio s‖ ^ 2 - 1 = 0 := by
        rw [hnorm]
        norm_num
      rw [cayley_ratio_norm_sq_sub_one hs] at hdefect
      have hnumerator : 1 - 2 * s.re = 0 :=
        (div_eq_zero_iff.mp hdefect).resolve_right hnormSq
      linarith
    · intro hline
      have hdefect := cayley_ratio_norm_sq_sub_one hs
      rw [hline] at hdefect
      norm_num at hdefect
      nlinarith [norm_nonneg (cayleyRatio s)]

#print axioms cayley_ratio_norm_one_iff_critical_line

end D5.S3.Midline.CayleyCriticalLine
