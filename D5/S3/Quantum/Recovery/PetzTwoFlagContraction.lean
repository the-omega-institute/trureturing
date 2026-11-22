/- GID: D5/S3/Quantum/Recovery/PetzTwoFlagContraction
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzTwoFlagContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact complex two-flag contraction bound with radial and phase deficiency. -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Quantum.Recovery.PetzTwoFlagContraction

/-- The radial and phase terms give the full deficiency from the two real corners.
The strict radial margins include the contribution of the coherence term. -/
theorem twoFlag_maximum (m C f g w v : ℝ) (y z : ℂ)
    (hm : 0 ≤ m) (hC : 0 < C) (hf : 0 < f) (hg : 0 < g)
    (hw : 0 < 8 * m + f * (f + g) / C - w)
    (hv : 0 < 8 * m + g * (f + g) / C - v)
    (hy : Complex.normSq y ≤ 1) (hz : Complex.normSq z ≤ 1) :
    let objective := w * (1 - Complex.normSq y) + v * (1 - Complex.normSq z) +
      4 * m * Complex.normSq (y - z) + (f * y.re - g * z.re) ^ 2 / C
    let optimum := 16 * m + (f + g) ^ 2 / C
    objective ≤ optimum ∧
      optimum - objective =
        (8 * m + f * (f + g) / C - w) * (1 - Complex.normSq y) +
        (8 * m + g * (f + g) / C - v) * (1 - Complex.normSq z) +
        4 * m * Complex.normSq (y + z) +
        f * (f + g) / C * y.im ^ 2 + g * (f + g) / C * z.im ^ 2 +
        f * g / C * (y.re + z.re) ^ 2 ∧
      (objective = optimum ↔ (y = 1 ∧ z = -1) ∨ (y = -1 ∧ z = 1)) := by
  dsimp only
  have hgap :
      16 * m + (f + g) ^ 2 / C -
        (w * (1 - Complex.normSq y) + v * (1 - Complex.normSq z) +
          4 * m * Complex.normSq (y - z) + (f * y.re - g * z.re) ^ 2 / C) =
        (8 * m + f * (f + g) / C - w) * (1 - Complex.normSq y) +
        (8 * m + g * (f + g) / C - v) * (1 - Complex.normSq z) +
        4 * m * Complex.normSq (y + z) +
        f * (f + g) / C * y.im ^ 2 + g * (f + g) / C * z.im ^ 2 +
        f * g / C * (y.re + z.re) ^ 2 := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]
    ring
  have hySlack := sub_nonneg.mpr hy
  have hzSlack := sub_nonneg.mpr hz
  have hcoherence := mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (4 : ℝ)) hm)
    (Complex.normSq_nonneg (y + z))
  have hyCoeff := div_pos (mul_pos hf (add_pos hf hg)) hC
  have hzCoeff := div_pos (mul_pos hg (add_pos hf hg)) hC
  have hphaseCoeff := div_pos (mul_pos hf hg) hC
  have hyPhase := mul_nonneg hyCoeff.le (sq_nonneg y.im)
  have hzPhase := mul_nonneg hzCoeff.le (sq_nonneg z.im)
  have hphase := mul_nonneg hphaseCoeff.le (sq_nonneg (y.re + z.re))
  have hyTerm := mul_nonneg hw.le hySlack
  have hzTerm := mul_nonneg hv.le hzSlack
  refine ⟨by linarith, hgap, ?_⟩
  constructor
  · intro h
    have hyr : 1 - Complex.normSq y = 0 :=
      (mul_eq_zero.mp (show (8 * m + f * (f + g) / C - w) *
        (1 - Complex.normSq y) = 0 by linarith)).resolve_left hw.ne'
    have hyi : y.im = 0 := by
      have hs : y.im ^ 2 = 0 := (mul_eq_zero.mp (show f * (f + g) / C *
        y.im ^ 2 = 0 by linarith)).resolve_left hyCoeff.ne'
      exact pow_eq_zero hs
    have hzi : z.im = 0 := by
      have hs : z.im ^ 2 = 0 := (mul_eq_zero.mp (show g * (f + g) / C *
        z.im ^ 2 = 0 by linarith)).resolve_left hzCoeff.ne'
      exact pow_eq_zero hs
    have hreal : y.re + z.re = 0 := by
      have hs : (y.re + z.re) ^ 2 = 0 := (mul_eq_zero.mp (show f * g / C *
        (y.re + z.re) ^ 2 = 0 by linarith)).resolve_left hphaseCoeff.ne'
      exact pow_eq_zero hs
    have hySign : y.re = 1 ∨ y.re = -1 := by
      rw [Complex.normSq_apply, hyi] at hyr
      exact (mul_eq_zero.mp (show (y.re - 1) * (y.re + 1) = 0 by nlinarith)).imp
        (fun h₁ => by linarith) (fun h₂ => by linarith)
    rcases hySign with h₁ | h₂
    · exact Or.inl ⟨Complex.ext (by simpa using h₁) (by simpa using hyi),
        Complex.ext (by simp; linarith) (by simpa using hzi)⟩
    · exact Or.inr ⟨Complex.ext (by simpa using h₂) (by simpa using hyi),
        Complex.ext (by simp; linarith) (by simpa using hzi)⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      norm_num [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] <;> ring

end D5.S3.Quantum.Recovery.PetzTwoFlagContraction
