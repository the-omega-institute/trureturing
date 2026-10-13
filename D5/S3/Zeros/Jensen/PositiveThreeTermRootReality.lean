/- GID: D5/S3/Zeros/Jensen/PositiveThreeTermRootReality
   generality: G
   mirror-B: D5/B/S3/Zeros/Jensen/PositiveThreeTermRootReality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A zero of a finite positive three-term recurrence has a real spectral parameter. -/

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Zeros.Jensen.PositiveThreeTermRootReality

private theorem finite_positive_three_term_nonreal_nonvanishing
    (q : ℕ) (z : ℂ) (c : ℕ → ℝ) (v : ℕ → ℂ)
    (hc : ∀ k, k + 2 ≤ q → 0 < c k) (hz : z.im ≠ 0)
    (hv0 : v 0 ≠ 0) (hv1 : v 1 = z * v 0)
    (hrec : ∀ k, k + 2 ≤ q →
      v (k + 2) = z * v (k + 1) - (c k : ℂ) * v k) :
    ∀ k, k ≤ q → v k ≠ 0 := by
  have hratio : ∀ k, k < q →
      v k ≠ 0 ∧ 0 < z.im * (v (k + 1) / v k).im := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨hv0, ?_⟩
        rw [hv1, mul_div_cancel_right₀ _ hv0]
        nlinarith [sq_pos_of_ne_zero hz]
    | succ k ih =>
        intro hk
        obtain ⟨hvk, him⟩ := ih (by omega)
        have hvnext : v (k + 1) ≠ 0 := by
          intro heq
          simp only [heq, zero_div, Complex.zero_im, mul_zero] at him
          exact (lt_irrefl 0) him
        have hr : v (k + 1) / v k ≠ 0 := div_ne_zero hvnext hvk
        have hnorm : 0 < Complex.normSq (v (k + 1) / v k) :=
          Complex.normSq_pos.mpr hr
        have hstep : k + 2 ≤ q := by omega
        have hid : v (k + 2) / v (k + 1) =
            z - (c k : ℂ) / (v (k + 1) / v k) := by
          rw [hrec k hstep]
          field_simp [hvk, hvnext]
        refine ⟨hvnext, ?_⟩
        change 0 < z.im * (v (k + 2) / v (k + 1)).im
        rw [hid]
        rw [Complex.sub_im, Complex.div_im]
        simp only [Complex.ofReal_im, Complex.ofReal_re,
          zero_mul, zero_div, zero_sub]
        have hp : 0 < c k * (z.im * (v (k + 1) / v k).im) /
            Complex.normSq (v (k + 1) / v k) :=
          div_pos (mul_pos (hc k hstep) him) hnorm
        have heq : z.im * (z.im - -(c k * (v (k + 1) / v k).im /
              Complex.normSq (v (k + 1) / v k))) =
            z.im ^ 2 + c k * (z.im * (v (k + 1) / v k).im) /
              Complex.normSq (v (k + 1) / v k) := by ring
        rw [heq]
        positivity
  intro k hk
  cases k with
  | zero => exact hv0
  | succ k =>
      obtain ⟨_, him⟩ := hratio k (by omega)
      intro heq
      simp only [heq, zero_div, Complex.zero_im, mul_zero] at him
      exact (lt_irrefl 0) him

/-- Positive recurrence coefficients exclude a nonreal spectral parameter
at a zero of the finite sequence. Only recurrence equations and coefficient
positivity through the selected endpoint are required; the tails of `c`
and `v` are unrestricted. -/
theorem finite_positive_three_term_zero_has_real_parameter
    (q : ℕ) (z : ℂ) (c : ℕ → ℝ) (v : ℕ → ℂ)
    (hc : ∀ k, k + 2 ≤ q → 0 < c k)
    (hv0 : v 0 ≠ 0) (hv1 : v 1 = z * v 0)
    (hrec : ∀ k, k + 2 ≤ q →
      v (k + 2) = z * v (k + 1) - (c k : ℂ) * v k)
    (hq : v q = 0) : z.im = 0 := by
  by_contra hz
  exact finite_positive_three_term_nonreal_nonvanishing
    q z c v hc hz hv0 hv1 hrec q le_rfl hq

#print axioms finite_positive_three_term_zero_has_real_parameter

end D5.S3.Zeros.Jensen.PositiveThreeTermRootReality
