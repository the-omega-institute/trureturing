/- GID: D5/S1/Digit/CompositeGasBeta
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact radical formula for the positive real digit-gas characteristic root. -/

import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S1.Digit

/-- The positive real root of the digit-gas characteristic equation. -/
noncomputable def e6Beta (c : ℕ) : ℝ :=
  (1 + Real.sqrt (1 + 4 * c)) / 2

theorem e6_beta_pos (c : ℕ) : 0 < e6Beta c := by
  rw [e6Beta]
  positivity

theorem e6_beta_ge_one (c : ℕ) : 1 ≤ e6Beta c := by
  rw [e6Beta]
  have hsqrt_sq : Real.sqrt (1 + 4 * (c : ℝ)) ^ 2 = 1 + 4 * c :=
    Real.sq_sqrt (by positivity)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + 4 * (c : ℝ)) :=
    Real.sqrt_nonneg _
  have hc : 0 ≤ (c : ℝ) := Nat.cast_nonneg c
  nlinarith

theorem e6_beta_sq (c : ℕ) : e6Beta c ^ 2 = e6Beta c + c := by
  rw [e6Beta]
  have hsqrt_sq : Real.sqrt (1 + 4 * (c : ℝ)) ^ 2 = 1 + 4 * c :=
    Real.sq_sqrt (by positivity)
  nlinarith

theorem e6_beta_unique (c : ℕ) {x : ℝ} (hx : 0 < x)
    (hsq : x ^ 2 = x + c) : x = e6Beta c := by
  have hbeta_sq := e6_beta_sq c
  have hbeta_ge_one := e6_beta_ge_one c
  have hfactor : (x - e6Beta c) * (x + e6Beta c - 1) = 0 := by
    nlinarith
  have hsecond : 0 < x + e6Beta c - 1 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hroot | hsecond_zero
  · exact sub_eq_zero.mp hroot
  · exact (hsecond.ne' hsecond_zero).elim

@[simp] theorem e6_beta_zero : e6Beta 0 = 1 := by
  simp [e6Beta]

theorem e6_beta_one : e6Beta 1 = Real.goldenRatio := by
  norm_num [e6Beta, Real.goldenRatio]

@[simp] theorem e6_beta_two : e6Beta 2 = 2 := by
  rw [e6Beta]
  have hsqrt_sq :
      Real.sqrt (1 + 4 * ((2 : ℕ) : ℝ)) ^ 2 =
        1 + 4 * ((2 : ℕ) : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg :
      0 ≤ Real.sqrt (1 + 4 * ((2 : ℕ) : ℝ)) := Real.sqrt_nonneg _
  have hrad : 1 + 4 * ((2 : ℕ) : ℝ) = 9 := by norm_num
  rw [hrad] at hsqrt_sq hsqrt_nonneg ⊢
  nlinarith

end D5.S1.Digit
