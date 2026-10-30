/- GID: D5/S3/Analytic/EllipticTailExponent/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/EllipticTailExponent/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.TangentCone.Real, mathlib/module/Mathlib.Topology.Order.IsLUB]
   utility: none
   digest: The elliptic remainder exponent has supremum two for every finite truncation. -/

import D5.S3.Analytic.EllipticTailExponent.Tail
import D5.S3.Analytic.EllipticTailExponent.Bounds
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.Order.IsLUB

noncomputable section
open Finset Set Filter
open scoped BigOperators Topology
open D5.S3.Analytic.EllipticTailExponent.Defs
open D5.S3.Analytic.EllipticTailExponent.Tail
open D5.S3.Analytic.EllipticTailExponent.Bounds

namespace D5.S3.Analytic.EllipticTailExponent.Result

private lemma t_eq_sq_mul_b {k : ℕ} (hk : 1 ≤ k) (a : ℝ) : t k a = a ^ 2 * b k a := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have he := d_product (k - 1) a
  have hcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
    rw [Nat.cast_sub hk, Nat.cast_one]; ring
  have hnat : k - 1 + 1 = k := by omega
  rw [hnat, hcast] at he
  unfold t b
  apply (mul_left_cancel₀ hk0)
  calc
    _ = a * ((k : ℝ) * d k a) / (k + 1) := by ring
    _ = _ := by rw [he]; field_simp

private def R (n : ℕ) (a : ℝ) : ℝ :=
  Real.sin (Real.pi * a) / (Real.pi * (1 - a)) - S n a

private lemma R_eq (n : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 2) :
    R n a = a ^ 2 * U n a := by
  rw [R, tail_eq_tsum n ha ha1, U, ← tsum_mul_left]
  congr 1
  ext k
  exact t_eq_sq_mul_b (by omega) a

private lemma differentiable_S (n : ℕ) : Differentiable ℝ (S n) := by
  unfold S g6
  fun_prop

private lemma hasDerivAt_R (n : ℕ) {a : ℝ} (ha : a ≠ 1) :
    HasDerivAt (R n)
      ((Real.sin (Real.pi * a) + Real.pi * (1 - a) * Real.cos (Real.pi * a)) /
        (Real.pi * (1 - a) ^ 2) - deriv (S n) a) a := by
  have hs := (Real.hasDerivAt_sin (Real.pi * a)).comp a ((hasDerivAt_id a).const_mul Real.pi)
  have hd := ((hasDerivAt_const a (1 : ℝ)).sub (hasDerivAt_id a)).const_mul Real.pi
  have h0 : Real.pi * (1 - a) ≠ 0 := mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr ha.symm)
  convert (hs.div hd h0).sub (differentiable_S n a).hasDerivAt using 1
  · rfl
  · dsimp
    field_simp
    ring

private lemma deriv_R_eq (n : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 2) :
    deriv (R n) a = 2 * a * U n a + a ^ 2 * deriv (U n) a := by
  have hleft := (hasDerivAt_R n (by linarith : a ≠ 1)).hasDerivWithinAt
    (s := Ioc 0 (1 / 2))
  have hright : HasDerivAt (fun x : ℝ => x ^ 2 * U n x)
      (2 * a * U n a + a ^ 2 * deriv (U n) a) a := by
    convert ((hasDerivAt_id a).pow 2).mul
      (hasDerivAt_U n ha (by linarith)).differentiableAt.hasDerivAt using 1
    · rfl
    · simp only [Pi.pow_apply, id_eq]
      ring
  have he := (uniqueDiffOn_Ioc (0 : ℝ) (1 / 2) a ⟨ha, ha1⟩).eq_deriv
    (Ioc 0 (1 / 2)) hleft
    (hright.hasDerivWithinAt.congr_of_mem
      (fun x hx => R_eq n hx.1 hx.2) ⟨ha, ha1⟩)
  rw [← (hasDerivAt_R n (by linarith : a ≠ 1)).deriv] at he
  exact he

/-- The denominator in the parameter exponent is strictly positive. -/
theorem denominator_pos (n : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 2) :
    0 < Real.sin (Real.pi * a) - Real.pi * (1 - a) * S n a := by
  have hr : 0 < R n a := by
    rw [R_eq n ha ha1]
    exact mul_pos (sq_pos_of_pos ha) (U_pos n ha.le (by linarith))
  have hm0 : 0 < 1 - a := by linarith
  have h0 : Real.pi * (1 - a) ≠ 0 := mul_ne_zero Real.pi_ne_zero hm0.ne'
  have he : Real.sin (Real.pi * a) - Real.pi * (1 - a) * S n a =
      Real.pi * (1 - a) * R n a := by
    unfold R
    field_simp [hm0.ne']
  rw [he]
  exact mul_pos (mul_pos Real.pi_pos (by linarith)) hr

/-- The exponent is two plus the logarithmic derivative of the normalized tail. -/
theorem lambda10_eq (n : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 2) :
    lambda10 n a = 2 + a * deriv (U n) a / U n a := by
  have hu := U_pos n ha.le (by linarith : a ≤ 3 / 4)
  have hden := denominator_pos n ha ha1
  have h0 : 1 - a ≠ 0 := by linarith
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have ha0 : a ≠ 0 := ha.ne'
  have hr : R n a ≠ 0 := by
    rw [R_eq n ha ha1]
    positivity
  have he : lambda10 n a = a * deriv (R n) a / R n a := by
    rw [(hasDerivAt_R n (by linarith : a ≠ 1)).deriv]
    unfold lambda10 R
    field_simp
  rw [he, deriv_R_eq n ha ha1, R_eq n ha ha1]
  field_simp

/-- Every parameter value is strictly below two. -/
theorem lambda10_lt_two (n : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 2) :
    lambda10 n a < 2 := by
  rw [lambda10_eq n ha ha1]
  have hn := deriv_U_neg n ha (by linarith : a < 3 / 4)
  have hu := U_pos n ha.le (by linarith : a ≤ 3 / 4)
  have := div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ha hn) hu
  linarith

/-- The exponent tends to two as the parameter decreases to zero. -/
theorem tendsto_lambda10 (n : ℕ) : Tendsto (lambda10 n) (𝓝[>] 0) (𝓝 2) := by
  let C : ℝ := 4 * ∑' k : ℕ,
    1 / (((k + n + 1 : ℕ) : ℝ) * (((k + n + 1 : ℕ) : ℝ) + 1))
  have hnum : Tendsto (fun a : ℝ => a * deriv (U n) a) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun a : ℝ => a * C)
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 3 / 4)] with a ha
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos ha.1]
      exact mul_le_mul_of_nonneg_left (norm_deriv_U_le n ha.1 ha.2) ha.1.le
    · simpa using ((tendsto_id.mono_left nhdsWithin_le_nhds).mul_const C :
        Tendsto (fun a : ℝ => a * C) (𝓝[>] 0) (𝓝 ((0 : ℝ) * C)))
  have hU : Tendsto (U n) (𝓝[>] 0) (𝓝 (1 / ((n : ℝ) + 1))) := by
    rw [← U_zero n]
    have hc := (continuousOn_U n 0 ⟨le_rfl, by norm_num⟩).tendsto
    rw [nhdsWithin_Icc_eq_nhdsGE (by norm_num : (0 : ℝ) < 3 / 4)] at hc
    exact hc.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have he : (fun a : ℝ => 2 + a * deriv (U n) a / U n a) =ᶠ[𝓝[>] 0] lambda10 n := by
    filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with a ha
    exact (lambda10_eq n ha.1 ha.2).symm
  have ht : Tendsto (fun a : ℝ => 2 + a * deriv (U n) a / U n a)
      (𝓝[>] 0) (𝓝 2) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).add (hnum.div hU (by positivity))
  exact ht.congr' he

/-- The supremum of the parameter exponent is two for every truncation. -/
theorem result : claim := by
  intro n
  apply isLUB_of_mem_closure
  · rintro y ⟨a, ha, rfl⟩
    exact (lambda10_lt_two n ha.1 ha.2).le
  · apply mem_closure_of_tendsto (tendsto_lambda10 n)
    filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with a ha
    exact ⟨a, ha, rfl⟩

end D5.S3.Analytic.EllipticTailExponent.Result
