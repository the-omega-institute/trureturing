/- GID: D5/S3/Analytic/Laplace/LongWindowBounds
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/LongWindowBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrarily late power windows and uniform numerical Landau comparisons. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Numerical bounds for long-window pole exclusion

The uniform exponential comparison in `landau_growth_contra` supplies the
numerical contradiction `landau_window_contra`. The window predicate records
only its width and pointwise bounds; exponent ranges are separate assumptions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Analytic.Laplace.LongWindowBounds

def LongWindowUpperBound (G : ℝ → ℝ) (theta delta C : ℝ) : Prop :=
  0 < delta ∧
    ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ 0 < Y ∧
      ∀ x ∈ Set.Icc Y (Y ^ (1 + delta)), G x ≤ C * x ^ theta

theorem landau_growth_contra {c d e C : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hde : d < e) :
    let η := Real.log (e / d) / 2
    let U₀ := 2 * |C| / (c * Real.log (e / d))
    0 < η ∧ 0 ≤ U₀ ∧ ∀ U ≥ U₀, ∀ k : ℕ, U ≤ k →
      C * Real.exp (η * U) / e ^ k < c / d ^ k := by
  have he : 0 < e := hd.trans hde
  have hL : 0 < Real.log (e / d) :=
    Real.log_pos ((one_lt_div hd).mpr hde)
  set ell := Real.log (e / d) with hell
  refine ⟨by positivity, by positivity, ?_⟩
  intro U hU k hk
  have hdk : 0 < d ^ k := pow_pos hd k
  have hek : 0 < e ^ k := pow_pos he k
  have hpow : e ^ k = d ^ k * Real.exp (k * ell) := by
    rw [Real.exp_nat_mul, hell, Real.exp_log (div_pos he hd), div_pow]
    exact (mul_div_cancel₀ _ hdk.ne').symm
  rw [div_lt_div_iff₀ hek hdk, hpow]
  set X := Real.exp (ell / 2 * U) with hXdef
  have hXpos : 0 < X := Real.exp_pos _
  have hcL : 0 < c * ell := mul_pos hc hL
  rw [ge_iff_le, div_le_iff₀ hcL] at hU
  have h1 : ell / 2 * U + 1 ≤ X := Real.add_one_le_exp _
  have hX : |C| < c * X := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hc.le]
  have hY : X * X ≤ Real.exp (k * ell) := by
    rw [hXdef, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hk hL.le]
  have hCX : C * X * d ^ k ≤ |C| * X * d ^ k := by
    have hCA := le_abs_self C
    have hXd : 0 < X * d ^ k := mul_pos hXpos hdk
    nlinarith
  have h2 : |C| * X < c * (X * X) := by nlinarith
  have h3 : c * (X * X) ≤ c * Real.exp (k * ell) :=
    mul_le_mul_of_nonneg_left hY hc.le
  calc
    C * X * d ^ k ≤ |C| * X * d ^ k := hCX
    _ < c * Real.exp (k * ell) * d ^ k :=
      mul_lt_mul_of_pos_right (h2.trans_le h3) hdk
    _ = c * (d ^ k * Real.exp (k * ell)) := by ring

theorem landau_window_contra {c d e E M C : ℝ} (hc : 0 < c)
    (hd : 0 < d) (hde : d < e) (hdE : d < E)
    (H : ∀ η : ℝ, 0 < η → ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧
      ∃ k : ℕ, U ≤ k ∧
        c / d ^ k ≤ M / e ^ k + C * Real.exp (η * U) / E ^ k) : False := by
  let m := min e E
  have hdm : d < m := lt_min hde hdE
  let η := Real.log (m / d) / 2
  let U₀ := 2 * (|M| + |C|) / (c * Real.log (m / d))
  obtain ⟨hη, _, hU₀⟩ := landau_growth_contra (C := |M| + |C|) hc hd hdm
  rw [abs_of_nonneg (add_nonneg (abs_nonneg M) (abs_nonneg C))] at hU₀
  obtain ⟨U, hU, k, hk, hle⟩ := H η hη (max U₀ 0)
  have h1 := hU₀ U ((le_max_left _ _).trans hU) k hk
  have hU0 : 0 ≤ U := (le_max_right _ _).trans hU
  have hm : 0 < m := hd.trans hdm
  have hek : 0 < m ^ k := pow_pos hm k
  have hexp : 1 ≤ Real.exp (η * U) := Real.one_le_exp (by positivity)
  have h2 : M / e ^ k ≤ |M| * Real.exp (η * U) / m ^ k := by
    apply div_le_div₀ (by positivity) _ hek
      (pow_le_pow_left₀ hm.le (min_le_left e E) k)
    exact (le_abs_self M).trans (le_mul_of_one_le_right (abs_nonneg M) hexp)
  have h3 : C * Real.exp (η * U) / E ^ k ≤
      |C| * Real.exp (η * U) / m ^ k := by
    apply div_le_div₀ (by positivity) _ hek
      (pow_le_pow_left₀ hm.le (min_le_right e E) k)
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
  have h4 : (|M| + |C|) * Real.exp (η * U) / m ^ k =
      |M| * Real.exp (η * U) / m ^ k +
        |C| * Real.exp (η * U) / m ^ k := by ring
  dsimp [η] at hle h2 h3 h4
  linarith

end D5.S3.Analytic.Laplace.LongWindowBounds
