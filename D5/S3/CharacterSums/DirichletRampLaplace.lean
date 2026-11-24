/- GID: D5/S3/CharacterSums/DirichletRampLaplace
   generality: I
   mirror-B: D5/B/S3/CharacterSums/DirichletRampLaplace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact log-coordinate Laplace transforms of the character-weighted Mangoldt ramp. -/

import D5.S3.CharacterSums.DirichletRampEndpoint

/-! # Laplace transforms for character-weighted Mangoldt ramps -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology LSeries.notation ArithmeticFunction
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.CharacterSums.DirichletRampEndpoint

namespace D5.S3.CharacterSums.DirichletRampLaplace

private theorem characterRamp_eq_range {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) :
    characterRamp χ x =
      ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (mangoldtRamp n x : ℂ) * χ (n : ZMod N) := by
  unfold characterRamp
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Ioc.mp hn).2)
  · intro n hn hnot
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos fun hp =>
      hnot (Finset.mem_Ioc.mpr ⟨hp, Nat.le_of_lt_succ (Finset.mem_range.mp hn)⟩)
    subst n
    simp [mangoldtRamp]

private theorem weighted_ramps_hasSum {N : ℕ} (χ : DirichletCharacter ℂ N) (t y : ℝ) :
    HasSum (fun n : ℕ => Complex.exp (-transformLine t * y) *
      (mangoldtRamp n (Real.exp y) : ℂ) * χ (n : ZMod N))
      (Complex.exp (-transformLine t * y) * characterRamp χ (Real.exp y)) := by
  rw [characterRamp_eq_range, Finset.mul_sum]
  simp_rw [← mul_assoc]
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  have hn' : ⌊Real.exp y⌋₊ + 1 ≤ n := by
    simpa only [Finset.mem_range, not_lt] using hn
  have hy : Real.exp y < (n : ℝ) :=
    (Nat.lt_succ_floor _).trans_le (by exact_mod_cast hn')
  simp [ramp_zero_of_lt (Real.exp_nonneg y) hy]

private theorem characterRamp_line_integrable {N : ℕ} (χ : DirichletCharacter ℂ N) (t : ℝ) :
    IntegrableOn (fun y : ℝ => Complex.exp (-transformLine t * y) *
      characterRamp χ (Real.exp y)) (Ioi 0) := by
  let f : ℕ → ℝ → ℂ := fun n y => Complex.exp (-transformLine t * y) *
    (mangoldtRamp n (Real.exp y) : ℂ) * χ (n : ZMod N)
  have hf (n : ℕ) : Continuous (f n) := by
    dsimp only [f]
    exact (show Continuous (fun y : ℝ => Complex.exp (-transformLine t * y)) by fun_prop).mul
      (Complex.continuous_ofReal.comp ((mangoldtRamp_continuous n).comp Real.continuous_exp)) |>.mul
        continuous_const
  have hm : Measurable (fun y : ℝ =>
      Complex.exp (-transformLine t * y) * characterRamp χ (Real.exp y)) := by
    apply measurable_of_tendsto_metrizable (f := fun k y => ∑ n ∈ Finset.range k, f n y)
    · intro k
      exact (continuous_finsetSum _ fun n _ => hf n).measurable
    · rw [tendsto_pi_nhds]
      intro y
      exact (weighted_ramps_hasSum χ t y).tendsto_sum_nat
  refine Integrable.mono (mangoldtPart_line_integrable t) hm.aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  simp only [norm_mul, Complex.norm_real]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [characterRamp_eq_range,
    mangoldtPart_eq_range (Real.exp_nonneg y) (Nat.lt_succ_floor (Real.exp y)),
    Real.norm_of_nonneg (Finset.sum_nonneg fun n _ => mangoldtRamp_nonneg n _)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mangoldtRamp_nonneg n _)]
  exact mul_le_of_le_one_right (mangoldtRamp_nonneg n _) (χ.norm_le_one _)

/-- The complete character-weighted ramp has the twisted Mangoldt transform on Re(s) = 2. -/
theorem characterRamp_line_laplace {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) :
    (∫ y : ℝ in Ioi 0, Complex.exp (-transformLine t * y) * characterRamp χ (Real.exp y)) =
      (-deriv χ.LFunction (transformLine t) / χ.LFunction (transformLine t)) /
        (transformLine t * (transformLine t - 1)) := by
  let s : ℂ := transformLine t
  have hs : 1 < s.re := by simp [s]
  let f : ℕ → ℝ → ℂ := fun n y => Complex.exp (-s * y) *
    (mangoldtRamp n (Real.exp y) : ℂ) * χ (n : ZMod N)
  have hi (n : ℕ) : Integrable (f n) (volume.restrict (Ioi 0)) :=
    (mangoldtRamp_laplace_integrable (n := n) hs).mul_const _
  have hnorm : Summable (fun n => ∫ y : ℝ in Ioi 0, ‖f n y‖) := by
    refine (mangoldtRamp_norm_integrals_summable t).of_nonneg_of_le
      (fun n => integral_nonneg fun y => norm_nonneg _) fun n => ?_
    change (∫ y : ℝ in Ioi 0, ‖f n y‖) ≤
      ∫ y : ℝ in Ioi 0, ‖Complex.exp (-s * y) * (mangoldtRamp n (Real.exp y) : ℂ)‖
    simp only [f, norm_mul]
    rw [integral_mul_const]
    exact mul_le_of_le_one_right (integral_nonneg fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (χ.norm_le_one _)
  have hsum := hasSum_integral_of_summable_integral_norm hi hnorm
  have hL := (χ.LSeriesSummable_twist_vonMangoldt hs).hasSum.div_const (s * (s - 1))
  change HasSum _ (LSeries (↗χ * ↗Λ) s / (s * (s - 1))) at hL
  rw [show LSeries (↗χ * ↗Λ) s = -deriv χ.LFunction s / χ.LFunction s by
    rw [χ.LSeries_twist_vonMangoldt_eq hs, χ.LFunction_eq_LSeries hs,
      χ.deriv_LFunction_eq_deriv_LSeries hs]] at hL
  have hterm (n : ℕ) : (∫ y : ℝ in Ioi 0, f n y) =
      LSeries.term (↗χ * ↗Λ) s n / (s * (s - 1)) := by
    dsimp only [f]
    rw [integral_mul_const, mangoldtRamp_laplace hs]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp only [LSeries.term_of_ne_zero hn, Pi.mul_apply]
      ring
  have hL' : HasSum (fun n : ℕ => ∫ y : ℝ in Ioi 0, f n y)
      ((-deriv χ.LFunction s / χ.LFunction s) / (s * (s - 1))) := by
    simpa only [hterm] using hL
  calc
    _ = ∫ y : ℝ in Ioi 0, ∑' n : ℕ, f n y :=
      setIntegral_congr_fun measurableSet_Ioi fun y _ => (weighted_ramps_hasSum χ t y).tsum_eq.symm
    _ = _ := hsum.unique hL'

/-- The nonprincipal correction in `gChi` contributes its endpoint logarithmic derivative. -/
theorem gChi_line_laplace {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (t : ℝ) :
    (∫ y : ℝ in Ioi 0, Complex.exp (-transformLine t * y) * gChi χ (Real.exp y)) =
      (-deriv χ.LFunction (transformLine t) / χ.LFunction (transformLine t)) /
        (transformLine t * (transformLine t - 1)) +
      (deriv χ.LFunction 1 / χ.LFunction 1) / (transformLine t - 1) := by
  let s : ℂ := transformLine t
  let c : ℂ := deriv χ.LFunction 1 / χ.LFunction 1
  have hneg : (1 - s).re < 0 := by simp [s]
  have hsplit (y : ℝ) : Complex.exp (-s * y) * gChi χ (Real.exp y) =
      Complex.exp (-s * y) * characterRamp χ (Real.exp y) + c * Complex.exp ((1 - s) * y) := by
    have he : Complex.exp (-s * y) * (Real.exp y : ℂ) = Complex.exp ((1 - s) * y) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      ring
    simp only [gChi, ite_eq_right hχ, mul_add]
    rw [← mul_assoc, he, mul_comm _ c]
  change (∫ y : ℝ in Ioi 0, Complex.exp (-s * y) * gChi χ (Real.exp y)) = _
  simp_rw [hsplit]
  rw [integral_add (characterRamp_line_integrable χ t)
    ((integrableOn_exp_mul_complex_Ioi hneg 0).const_mul c), characterRamp_line_laplace,
    integral_const_mul, integral_exp_mul_complex_Ioi hneg]
  rw [show 1 - s = -(s - 1) by ring]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_div, neg_neg,
    mul_one_div]
  rfl

end D5.S3.CharacterSums.DirichletRampLaplace
