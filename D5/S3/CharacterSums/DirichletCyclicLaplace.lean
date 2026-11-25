/- GID: D5/S3/CharacterSums/DirichletCyclicLaplace
   generality: I
   mirror-B: D5/B/S3/CharacterSums/DirichletCyclicLaplace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual cyclic character family has an explicit half-plane Laplace transform. -/

import D5.S3.CharacterSums.DirichletRampLaplace
import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtHalfPlane

/-! # The actual cyclic family's Laplace transform

The character ramp is absolutely integrable after damping at every complex
exponent with real part greater than one. Taking its real part requires
Schwarz reflection of the transform, rather than taking the real part of its
value at a complex exponent.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology LSeries.notation ArithmeticFunction
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtHalfPlane
open D5.S3.CharacterSums.DirichletRampEndpoint
open D5.S3.CharacterSums.DirichletRampLaplace
open D5.S3.Arith.Robin.CompleteMertensPeak

namespace D5.S3.CharacterSums.DirichletCyclicLaplace

def cyclicPositiveFamily {r : ℕ} (u : ℝ → ℝ)
    (f : Fin (r - 1) → ℝ → ℝ) : ℝ → ℝ :=
  fun x => u x + (1 / (3 * r + 1 : ℝ)) * ∑ j : Fin (r - 1), f j x

def gl1CyclicFamily {N r : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℝ → ℝ :=
  cyclicPositiveFamily (r := r) U (fun j x =>
    (gChi (χ ^ (j.1 + 1)) x).re)

theorem weighted_character_hasSum {N : ℕ} (χ : DirichletCharacter ℂ N)
    (s : ℂ) (y : ℝ) :
    HasSum (fun n : ℕ => Complex.exp (-s * y) *
      (mangoldtRamp n (Real.exp y) : ℂ) * χ (n : ZMod N))
      (Complex.exp (-s * y) * characterRamp χ (Real.exp y)) := by
  have he : Complex.exp (-transformLine 0 * (y : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have h := (weighted_ramps_hasSum χ 0 y).mul_left
    (Complex.exp (-s * (y : ℂ)) / Complex.exp (-transformLine 0 * (y : ℂ)))
  simpa only [← mul_assoc, div_mul_cancel₀ _ he] using h

/-- Damping controls every character ramp by the untwisted nonnegative ramp. -/
private theorem characterRamp_half_plane_integrable {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => Complex.exp (-s * y) *
      characterRamp χ (Real.exp y)) (Ioi 0) := by
  let f : ℕ → ℝ → ℂ := fun n y => Complex.exp (-s * y) *
    (mangoldtRamp n (Real.exp y) : ℂ) * χ (n : ZMod N)
  have hf (n : ℕ) : Continuous (f n) := by
    dsimp only [f]
    exact (show Continuous (fun y : ℝ => Complex.exp (-s * y)) by fun_prop).mul
      (Complex.continuous_ofReal.comp
        ((mangoldtRamp_continuous n).comp Real.continuous_exp)) |>.mul continuous_const
  have hm : Measurable (fun y : ℝ => Complex.exp (-s * y) *
      characterRamp χ (Real.exp y)) := by
    apply measurable_of_tendsto_metrizable (f := fun k y => ∑ n ∈ Finset.range k, f n y)
    · intro k
      exact (continuous_finsetSum _ fun n _ => hf n).measurable
    · rw [tendsto_pi_nhds]
      intro y
      exact (weighted_character_hasSum χ s y).tendsto_sum_nat
  refine Integrable.mono (part_integrable hs) hm.aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  simp only [norm_mul, Complex.norm_real]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [characterRamp_eq_range,
    mangoldtPart_eq_range (Real.exp_nonneg y) (Nat.lt_succ_floor (Real.exp y)),
    Real.norm_of_nonneg (Finset.sum_nonneg fun n _ => mangoldtRamp_nonneg n _)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mangoldtRamp_nonneg n _)]
  exact mul_le_of_le_one_right (mangoldtRamp_nonneg n _) (χ.norm_le_one _)

/-- The half-plane identity uses the actual twisted Mangoldt Dirichlet series. -/
theorem characterRamp_half_plane_laplace {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    (∫ y : ℝ in Ioi 0, Complex.exp (-s * y) * characterRamp χ (Real.exp y)) =
      (-deriv χ.LFunction s / χ.LFunction s) / (s * (s - 1)) := by
  let f : ℕ → ℝ → ℂ := fun n y => Complex.exp (-s * y) *
    (mangoldtRamp n (Real.exp y) : ℂ) * χ (n : ZMod N)
  have hi (n : ℕ) : Integrable (f n) (volume.restrict (Ioi 0)) :=
    (mangoldtRamp_laplace_integrable (n := n) hs).mul_const _
  have hnorm : Summable (fun n => ∫ y : ℝ in Ioi 0, ‖f n y‖) := by
    refine (ramp_norm_summable hs).of_nonneg_of_le
      (fun n => integral_nonneg fun y => norm_nonneg _) fun n => ?_
    change (∫ y : ℝ in Ioi 0, ‖f n y‖) ≤
      ∫ y : ℝ in Ioi 0, ‖Complex.exp (-s * y) * (mangoldtRamp n (Real.exp y) : ℂ)‖
    simp only [f, norm_mul]
    rw [integral_mul_const]
    exact mul_le_of_le_one_right
      (integral_nonneg fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _))
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
      setIntegral_congr_fun measurableSet_Ioi fun y _ =>
        (weighted_character_hasSum χ s y).tsum_eq.symm
    _ = _ := hsum.unique hL'

/-- The explicit continuation of a nonprincipal corrected ramp. -/
def characterTransform {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  (-deriv χ.LFunction s / χ.LFunction s) / (s * (s - 1)) +
    (deriv χ.LFunction 1 / χ.LFunction 1) / (s - 1)

/-- Both absolute convergence and the endpoint correction hold on the full half-plane. -/
theorem gChi_half_plane_laplace {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => Complex.exp (-s * y) * gChi χ (Real.exp y)) (Ioi 0) ∧
      (∫ y : ℝ in Ioi 0, Complex.exp (-s * y) * gChi χ (Real.exp y)) =
        characterTransform χ s := by
  let c : ℂ := deriv χ.LFunction 1 / χ.LFunction 1
  have hneg : (1 - s).re < 0 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hsplit (y : ℝ) : Complex.exp (-s * y) * gChi χ (Real.exp y) =
      Complex.exp (-s * y) * characterRamp χ (Real.exp y) +
        c * Complex.exp ((1 - s) * y) := by
    have he : Complex.exp (-s * y) * (Real.exp y : ℂ) =
        Complex.exp ((1 - s) * y) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      ring
    simp only [gChi, ite_eq_right hχ, mul_add]
    rw [← mul_assoc, he, mul_comm _ c]
  have hconst := (integrableOn_exp_mul_complex_Ioi hneg 0).const_mul c
  have hchar := characterRamp_half_plane_integrable χ hs
  constructor
  · exact (hchar.add hconst).congr (Eventually.of_forall fun y => (hsplit y).symm)
  · simp_rw [hsplit]
    rw [integral_add hchar hconst, characterRamp_half_plane_laplace χ hs,
      integral_const_mul, integral_exp_mul_complex_Ioi hneg]
    rw [show 1 - s = -(s - 1) by ring]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_div, neg_neg,
      mul_one_div]
    simp only [characterTransform, c, neg_div]

/-- The real-part ramp has the Schwarz-symmetrized transform. -/
private theorem real_part_laplace {f : ℝ → ℂ} {s : ℂ}
    (hi : IntegrableOn (fun y : ℝ => Complex.exp (-s * y) * f y) (Ioi 0))
    (hc : IntegrableOn (fun y : ℝ => Complex.exp (-star s * y) * f y) (Ioi 0)) :
    IntegrableOn (fun y : ℝ => Complex.exp (-s * y) * (f y).re) (Ioi 0) ∧
      (∫ y : ℝ in Ioi 0, Complex.exp (-s * y) * (f y).re) =
        ((∫ y : ℝ in Ioi 0, Complex.exp (-s * y) * f y) +
          star (∫ y : ℝ in Ioi 0, Complex.exp (-star s * y) * f y)) / 2 := by
  have he (y : ℝ) : Complex.exp (-s * y) * ((f y).re : ℂ) =
      (Complex.exp (-s * y) * f y +
        star (Complex.exp (-star s * y) * f y)) / 2 := by
    have hexp : star (Complex.exp (-star s * (y : ℂ))) = Complex.exp (-s * y) := by
      change (starRingEnd ℂ) (Complex.exp _) = _
      rw [← Complex.exp_conj]
      congr 1
      simp
    have hr : ((f y).re : ℂ) = (f y + star (f y)) / 2 := by
      apply Complex.ext <;> simp <;> ring
    rw [star_mul, hexp, hr]
    ring
  have hci := (RCLike.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ).integrable_comp_iff.mpr hc
  change IntegrableOn (fun y : ℝ =>
    star (Complex.exp (-star s * y) * f y)) (Ioi 0) at hci
  constructor
  · exact ((hi.add hci).div_const (2 : ℂ)).congr
      (Eventually.of_forall fun y => (he y).symm)
  · simp_rw [he]
    rw [integral_div, integral_add hi hci]
    have hint := integral_conj (μ := volume.restrict (Ioi (0 : ℝ)))
      (f := fun y : ℝ => Complex.exp (-star s * y) * f y)
    simp only [starRingEnd_apply] at hint
    rw [hint]

/-- The zeta summand, with its double-pole main term subtracted. -/
def zetaTransform (s : ℂ) : ℂ :=
  (-deriv riemannZeta s / riemannZeta s) / (s * (s - 1)) -
    1 / (s - 1) ^ 2 + ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) / (s - 1)

/-- An explicit formula retaining the reflection required by the actual real-valued family. -/
def cyclicTransform {N r : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  zetaTransform s + (1 / (3 * r + 1 : ℂ)) *
    ∑ j : Fin (r - 1),
      (characterTransform (χ ^ (j.1 + 1)) s +
        star (characterTransform (χ ^ (j.1 + 1)) (star s))) / 2

/-- The actual cyclic family, with no zero or pole hypotheses, has the stated transform. -/
theorem gl1CyclicFamily_half_plane_laplace {N r : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hr : r ≤ orderOf χ)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => Complex.exp (-s * y) *
      (gl1CyclicFamily (r := r) χ (Real.exp y) : ℂ)) (Ioi 0) ∧
      (∫ y : ℝ in Ioi 0, Complex.exp (-s * y) *
        (gl1CyclicFamily (r := r) χ (Real.exp y) : ℂ)) = cyclicTransform (r := r) χ s := by
  have hj (j : Fin (r - 1)) : χ ^ (j.1 + 1) ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf (by omega)
    have := j.isLt
    omega
  have hm (j : Fin (r - 1)) := gChi_half_plane_laplace (χ ^ (j.1 + 1)) (hj j) hs
  have hc (j : Fin (r - 1)) := gChi_half_plane_laplace (χ ^ (j.1 + 1)) (hj j)
    (show 1 < (star s).re by simpa using hs)
  have hreal (j : Fin (r - 1)) := real_part_laplace (hm j).1 (hc j).1
  let a : ℂ := 1 / (3 * r + 1 : ℂ)
  have hsplit (y : ℝ) : Complex.exp (-s * y) *
      (gl1CyclicFamily (r := r) χ (Real.exp y) : ℂ) =
      Complex.exp (-s * y) * (U (Real.exp y) : ℂ) +
        a * ∑ j : Fin (r - 1), Complex.exp (-s * y) *
          ((gChi (χ ^ (j.1 + 1)) (Real.exp y)).re : ℂ) := by
    simp only [gl1CyclicFamily, cyclicPositiveFamily, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_sum,
      Complex.ofReal_natCast]
    dsimp only [a]
    push_cast
    rw [mul_add, ← Finset.mul_sum]
    ring
  have hu := u_laplace_half_plane hs
  have hsum := integrable_finsetSum Finset.univ fun j _ => (hreal j).1
  constructor
  · exact (hu.1.add (hsum.const_mul a)).congr
      (Eventually.of_forall fun y => (hsplit y).symm)
  · simp_rw [hsplit]
    rw [integral_add hu.1 (hsum.const_mul a), integral_const_mul,
      integral_finsetSum _ fun j _ => (hreal j).1, hu.2]
    simp_rw [(hreal _).2, (hm _).2, (hc _).2]
    rfl

end D5.S3.CharacterSums.DirichletCyclicLaplace
