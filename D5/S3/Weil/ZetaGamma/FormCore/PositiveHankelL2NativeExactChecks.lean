/- TRANSIENT SOURCE_ONLY / UNCOMPILED exact checks, 2026-10-25.
This file is not a retained D5 mathematical module and has no registration
or Describe target. Stage it only for the eventual scoped native check,
preserve its acceptance evidence, and remove it before a PR.
The exponential inputs are noncompact on the positive half-line.
Neither actual Hankel integrability nor its series identity is assumed.
-/
import D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Filter
open D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2

private def exponentialInput (a s : ℝ) : ℂ := (Real.exp (-a * s) : ℂ)

private theorem exponentialInput_sq (a s : ℝ) :
    ‖exponentialInput a s‖ ^ 2 = Real.exp ((-2 * a) * s) := by
  unfold exponentialInput
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    ← Real.exp_nat_mul]
  congr 1
  ring

private theorem exponentialInput_memLp {a : ℝ} (ha : 0 < a) :
    MemLp (exponentialInput a) 2 halfline := by
  apply (memLp_two_iff_integrable_sq_norm
    (show Continuous (exponentialInput a) by
      unfold exponentialInput
      fun_prop).aestronglyMeasurable).2
  simp_rw [exponentialInput_sq]
  exact integrableOn_exp_mul_Ioi (by linarith : -2 * a < 0) 0

private theorem exponentialInput_mass {a : ℝ} (ha : 0 < a) :
    (∫ s : ℝ, ‖exponentialInput a s‖ ^ 2 ∂halfline) = 1 / (2 * a) := by
  simp_rw [exponentialInput_sq]
  rw [integral_exp_mul_Ioi (by linarith : -2 * a < 0) 0]
  norm_num

private theorem exponential_laplace {a b : ℝ} (hab : 0 < b + a) :
    literalLaplace b (exponentialInput a) = ((1 / (b + a) : ℝ) : ℂ) := by
  unfold literalLaplace
  calc
    _ = ∫ s : ℝ in Ioi 0, (Real.exp ((-(b + a)) * s) : ℂ) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by
        change (Real.exp (-b * s) : ℂ) * (Real.exp (-a * s) : ℂ) = _
        rw [← Complex.ofReal_mul, ← Real.exp_add]
        congr 2
        ring
    _ = _ := by
      rw [integral_complex_ofReal,
        integral_exp_mul_Ioi (by linarith : -(b + a) < 0) 0]
      norm_num

private theorem exponential_laplace_sq {a b : ℝ} (hab : 0 < b + a) :
    Complex.normSq (literalLaplace b (exponentialInput a)) =
      (1 / (b + a)) ^ 2 := by
  rw [exponential_laplace hab]
  simp only [Complex.normSq_ofReal]
  ring

/- All positive rates, including k<1/4: the actual input L2 pays the
actual Hankel theorem. Only then are the individual Laplace values
evaluated and their full summable series substituted. -/
example {a k : ℝ} (ha : 0 < a) (hk : 0 < k) :
    Summable (fun n : ℕ => (1 / (k + n + a)) ^ 2) ∧
      actualHankel k (exponentialInput a) =
        ((∑' n : ℕ, (1 / (k + n + a)) ^ 2 : ℝ) : ℂ) := by
  obtain ⟨_, _, _, _, hS, hH, _, _, _⟩ :=
    positive_hankel_actual_l2_domain_all_positive_rates hk _ (exponentialInput_memLp ha)
  have hterm : (fun n : ℕ =>
      Complex.normSq (literalLaplace (k + n) (exponentialInput a))) =
        (fun n : ℕ => (1 / (k + n + a)) ^ 2) := by
    funext n
    exact exponential_laplace_sq (by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)
  rw [hterm] at hS hH
  exact ⟨hS, hH⟩

/- The improved pi bound is also checked on the same genuinely noncompact
family. Both the absolute and complex actual domains remain explicit. -/
example {a k : ℝ} (ha : 0 < a) (hk : (1 / 4 : ℝ) ≤ k) :
    Integrable (hankelAbsolute k (exponentialInput a)) (halfline.prod halfline) ∧
      Integrable (hankelIntegrand k (exponentialInput a)) (halfline.prod halfline) ∧
      0 ≤ (actualHankel k (exponentialInput a)).re ∧
      (actualHankel k (exponentialInput a)).re ≤ Real.pi / (2 * a) := by
  obtain ⟨hAi, _, hHi, _, _, _, hpos, _, hbound⟩ :=
    positive_hankel_actual_l2_domain_quarter_sharp hk _ (exponentialInput_memLp ha)
  refine ⟨hAi, hHi, hpos, ?_⟩
  calc
    _ ≤ Real.pi * ∫ s : ℝ, ‖exponentialInput a s‖ ^ 2 ∂halfline := hbound
    _ = Real.pi / (2 * a) := by
      rw [exponentialInput_mass ha]
      ring

