/- GID: D5/S3/Weil/Separator/ArchimedeanConvergence
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/ArchimedeanConvergence
   mirror-E: none(waiver:kernel-verified-integrability-and-criterion-only)
   anchors: []
   digest: Weil tests converge archimedeanly, removing hArch from the prime-side criterion. -/

import D5.S3.Fourier.FourierLaplaceEntire
import D5.S3.Weil.PrimePoleTerms
import D5.S3.Weil.Separator.ExplicitFormulaWeilCriterion
import D5.S3.Weil.TestFunctions.FourierLaplaceClosedStripDecay
import D5.S3.Weil.ZetaExplicit.FullLine

/-!
# Archimedean convergence

Closed-strip decay of the Fourier-Laplace transform, together with the
repository's Zeta23 gamma-factor bound, proves archimedean integrability for
every `WeilTestFunction`. The frozen explicit-formula Weil criterion therefore
has no remaining archimedean-convergence hypothesis.

The criterion remains relative to supplied `ZeroData`; this module does not
assert that such data exists, and M1-b remains open. Consequently this is a
reformulation of the Weil criterion, not a proof of the Riemann hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Weil.Separator.ArchimedeanConvergence

open MeasureTheory
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.PrimePoleTerms
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.TestFunctions.FourierLaplaceClosedStripDecay
open D5.S3.Weil.ZeroSum

noncomputable section

private theorem fourierLaplace_continuous_real (g : WeilTestFunction) :
    Continuous (fun t : ℝ => fourierLaplace g (t : ℂ)) :=
  (fourierLaplace_entire g).continuous.comp Complex.continuous_ofReal

private theorem integrable_plus (g : WeilTestFunction) {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ t : ℝ, ‖fourierLaplace g (t : ℂ)‖ ≤ C / (1 + t ^ 2)) :
    Integrable (fun t : ℝ =>
      fourierLaplace g (t : ℂ) *
        logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) :=
  Zeta23.WeilEF.integrable_mul_logDeriv_Gammaℝ_of_decay
    (φ := fun t : ℝ => fourierLaplace g (t : ℂ)) (C := C) (σ := (1 / 2 : ℝ))
    (fourierLaplace_continuous_real g) hC hdecay (by norm_num) (by norm_num)

private theorem integrable_minus (g : WeilTestFunction) {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ t : ℝ, ‖fourierLaplace g (t : ℂ)‖ ≤ C / (1 + t ^ 2)) :
    Integrable (fun t : ℝ =>
      fourierLaplace g (t : ℂ) *
        logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I)) := by
  have hcontinuousNeg : Continuous (fun t : ℝ => fourierLaplace g ((-t : ℝ) : ℂ)) := by
    change Continuous ((fun u : ℝ => fourierLaplace g (u : ℂ)) ∘ fun t : ℝ => -t)
    exact (fourierLaplace_continuous_real g).comp continuous_neg
  have hdecayNeg : ∀ t : ℝ, ‖fourierLaplace g ((-t : ℝ) : ℂ)‖ ≤ C / (1 + t ^ 2) := by
    intro t
    simpa only [Complex.ofReal_neg, neg_sq] using hdecay (-t)
  have hbefore : Integrable (fun t : ℝ =>
      fourierLaplace g ((-t : ℝ) : ℂ) *
        logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) :=
    Zeta23.WeilEF.integrable_mul_logDeriv_Gammaℝ_of_decay
      (φ := fun t : ℝ => fourierLaplace g ((-t : ℝ) : ℂ)) (C := C) (σ := (1 / 2 : ℝ))
      hcontinuousNeg hC hdecayNeg (by norm_num) (by norm_num)
  simpa only [neg_neg, Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using hbefore.comp_neg

set_option maxHeartbeats 1000000 in
-- The decay-to-gamma-integrability calculation exceeds the default budget.
/-- The gamma-factor integrability proof needs the enlarged heartbeat budget.
Every repository Weil test function has an integrable archimedean
explicit-formula term. -/
theorem archimedeanConvergent_of_weilTestFunction (g : WeilTestFunction) :
    ArchimedeanConvergent g := by
  obtain ⟨C, hC, hdecay⟩ := fourierLaplace_decay_closedStrip g 0 (by norm_num)
  have hdecayReal : ∀ t : ℝ, ‖fourierLaplace g (t : ℂ)‖ ≤ C / (1 + t ^ 2) := by
    intro t
    simpa using hdecay (t : ℂ) (by simp)
  have hplus := integrable_plus g hC hdecayReal
  have hminus := integrable_minus g hC hdecayReal
  have hsum : Integrable (fun t : ℝ =>
      fourierLaplace g (t : ℂ) *
        (logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) +
         logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I))) := by
    rw [show (fun t : ℝ =>
        fourierLaplace g (t : ℂ) *
          (logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) +
           logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I))) =
        (fun t : ℝ => fourierLaplace g (t : ℂ) *
          logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) +
        (fun t : ℝ => fourierLaplace g (t : ℂ) *
          logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I)) by
      funext t
      exact mul_add _ _ _]
    exact hplus.add hminus
  have hintegrand : archimedeanIntegrand g = fun t : ℝ =>
      fourierLaplace g (t : ℂ) *
        (logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) +
         logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) - (t : ℂ) * Complex.I)) := by
    funext t
    unfold archimedeanIntegrand
    have harg : (1 / 4 : ℂ) + Complex.I * (t : ℂ) / 2 =
        (1 / 4 : ℂ) + (t : ℂ) / 2 * Complex.I := by ring
    rw [harg, ← Zeta23.WeilEF.gammaR_bracket t, mul_comm]
    norm_num
  rw [ArchimedeanConvergent]
  rw [hintegrand]
  exact hsum

/-- Relative to supplied zero data, RH is equivalent to nonnegativity of the
prime-side explicit-formula expression on every convolution square. -/
theorem rh_iff_primeSidePositivity (Z : ZeroData) :
    RiemannHypothesis ↔
      ∀ g : WeilTestFunction,
        0 ≤ (poleTerm (convolutionSquare g) -
          primeTerm (convolutionSquare g) +
          archimedeanTerm (convolutionSquare g)
            (archimedeanConvergent_of_weilTestFunction (convolutionSquare g))).re :=
  Separator.ExplicitFormulaWeilCriterion.rh_iff_explicitFormulaPositivity Z
    (fun g => archimedeanConvergent_of_weilTestFunction (convolutionSquare g))

-- The quantified domains and the derived convergence witness are checked.
example : Nonempty WeilTestFunction := ⟨standardTestFunction⟩

example (Z : ZeroData) : Nonempty ZeroData := ⟨Z⟩

example (g : WeilTestFunction) : ArchimedeanConvergent g :=
  archimedeanConvergent_of_weilTestFunction g

#print axioms archimedeanConvergent_of_weilTestFunction
#print axioms rh_iff_primeSidePositivity

end

end D5.S3.Weil.Separator.ArchimedeanConvergence
