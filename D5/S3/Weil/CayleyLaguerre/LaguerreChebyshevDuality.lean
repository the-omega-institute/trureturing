/- GID: D5/S3/Weil/CayleyLaguerre/LaguerreChebyshevDuality
   generality: I
   mirror-B: D5/B/S3/Weil/CayleyLaguerre/LaguerreChebyshevDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Laguerre time tomography equals the Chebyshev derivative jet. -/

import D5.S3.Weil.Budget.PositiveCayleyScaleTransport
import D5.S3.Weil.CayleyLaguerre.CayleyMomentTransport
import D5.S3.Weil.TestFunctions.CayleyLaguerreMomentTomography
import Mathlib.MeasureTheory.Group.MeasurableEquiv

/- Library-search audit trail (2026-08-30):
   * The canonical resolvent-weighted measure and its Cayley coordinate are
     imported from `PositiveCayleyScaleTransport`; body-shape searches for
     resolvent `withDensity` constructions found that owner and no second
     public evenness bridge.
   * `CayleyLaguerreMomentTomography.laguerre_moment_tomography` is the exact
     time-axis constituent, while
     `CayleyMomentTransport.chebyshev_stieltjes_jet` is the exact scale-axis
     constituent. Neither frozen theorem states their common public equality.
   * Pinned Mathlib has no Laguerre--Chebyshev duality theorem. It supplies
     integration against `withDensity`, used only to identify both imported
     constituents on the canonical weighted measure. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open D5.S3.Weil.Budget.PositiveCayleyScaleTransport
open D5.S3.Weil.CayleyLaguerre.CayleyMomentTransport
open D5.S3.Weil.TestFunctions.CayleyLaguerreMomentTomography

namespace D5.S3.Weil.CayleyLaguerre.LaguerreChebyshevDuality

/-- The Laguerre observation of an even resolvent correlation is the same
Cayley moment as the derivative jet of its Stieltjes budget curve. -/
theorem laguerre_chebyshev_duality
    (nu : Measure Real) (n : Nat) (u : Real)
    (p : Fin (n + 1) -> Real)
    (hEven : Measure.map (fun xi : Real => -xi) nu = nu)
    (hn : 1 <= n) (uPositive : 0 < u)
    (coefficientExpansion : forall x : Real,
      (Polynomial.Chebyshev.T Real (n : Int)).eval (1 - 2 * x) =
        Finset.univ.sum (fun k => p k * x ^ (k : Nat)))
    (budgetIntegrable :
      Integrable (fun xi : Real => 1 / (xi ^ 2 + u)) nu) :
    let scale := Real.sqrt u
    let weighted := resolventWeightedMeasure nu scale
    let budget : Real -> Real := fun v =>
      integral nu (fun xi : Real => 1 / (xi ^ 2 + v))
    (budget u : Complex) - (2 * scale : Real) *
        integral (volume.restrict (Ioi 0)) (fun t : Real =>
          ((Real.exp (-scale * t) *
            D5.S3.Analytic.LiCausalTrichotomy.laguerreOne (n - 1)
              (2 * scale * t) : Real) : Complex) *
            resolventCorrelation weighted t) =
      Complex.ofReal (Finset.univ.sum (fun k : Fin (n + 1) =>
        p k * u ^ (k : Nat) *
          ((-1 : Real) ^ (k : Nat) / ((k : Nat).factorial : Real)) *
            iteratedDeriv (k : Nat) budget u)) := by
  dsimp only
  let scale : Real := Real.sqrt u
  let weighted : Measure Real := resolventWeightedMeasure nu scale
  have scalePositive : 0 < scale := Real.sqrt_pos.2 uPositive
  have scaleSquare : scale ^ 2 = u := by
    exact Real.sq_sqrt uPositive.le
  have weightedIntegrable :
      Integrable (fun xi : Real => (xi ^ 2 + scale ^ 2)⁻¹) nu := by
    simpa only [one_div, scaleSquare] using budgetIntegrable
  letI : IsFiniteMeasure weighted := by
    dsimp only [weighted, resolventWeightedMeasure]
    exact isFiniteMeasure_withDensity_ofReal weightedIntegrable.hasFiniteIntegral
  have mapWithDensityEq
      (mu : Measure Real) (f : Real -> Real) (g : Real -> ENNReal)
      (hf : Measurable f) (hg : Measurable g) :
      (Measure.map f mu).withDensity g =
        Measure.map f (mu.withDensity (g ∘ f)) := by
    ext s hs
    rw [withDensity_apply _ hs, MeasureTheory.setLIntegral_map hs hg hf]
    rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs)]
    rfl
  have weightedEven : Measure.map (fun xi : Real => -xi) weighted = weighted := by
    let density : Real -> ENNReal := fun xi =>
      ENNReal.ofReal ((xi ^ 2 + scale ^ 2)⁻¹)
    have densityMeasurable : Measurable density := by
      dsimp only [density]
      fun_prop
    have densityNeg : density ∘ (fun xi : Real => -xi) = density := by
      funext xi
      simp only [density, Function.comp_apply, neg_sq]
    have mappedDensity := mapWithDensityEq nu (fun xi : Real => -xi) density
      measurable_neg densityMeasurable
    dsimp only [weighted, resolventWeightedMeasure]
    change Measure.map (fun xi : Real => -xi) (nu.withDensity density) =
      nu.withDensity density
    calc
      Measure.map (fun xi : Real => -xi) (nu.withDensity density) =
          (Measure.map (fun xi : Real => -xi) nu).withDensity density := by
        simpa only [densityNeg] using mappedDensity.symm
      _ = nu.withDensity density := by rw [hEven]
  have densityMeasurable : Measurable fun xi : Real =>
      ENNReal.ofReal ((xi ^ 2 + scale ^ 2)⁻¹) := by
    fun_prop
  have densityFinite : forall xi : Real,
      ENNReal.ofReal ((xi ^ 2 + scale ^ 2)⁻¹) < (⊤ : ENNReal) := by
    intro xi
    exact ENNReal.ofReal_lt_top
  have massIdentity : spectralMass weighted =
      integral nu (fun xi : Real => 1 / (xi ^ 2 + u)) := by
    calc
      spectralMass weighted = integral weighted (fun _xi : Real => (1 : Real)) := by
        simp only [spectralMass, integral_const, Measure.real, smul_eq_mul, mul_one]
      _ = integral nu (fun xi : Real =>
          (ENNReal.ofReal ((xi ^ 2 + scale ^ 2)⁻¹)).toReal • (1 : Real)) := by
        dsimp only [weighted, resolventWeightedMeasure]
        exact integral_withDensity_eq_integral_toReal_smul densityMeasurable
          (Filter.Eventually.of_forall densityFinite) _
      _ = integral nu (fun xi : Real => 1 / (xi ^ 2 + u)) := by
        apply integral_congr_ae
        filter_upwards with xi
        rw [ENNReal.toReal_ofReal (by positivity)]
        simp only [smul_eq_mul, mul_one, one_div, scaleSquare]
  have momentIdentity : cayleyMoment weighted n scale =
      integral nu (fun xi : Real =>
        (((xi : Complex) + Complex.I * scale) /
          ((xi : Complex) - Complex.I * scale)) ^ n / (xi ^ 2 + u)) := by
    rw [cayleyMoment]
    dsimp only [weighted, resolventWeightedMeasure]
    rw [integral_withDensity_eq_integral_toReal_smul densityMeasurable
      (Filter.Eventually.of_forall densityFinite)]
    apply integral_congr_ae
    filter_upwards with xi
    rw [ENNReal.toReal_ofReal (by positivity)]
    simp only [Complex.real_smul, scaleSquare]
    rw [cayleyCharacter]
    push_cast
    ring
  have timeTomography :=
    (laguerre_moment_tomography weighted weightedEven hn scalePositive).2
  have scaleTomography := chebyshev_stieltjes_jet nu n u p hEven uPositive
    coefficientExpansion budgetIntegrable
  change integral nu (fun xi : Real =>
      (((xi : Complex) + Complex.I * scale) /
        ((xi : Complex) - Complex.I * scale)) ^ n / (xi ^ 2 + u)) = _
    at scaleTomography
  calc
    ((integral nu (fun xi : Real => 1 / (xi ^ 2 + u)) : Real) : Complex) -
        (2 * scale : Real) * integral (volume.restrict (Ioi 0))
          (fun t : Real =>
            ((Real.exp (-scale * t) *
              D5.S3.Analytic.LiCausalTrichotomy.laguerreOne (n - 1)
                (2 * scale * t) : Real) : Complex) *
              resolventCorrelation weighted t) = cayleyMoment weighted n scale := by
      simpa only [massIdentity] using timeTomography.symm
    _ = integral nu (fun xi : Real =>
        (((xi : Complex) + Complex.I * scale) /
          ((xi : Complex) - Complex.I * scale)) ^ n / (xi ^ 2 + u)) :=
      momentIdentity
    _ = Complex.ofReal (Finset.univ.sum (fun k : Fin (n + 1) =>
        p k * u ^ (k : Nat) *
          ((-1 : Real) ^ (k : Nat) / ((k : Nat).factorial : Real)) *
            iteratedDeriv (k : Nat)
              (fun v : Real => integral nu
                (fun xi : Real => 1 / (xi ^ 2 + v))) u)) := scaleTomography

#print axioms laguerre_chebyshev_duality

end D5.S3.Weil.CayleyLaguerre.LaguerreChebyshevDuality
