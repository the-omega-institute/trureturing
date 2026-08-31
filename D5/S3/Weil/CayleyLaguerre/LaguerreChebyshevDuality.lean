/- GID: D5/S3/Weil/CayleyLaguerre/LaguerreChebyshevDuality
   generality: I
   mirror-B: D5/B/S3/Weil/CayleyLaguerre/LaguerreChebyshevDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Laguerre time tomography equals the Chebyshev derivative jet. -/

import D5.S3.Weil.CayleyLaguerre.CayleyMomentTransport
import D5.S3.Analytic.LiCausalTrichotomy
import D5.S3.Weil.Budget.PositiveCayleyScaleTransport
import D5.S3.Weil.TestFunctions.CayleyLaguerreMomentTomography

/- Library-search audit trail (2026-08-30):
   * `LiCausalTrichotomy` owns the complex Laplace-moment and binomial
     identities used by the frozen Laguerre family.
   * `CayleyLaguerreMomentTomography.laguerre_moment_tomography` is the frozen
     owner of the time-axis identity; this module projects its second conjunct.
   * `CayleyMomentTransport.chebyshev_stieltjes_jet` supplies the scale-axis
     constituent. No frozen theorem states their common public equality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open D5.S3.Weil.CayleyLaguerre.CayleyMomentTransport

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
    let budget : Real -> Real := fun v =>
      integral nu (fun xi : Real => 1 / (xi ^ 2 + v))
    (budget u : Complex) - (2 * scale : Real) *
        integral (volume.restrict (Ioi 0)) (fun t : Real =>
          ((Real.exp (-scale * t) *
            D5.S3.Analytic.LiCausalTrichotomy.laguerreOne
              (n - 1) (2 * scale * t) : Real) : Complex) *
            D5.S3.Weil.TestFunctions.CayleyLaguerreMomentTomography.resolventCorrelation
              (D5.S3.Weil.Budget.PositiveCayleyScaleTransport.resolventWeightedMeasure
                nu scale) t) =
      Complex.ofReal (Finset.univ.sum (fun k : Fin (n + 1) =>
        p k * u ^ (k : Nat) *
          ((-1 : Real) ^ (k : Nat) / ((k : Nat).factorial : Real)) *
            iteratedDeriv (k : Nat) budget u)) := by
  dsimp only
  let scale : Real := Real.sqrt u
  let weighted : Measure Real :=
    D5.S3.Weil.Budget.PositiveCayleyScaleTransport.resolventWeightedMeasure nu scale
  have scalePositive : 0 < scale := Real.sqrt_pos.2 uPositive
  have scaleSquare : scale ^ 2 = u := by
    exact Real.sq_sqrt uPositive.le
  have weightedIntegrable :
      Integrable (fun xi : Real => (xi ^ 2 + scale ^ 2)⁻¹) nu := by
    simpa only [one_div, scaleSquare] using budgetIntegrable
  letI : IsFiniteMeasure weighted := by
    dsimp only [weighted,
      D5.S3.Weil.Budget.PositiveCayleyScaleTransport.resolventWeightedMeasure]
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
    dsimp only [weighted,
      D5.S3.Weil.Budget.PositiveCayleyScaleTransport.resolventWeightedMeasure]
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
  have massIdentity : weighted.real Set.univ =
      integral nu (fun xi : Real => 1 / (xi ^ 2 + u)) := by
    calc
      weighted.real Set.univ = integral weighted (fun _xi : Real => (1 : Real)) := by
        simp only [integral_const, Measure.real, smul_eq_mul, mul_one]
      _ = integral nu (fun xi : Real =>
          (ENNReal.ofReal ((xi ^ 2 + scale ^ 2)⁻¹)).toReal • (1 : Real)) := by
        dsimp only [weighted,
          D5.S3.Weil.Budget.PositiveCayleyScaleTransport.resolventWeightedMeasure]
        exact integral_withDensity_eq_integral_toReal_smul densityMeasurable
          (Filter.Eventually.of_forall densityFinite) _
      _ = integral nu (fun xi : Real => 1 / (xi ^ 2 + u)) := by
        apply integral_congr_ae
        filter_upwards with xi
        rw [ENNReal.toReal_ofReal (by positivity)]
        simp only [smul_eq_mul, mul_one, one_div, scaleSquare]
  have momentIdentity : integral weighted (fun xi : Real =>
      (((xi : Complex) + Complex.I * scale) /
        ((xi : Complex) - Complex.I * scale)) ^ n) =
      integral nu (fun xi : Real =>
        (((xi : Complex) + Complex.I * scale) /
          ((xi : Complex) - Complex.I * scale)) ^ n / (xi ^ 2 + u)) := by
    dsimp only [weighted,
      D5.S3.Weil.Budget.PositiveCayleyScaleTransport.resolventWeightedMeasure]
    rw [integral_withDensity_eq_integral_toReal_smul densityMeasurable
      (Filter.Eventually.of_forall densityFinite)]
    apply integral_congr_ae
    filter_upwards with xi
    rw [ENNReal.toReal_ofReal (by positivity)]
    simp only [Complex.real_smul, scaleSquare]
    push_cast
    ring
  have timeTomography :=
    (D5.S3.Weil.TestFunctions.CayleyLaguerreMomentTomography.laguerre_moment_tomography
      weighted weightedEven hn scalePositive).2
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
              D5.S3.Analytic.LiCausalTrichotomy.laguerreOne
                (n - 1) (2 * scale * t) : Real) : Complex) *
              D5.S3.Weil.TestFunctions.CayleyLaguerreMomentTomography.resolventCorrelation
                weighted t) =
        integral weighted (fun xi : Real =>
          (((xi : Complex) + Complex.I * scale) /
            ((xi : Complex) - Complex.I * scale)) ^ n) := by
      simpa only [
        D5.S3.Weil.TestFunctions.CayleyLaguerreMomentTomography.cayleyMoment,
        D5.S3.Weil.TestFunctions.CayleyLaguerreMomentTomography.cayleyCharacter,
        D5.S3.Weil.TestFunctions.CayleyLaguerreMomentTomography.spectralMass,
        Nat.sub_add_cancel hn, massIdentity] using timeTomography.symm
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
