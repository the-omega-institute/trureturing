/- GID: D5/S3/Weil/ZetaGamma/FormCore/SourceActualGammaCross
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:actual-gamma-domain-and-cross)
   anchors: []
   utility: none
   digest: Actual Gamma graph closure and complete positive-tail resonance identity. -/

/- SOURCE_ONLY / UNCOMPILED, 2026-10-25.
Literal shifted Gamma graph equivalence and actual complete reflected cross.
Consumes actual finite-to-infinite bare W closure and actual L1 residual
series. No target Gamma cross/energy identity is supplied as a premise.
No native verification, KPI, Reg or admission claim is made. -/

import D5.S3.Weil.ZetaGamma.FormCore.SourceGammaResidualCross
import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.SourceActualGammaCross

open MeasureTheory Set Filter
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample.Symbol
open D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal
open D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure
open D5.S3.Weil.ZetaGamma.FormCore.SourceGammaResidualCross
open scoped Topology ComplexConjugate FourierTransform ENNReal

private abbrev halfline : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
private def zeroExtension (u : ℝ → ℂ) : ℝ → ℂ := (Ioi (0 : ℝ)).indicator u

private theorem continuous_unitarySourceFourier {f : ℝ → ℂ} (hf : Integrable f volume) :
    Continuous (unitarySourceFourier f) := by
  unfold unitarySourceFourier
  exact continuous_const.mul
    ((D5.S3.Weil.ZetaGamma.FormCore.LineFourier.continuous_raw_fourier hf).comp
      (by fun_prop))

private def gammaRationalFactor (ξ : ℝ) : ℝ :=
  (ξ ^ 2 + 1 / 16) / (ξ ^ 2 + 25 / 16)

private def gammaScale : ℝ := 2 / Real.sqrt Real.pi

private def gammaBase : ℝ :=
  (Complex.digamma (1 / 4)).re - Real.log Real.pi

private def gammaRemainder (c ξ : ℝ) : ℝ :=
  gammaScale * (gammaRationalFactor ξ * gammaBase) +
    (1 + 4 * Real.sqrt Real.pi + c)

private def gammaRemainderBound (c : ℝ) : ℝ :=
  gammaScale * |gammaBase| + |1 + 4 * Real.sqrt Real.pi + c|

private theorem gammaScale_positive : 0 < gammaScale := by
  unfold gammaScale
  exact div_pos (by norm_num) (Real.sqrt_pos.2 Real.pi_pos)

/-- New lower bound is uniform at ξ=0, where equality is attained.
The original frozen Gamma/log bounds are neither restated nor reproved. -/
private theorem gammaRationalFactor_bounds (ξ : ℝ) :
    (1 / 25 : ℝ) ≤ gammaRationalFactor ξ ∧ gammaRationalFactor ξ ≤ 1 := by
  have hd : 0 < ξ ^ 2 + (25 / 16 : ℝ) := by positivity
  unfold gammaRationalFactor
  constructor
  · apply (le_div_iff₀ hd).2
    nlinarith [sq_nonneg ξ]
  · apply (div_le_one hd).2
    linarith

/-- Definitional connection to the literal original owner. Its private
gammaRatio/gammaDensity unfold through change; no owner visibility change
and no replacement weight is needed. -/
private theorem gammaWeight_quarter_decomposition (c ξ : ℝ) :
    gammaWeight ξ + c =
      gammaScale * (gammaRationalFactor ξ * actualBareQuarterWeight ξ) +
        gammaRemainder c ξ := by
  change
    (2 / Real.sqrt Real.pi) *
        (((ξ ^ 2 + 1 / 16) / (ξ ^ 2 + 25 / 16)) *
          ((Complex.digamma (((1 / 4 : ℝ) : ℂ) + Complex.I * (ξ : ℂ))).re -
            Real.log Real.pi)) + 1 + 4 * Real.sqrt Real.pi + c =
    (2 / Real.sqrt Real.pi) *
        (((ξ ^ 2 + 1 / 16) / (ξ ^ 2 + 25 / 16)) *
          ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (ξ : ℂ))).re -
            (Complex.digamma (1 / 4)).re)) +
      ((2 / Real.sqrt Real.pi) *
          (((ξ ^ 2 + 1 / 16) / (ξ ^ 2 + 25 / 16)) *
            ((Complex.digamma (1 / 4)).re - Real.log Real.pi)) +
        (1 + 4 * Real.sqrt Real.pi + c))
  have hquarter : ((1 / 4 : ℝ) : ℂ) = (1 / 4 : ℂ) := by norm_num
  rw [hquarter]
  ring

private theorem gammaRemainder_abs_le (c ξ : ℝ) :
    |gammaRemainder c ξ| ≤ gammaRemainderBound c := by
  have hr := gammaRationalFactor_bounds ξ
  have hr0 : 0 ≤ gammaRationalFactor ξ := by linarith [hr.1]
  have hmul :
      gammaScale * gammaRationalFactor ξ * |gammaBase| ≤
        gammaScale * |gammaBase| := by
    have h := mul_le_mul_of_nonneg_left hr.2 gammaScale_positive.le
    simpa only [mul_one] using mul_le_mul_of_nonneg_right h (abs_nonneg gammaBase)
  calc
    _ ≤ |gammaScale * (gammaRationalFactor ξ * gammaBase)| +
        |1 + 4 * Real.sqrt Real.pi + c| := abs_add_le _ _
    _ = gammaScale * gammaRationalFactor ξ * |gammaBase| +
        |1 + 4 * Real.sqrt Real.pi + c| := by
      rw [abs_mul, abs_mul, abs_of_pos gammaScale_positive, abs_of_nonneg hr0]
      ring
    _ ≤ gammaRemainderBound c := by
      unfold gammaRemainderBound
      linarith

private theorem shifted_gamma_quarter_absolute_upper (c ξ : ℝ) :
    |gammaWeight ξ + c| ≤
      gammaScale * actualBareQuarterWeight ξ + gammaRemainderBound c := by
  have hr := gammaRationalFactor_bounds ξ
  have hp := actual_bare_quarter_nonneg ξ
  have hr0 : 0 ≤ gammaRationalFactor ξ := by linarith [hr.1]
  have hmainNN : 0 ≤ gammaScale * (gammaRationalFactor ξ * actualBareQuarterWeight ξ) :=
    mul_nonneg gammaScale_positive.le (mul_nonneg hr0 hp)
  have hmain :
      gammaScale * (gammaRationalFactor ξ * actualBareQuarterWeight ξ) ≤
        gammaScale * actualBareQuarterWeight ξ := by
    have h := mul_le_mul_of_nonneg_right hr.2 hp
    simpa only [one_mul] using mul_le_mul_of_nonneg_left h gammaScale_positive.le
  rw [gammaWeight_quarter_decomposition]
  calc
    _ ≤ |gammaScale * (gammaRationalFactor ξ * actualBareQuarterWeight ξ)| +
        |gammaRemainder c ξ| := abs_add_le _ _
    _ ≤ gammaScale * actualBareQuarterWeight ξ + gammaRemainderBound c := by
      rw [abs_of_nonneg hmainNN]
      exact add_le_add hmain (gammaRemainder_abs_le c ξ)

private theorem quarter_le_shifted_gamma_absolute (c ξ : ℝ) :
    actualBareQuarterWeight ξ ≤
      (25 / gammaScale) * (|gammaWeight ξ + c| + gammaRemainderBound c) := by
  have hr := gammaRationalFactor_bounds ξ
  have hp := actual_bare_quarter_nonneg ξ
  have hlo :
      (gammaScale / 25) * actualBareQuarterWeight ξ ≤
        gammaScale * (gammaRationalFactor ξ * actualBareQuarterWeight ξ) := by
    have h := mul_le_mul_of_nonneg_right hr.1 hp
    have h' := mul_le_mul_of_nonneg_left h gammaScale_positive.le
    convert h' using 1 <;> ring
  have hdecomp := gammaWeight_quarter_decomposition c ξ
  have hrem := gammaRemainder_abs_le c ξ
  have hmain :
      gammaScale * (gammaRationalFactor ξ * actualBareQuarterWeight ξ) ≤
        |gammaWeight ξ + c| + gammaRemainderBound c := by
    have habs := le_abs_self (gammaWeight ξ + c)
    have hneg := neg_le_abs (gammaRemainder c ξ)
    linarith
  have h25 :
      actualBareQuarterWeight ξ * gammaScale ≤
        25 * (|gammaWeight ξ + c| + gammaRemainderBound c) := by
    nlinarith [hlo.trans hmain]
  rw [show (25 / gammaScale) *
      (|gammaWeight ξ + c| + gammaRemainderBound c) =
      (25 * (|gammaWeight ξ + c| + gammaRemainderBound c)) / gammaScale by ring]
  exact (le_div_iff₀ gammaScale_positive).2 h25

/-- Arbitrary constant shifts of the literal Gamma multiplier have exactly
the actual quarter-digamma graph domain on each actual complex L1∩L2 source.
The rational factor is retained in the decomposition and bounded both ways;
this is domain equivalence, not an energy equality. -/
theorem shifted_actual_gamma_graph_equivalence {f : ℝ → ℂ}
    (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume) (c : ℝ) :
    Integrable (fun ξ : ℝ =>
      (gammaWeight ξ + c) * ‖unitarySourceFourier f ξ‖ ^ 2) volume ↔
      InActualBareQuarterGraph f := by
  have hmass := unitarySourceFourier_squared_integrable hf₁ hf₂
  have hfreq := continuous_unitarySourceFourier hf₁
  have hGammaM : AEStronglyMeasurable (fun ξ : ℝ =>
      (gammaWeight ξ + c) * ‖unitarySourceFourier f ξ‖ ^ 2) volume :=
    ((finiteGammaWeight_continuous.add continuous_const).mul (hfreq.norm.pow 2)).aestronglyMeasurable
  have hQuarterM : AEStronglyMeasurable (fun ξ : ℝ =>
      actualBareQuarterWeight ξ * ‖unitarySourceFourier f ξ‖ ^ 2) volume :=
    actual_bare_quarter_measurable.aestronglyMeasurable.mul
      (hfreq.aestronglyMeasurable.norm.pow 2)
  constructor
  · intro hGamma
    apply (((hGamma.norm).add (hmass.const_mul (gammaRemainderBound c))).const_mul
      (25 / gammaScale)).mono' hQuarterM
    exact Eventually.of_forall fun ξ => by
      have hq : 0 ≤ ‖unitarySourceFourier f ξ‖ ^ 2 := sq_nonneg _
      change ‖actualBareQuarterWeight ξ * ‖unitarySourceFourier f ξ‖ ^ 2‖ ≤
        (25 / gammaScale) * (‖(gammaWeight ξ + c) * ‖unitarySourceFourier f ξ‖ ^ 2‖ +
          gammaRemainderBound c * ‖unitarySourceFourier f ξ‖ ^ 2)
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (actual_bare_quarter_nonneg ξ) hq)]
      have h := mul_le_mul_of_nonneg_right (quarter_le_shifted_gamma_absolute c ξ) hq
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hq] using
        (show actualBareQuarterWeight ξ * ‖unitarySourceFourier f ξ‖ ^ 2 ≤
          (25 / gammaScale) *
            (|gammaWeight ξ + c| * ‖unitarySourceFourier f ξ‖ ^ 2 +
              gammaRemainderBound c * ‖unitarySourceFourier f ξ‖ ^ 2) from by
          convert h using 1 <;> ring)
  · intro hQ
    apply ((hQ.const_mul gammaScale).add
      (hmass.const_mul (gammaRemainderBound c))).mono' hGammaM
    exact Eventually.of_forall fun ξ => by
      have hq : 0 ≤ ‖unitarySourceFourier f ξ‖ ^ 2 := sq_nonneg _
      change ‖(gammaWeight ξ + c) * ‖unitarySourceFourier f ξ‖ ^ 2‖ ≤
        gammaScale * (actualBareQuarterWeight ξ * ‖unitarySourceFourier f ξ‖ ^ 2) +
          gammaRemainderBound c * ‖unitarySourceFourier f ξ‖ ^ 2
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hq]
      have h := mul_le_mul_of_nonneg_right (shifted_gamma_quarter_absolute_upper c ξ) hq
      calc
        _ ≤ (gammaScale * actualBareQuarterWeight ξ + gammaRemainderBound c) *
            ‖unitarySourceFourier f ξ‖ ^ 2 := h
        _ = _ := by ring

private theorem literal_gamma_bare_residual_decomposition (c ξ : ℝ) :
    gammaWeight ξ + c =
      gammaScale * actualBareQuarterWeight ξ -
        (gammaScale * (3 / 2)) *
          (actualBareQuarterWeight ξ / (ξ ^ 2 + (5 / 4 : ℝ) ^ 2)) -
        (gammaScale * (3 / 2) * gammaBase) /
          (ξ ^ 2 + (5 / 4 : ℝ) ^ 2) +
        (gammaScale * gammaBase + 1 + 4 * Real.sqrt Real.pi + c) := by
  rw [gammaWeight_quarter_decomposition]
  unfold gammaRemainder gammaRationalFactor
  norm_num only [show (5 / 4 : ℝ) ^ 2 = 25 / 16 by norm_num]
  have hd : ξ ^ 2 + (25 / 16 : ℝ) ≠ 0 := by positivity
  field_simp [hd]
  <;> ring

/-- Actual complete Gamma off-diagonal identity, on the ORIGINAL Gamma
graph and the same complex source u. Arbitrary constant shifts cancel.
The series uses the true resonant mixed moment rather than a diagonal
proxy; quarter-rate cancellation and scalar tail compression may be
performed afterwards on this paid actual identity. -/
private theorem actual_gamma_reflected_cross_complete_series
    (c : ℝ) {u : ℝ → ℂ} (hu₁ : Integrable u halfline) (hu₂ : MemLp u 2 halfline)
    (hGamma : Integrable (fun ξ : ℝ =>
      (gammaWeight ξ + c) * ‖unitarySourceFourier (zeroExtension u) ξ‖ ^ 2) volume) :
    Integrable (fun ξ : ℝ => ((gammaWeight ξ + c : ℝ) : ℂ) * actualSourceSpectralCross u ξ) volume ∧
    Real.sqrt Real.pi * (-(∫ ξ : ℝ,
      ((gammaWeight ξ + c : ℝ) : ℂ) * actualSourceSpectralCross u ξ).re) =
      (D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.actualHankel (1 / 4) u).re +
        3 * (∑' n : ℕ, actualResidualLayerCrossValue (5 / 4) ((n : ℝ) + 1 / 4) u) +
        (6 / 5) * ((Complex.digamma (1 / 4)).re - Real.log Real.pi) *
          Complex.normSq (literalSourceLaplace (5 / 4) u) := by
  have hU₁ : Integrable (zeroExtension u) volume :=
    (integrable_indicator_iff measurableSet_Ioi).2 hu₁
  have hU₂ : MemLp (zeroExtension u) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).2 hu₂
  have hWgraph : InActualBareQuarterGraph (zeroExtension u) :=
    (shifted_actual_gamma_graph_equivalence hU₁ hU₂ c).mp hGamma
  obtain ⟨hW₀, hWi₀⟩ := actual_bare_quarter_reflected_cross hu₁ hu₂ hWgraph
  obtain ⟨hB₀, hBS⟩ := actual_residual_reflected_cross_complete_series
    (a := (5 / 4 : ℝ)) (by norm_num) hu₁
  obtain ⟨_, hP₀, hPi₀⟩ := actual_resolvent_reflected_cross_laplace_square
    (a := (5 / 4 : ℝ)) (by norm_num) hu₁
  let C : ℝ → ℂ := actualSourceSpectralCross u
  let A : ℝ → ℂ := fun ξ => (actualBareQuarterWeight ξ : ℂ) * C ξ
  let B : ℝ → ℂ := fun ξ =>
    ((actualBareQuarterWeight ξ / (ξ ^ 2 + (5 / 4 : ℝ) ^ 2) : ℝ) : ℂ) * C ξ
  let P : ℝ → ℂ := fun ξ => actualResolventSymbol (5 / 4) ξ * C ξ
  let K : ℝ := gammaScale * gammaBase + 1 + 4 * Real.sqrt Real.pi + c
  have hA : Integrable A volume := by
    convert hW₀ using 1
    funext ξ
    exact (mul_assoc _ _ _).symm
  have hB : Integrable B volume := hB₀
  have hP : Integrable P volume := by
    convert hP₀ using 1
    funext ξ
    exact (mul_assoc _ _ _).symm
  have hC : Integrable C volume := actual_unweighted_reflected_cross_integrable hu₁ hu₂
  have hARe : (∫ ξ, A ξ).re =
      -(D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.actualHankel (1 / 4) u).re / 2 := by
    convert hWi₀ using 1
    apply congrArg Complex.re
    apply integral_congr_ae
    exact Eventually.of_forall fun ξ => (mul_assoc _ _ _).symm
  have hBRe : (∫ ξ, B ξ).re =
      ∑' n : ℕ, actualResidualLayerCrossValue (5 / 4) ((n : ℝ) + 1 / 4) u :=
    hBS.tsum_eq.symm
  have hPRe : (∫ ξ, P ξ).re = Complex.normSq (literalSourceLaplace (5 / 4) u) / (5 / 2) := by
    have hPi : (∫ ξ, P ξ) =
        (Complex.normSq (literalSourceLaplace (5 / 4) u) : ℂ) /
          ((2 * (5 / 4) : ℝ) : ℂ) := by
      convert hPi₀ using 1
      · apply integral_congr_ae
        exact Eventually.of_forall fun ξ => (mul_assoc _ _ _).symm
      · rfl
    have h := congrArg Complex.re hPi
    rw [Complex.div_ofReal_re, Complex.ofReal_re] at h
    norm_num at h
    exact h
  have hCRe : (∫ ξ, C ξ).re = 0 := actual_constant_reflected_cross_re_zero hu₁ hu₂
  have hPoint (ξ : ℝ) :
      ((gammaWeight ξ + c : ℝ) : ℂ) * C ξ =
        (gammaScale : ℂ) * A ξ - ((gammaScale * (3 / 2) : ℝ) : ℂ) * B ξ -
          ((gammaScale * (3 / 2) * gammaBase : ℝ) : ℂ) * P ξ + (K : ℂ) * C ξ := by
    rw [literal_gamma_bare_residual_decomposition]
    dsimp [A, B, P, K, actualResolventSymbol]
    push_cast
    ring
  have hI1 := hA.const_mul (gammaScale : ℂ)
  have hI2 := hB.const_mul ((gammaScale * (3 / 2) : ℝ) : ℂ)
  have hI3 := hP.const_mul ((gammaScale * (3 / 2) * gammaBase : ℝ) : ℂ)
  have hI4 := hC.const_mul (K : ℂ)
  have hI12 : Integrable (fun ξ => (gammaScale : ℂ) * A ξ -
      ((gammaScale * (3 / 2) : ℝ) : ℂ) * B ξ) volume := hI1.sub hI2
  have hI123 : Integrable (fun ξ => (gammaScale : ℂ) * A ξ -
      ((gammaScale * (3 / 2) : ℝ) : ℂ) * B ξ -
      ((gammaScale * (3 / 2) * gammaBase : ℝ) : ℂ) * P ξ) volume := hI12.sub hI3
  have hGammaCross : Integrable (fun ξ : ℝ => ((gammaWeight ξ + c : ℝ) : ℂ) * C ξ) volume := by
    simp_rw [hPoint]
    exact ((hI1.sub hI2).sub hI3).add hI4
  have hIntegral : (∫ ξ : ℝ, ((gammaWeight ξ + c : ℝ) : ℂ) * C ξ) =
      (gammaScale : ℂ) * (∫ ξ, A ξ) -
        ((gammaScale * (3 / 2) : ℝ) : ℂ) * (∫ ξ, B ξ) -
        ((gammaScale * (3 / 2) * gammaBase : ℝ) : ℂ) * (∫ ξ, P ξ) +
        (K : ℂ) * (∫ ξ, C ξ) := by
    simp_rw [hPoint]
    rw [integral_add hI123 hI4,
      integral_sub hI12 hI3, integral_sub hI1 hI2]
    simp_rw [integral_const_mul]
  refine ⟨hGammaCross, ?_⟩
  change Real.sqrt Real.pi * (-(∫ ξ : ℝ, ((gammaWeight ξ + c : ℝ) : ℂ) * C ξ).re) = _
  rw [hIntegral]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hARe, hBRe, hPRe, hCRe]
  change Real.sqrt Real.pi * _ =
    _ + 3 * _ + (6 / 5) * gammaBase * Complex.normSq (literalSourceLaplace (5 / 4) u)
  unfold gammaScale
  field_simp [ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)]
  <;> ring

private theorem literal_shifted_gamma_even (c ξ : ℝ) :
    gammaWeight (-ξ) + c = gammaWeight ξ + c := by
  rw [literal_gamma_bare_residual_decomposition,
    literal_gamma_bare_residual_decomposition, actual_bare_quarter_even, neg_sq]

/-- Same-input actual Gamma energy difference, with the literal even
extension u|t|. The original shifted Gamma domain supplies both energies'
actual integrability through the proved domain equivalence. -/
private theorem actual_gamma_literal_even_energy_difference_complete_series
    (c : ℝ) {u : ℝ → ℂ} (hu₁ : Integrable u halfline) (hu₂ : MemLp u 2 halfline)
    (hGamma : Integrable (fun ξ : ℝ =>
      (gammaWeight ξ + c) * ‖unitarySourceFourier (zeroExtension u) ξ‖ ^ 2) volume) :
    Integrable (fun ξ : ℝ =>
      (gammaWeight ξ + c) * ‖unitarySourceFourier (fun t : ℝ => u |t|) ξ‖ ^ 2) volume ∧
    Real.sqrt Real.pi *
      ((∫ ξ : ℝ, (gammaWeight ξ + c) *
        ‖unitarySourceFourier (zeroExtension u) ξ‖ ^ 2) -
      (∫ ξ : ℝ, (gammaWeight ξ + c) *
        ‖unitarySourceFourier (fun t : ℝ => u |t|) ξ‖ ^ 2) / 2) =
      (D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.actualHankel (1 / 4) u).re +
        3 * (∑' n : ℕ, actualResidualLayerCrossValue (5 / 4) ((n : ℝ) + 1 / 4) u) +
        (6 / 5) * ((Complex.digamma (1 / 4)).re - Real.log Real.pi) *
          Complex.normSq (literalSourceLaplace (5 / 4) u) := by
  have hU₁ : Integrable (zeroExtension u) volume :=
    (integrable_indicator_iff measurableSet_Ioi).2 hu₁
  have hU₂ : MemLp (zeroExtension u) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).2 hu₂
  have hWgraph : InActualBareQuarterGraph (zeroExtension u) :=
    (shifted_actual_gamma_graph_equivalence hU₁ hU₂ c).mp hGamma
  have hWEgraph : InActualBareQuarterGraph (actualEvenZeroExtension u) :=
    (actual_bare_quarter_even_zero_domain_and_identity hu₁ hu₂).1.mpr hWgraph
  have hE₁ : Integrable (actualEvenZeroExtension u) volume :=
    hU₁.add ((Measure.measurePreserving_neg volume).integrable_comp_of_integrable hU₁)
  have hE₂ : MemLp (actualEvenZeroExtension u) 2 volume :=
    hU₂.add (hU₂.comp_measurePreserving (Measure.measurePreserving_neg volume))
  have hGE : Integrable (fun ξ : ℝ => (gammaWeight ξ + c) *
      ‖unitarySourceFourier (actualEvenZeroExtension u) ξ‖ ^ 2) volume :=
    (shifted_actual_gamma_graph_equivalence hE₁ hE₂ c).mpr hWEgraph
  let A : ℝ → ℝ := fun ξ => (gammaWeight ξ + c) *
    ‖unitarySourceFourier (zeroExtension u) ξ‖ ^ 2
  let B : ℝ → ℝ := fun ξ => (gammaWeight ξ + c) *
    ‖unitarySourceFourier (zeroExtension u) (-ξ)‖ ^ 2
  let R : ℝ → ℂ := fun ξ => ((gammaWeight ξ + c : ℝ) : ℂ) * actualSourceSpectralCross u ξ
  have hA : Integrable A volume := hGamma
  have hB : Integrable B volume := by
    simpa only [Function.comp_def, A, B, literal_shifted_gamma_even] using
      (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hA
  obtain ⟨hR, hRvalue⟩ := actual_gamma_reflected_cross_complete_series c hu₁ hu₂ hGamma
  have hReflect : (∫ ξ, B ξ) = ∫ ξ, A ξ := by
    simpa only [A, B, literal_shifted_gamma_even] using integral_neg_eq_self A volume
  have hPoint (z w : ℂ) : ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 +
      2 * ((starRingEnd ℂ) z * w).re := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_add,
      Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hExpansion : (∫ ξ : ℝ, (gammaWeight ξ + c) *
      ‖unitarySourceFourier (actualEvenZeroExtension u) ξ‖ ^ 2) =
        2 * (∫ ξ, A ξ) + 2 * (∫ ξ, R ξ).re := by
    calc
      _ = ∫ ξ : ℝ, (A ξ + B ξ) + 2 * (R ξ).re := by
        apply integral_congr_ae
        exact Eventually.of_forall fun ξ => by
          dsimp only
          rw [actual_even_zero_fourier hu₁, hPoint]
          let z := unitarySourceFourier (zeroExtension u) ξ
          let w := unitarySourceFourier (zeroExtension u) (-ξ)
          change (gammaWeight ξ + c) * (‖z‖ ^ 2 + ‖w‖ ^ 2 +
              2 * ((starRingEnd ℂ) z * w).re) =
            (gammaWeight ξ + c) * ‖z‖ ^ 2 + (gammaWeight ξ + c) * ‖w‖ ^ 2 +
              2 * (((gammaWeight ξ + c : ℝ) : ℂ) * ((starRingEnd ℂ) z * w)).re
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            zero_mul, sub_zero]
          ring
      _ = (∫ ξ, A ξ) + (∫ ξ, B ξ) + 2 * (∫ ξ, R ξ).re := by
        have hSum : Integrable (fun ξ => A ξ + B ξ) volume := hA.add hB
        have hTerm : Integrable (fun ξ => 2 * (R ξ).re) volume := hR.re.const_mul 2
        rw [integral_add hSum hTerm, integral_add hA hB, integral_const_mul]
        have hre : (∫ ξ : ℝ, (R ξ).re) = (∫ ξ : ℝ, R ξ).re := integral_re hR
        rw [hre]
      _ = _ := by rw [hReflect]; ring
  constructor
  · simpa only [actual_literal_even_fourier] using hGE
  · simp_rw [actual_literal_even_fourier]
    change Real.sqrt Real.pi * ((∫ ξ, A ξ) - _ / 2) = _
    rw [hExpansion]
    calc
      _ = Real.sqrt Real.pi * (-(∫ ξ, R ξ).re) := by ring
      _ = _ := hRvalue


/- Actual coefficient compression after the paid cross identity. -/
private theorem positive_real_avoids_nonpositive_poles {z : ℝ} (hz : 0 < z)
    (m : ℕ) : (z : ℂ) ≠ -(m : ℂ) := by
  intro hm
  have hr := congrArg Complex.re hm
  simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hr
  have hn : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

private theorem real_digamma_gap_hasSum {z : ℝ} (hz : 0 < z)
    (hm : (z : ℂ) ∈ Complex.integerComplement) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1 + z))
      ((Complex.digamma ((z : ℂ) + 1)).re + Real.eulerMascheroniConstant) := by
  have h := Complex.hasSum_re (Zeta23.DigammaSeries.hasSum_digamma_series hm)
  have hRow (n : ℕ) :
      ((1 : ℂ) / ((n : ℂ) + 1) - 1 / ((z : ℂ) + n + 1)).re =
        1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1 + z) := by
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      show ((z : ℂ) + n + 1) = (((n : ℝ) + 1 + z : ℝ) : ℂ) by push_cast; ring]
    simp only [Complex.sub_re, Complex.div_ofReal_re, Complex.one_re]
  have hLimit : (Complex.digamma (z : ℂ) + (Real.eulerMascheroniConstant : ℂ) +
      1 / (z : ℂ)).re =
        (Complex.digamma ((z : ℂ) + 1)).re + Real.eulerMascheroniConstant := by
    rw [Complex.digamma_apply_add_one _ (positive_real_avoids_nonpositive_poles hz)]
    simp only [Complex.add_re, Complex.ofReal_re, one_div]
    ring
  simpa only [hRow, hLimit] using h

private def gammaTailScalar (n : ℕ) : ℝ :=
  (5 / 4) / (((n : ℝ) + 9 / 4) *
    (((n : ℝ) + 9 / 4) ^ 2 - (5 / 4 : ℝ) ^ 2))

private theorem gamma_tail_scalar_hasSum : HasSum gammaTailScalar
    ((4 / 5) * ((Complex.digamma (1 / 4)).re - (Complex.digamma 1).re +
      Real.log 2 + 49 / 15)) := by
  have hquarter : (1 / 4 : ℂ) ∈ Complex.integerComplement := by
    convert Zeta23.MuFields.abscissa_mem (a := (1 / 4 : ℝ))
      (by norm_num) (by norm_num) 0 using 1 <;> norm_num
  have hhalf : (1 / 2 : ℂ) ∈ Complex.integerComplement := by
    convert Zeta23.MuFields.abscissa_mem (a := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) 0 using 1 <;> norm_num
  have h54 : (5 / 4 : ℂ) ∈ Complex.integerComplement := by
    convert (Complex.add_intCast_mem_integerComplement 1).2 hquarter using 1 <;> norm_num
  have h52 : (5 / 2 : ℂ) ∈ Complex.integerComplement := by
    convert (Complex.add_intCast_mem_integerComplement 2).2 hhalf using 1 <;> norm_num
  have hA := real_digamma_gap_hasSum (z := (5 / 4 : ℝ)) (by norm_num)
    (by convert h54 using 1 <;> norm_num)
  have hB := real_digamma_gap_hasSum (z := (5 / 2 : ℝ)) (by norm_num)
    (by convert h52 using 1 <;> norm_num)
  have h := ((hA.mul_left 2).sub hB).mul_left (2 / 5 : ℝ)
  have hRow (n : ℕ) : gammaTailScalar n =
      (2 / 5 : ℝ) *
        (2 * (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1 + 5 / 4)) -
          (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1 + 5 / 2))) := by
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 1 + 5 / 4 ≠ 0 := by positivity
    have h3 : (n : ℝ) + 1 + 5 / 2 ≠ 0 := by positivity
    have h4 : (n : ℝ) + 9 / 4 ≠ 0 := by positivity
    have hd : ((n : ℝ) + 9 / 4) ^ 2 - (5 / 4 : ℝ) ^ 2 ≠ 0 := by
      have hp : 0 < ((n : ℝ) + 9 / 4) ^ 2 - (5 / 4 : ℝ) ^ 2 := by
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      exact hp.ne'
    have hfactor : ((n : ℝ) + 9 / 4) ^ 2 - (5 / 4 : ℝ) ^ 2 =
        ((n : ℝ) + 1) * ((n : ℝ) + 7 / 2) := by ring
    unfold gammaTailScalar
    rw [hfactor]
    field_simp (disch := positivity)
    <;> ring
  have hQ := congrArg Complex.re
    (Complex.digamma_apply_add_nat
      (s := ((1 / 4 : ℝ) : ℂ))
      (positive_real_avoids_nonpositive_poles (z := (1 / 4 : ℝ)) (by norm_num)) 2)
  have hH := congrArg Complex.re
    (Complex.digamma_apply_add_nat
      (s := ((1 / 2 : ℝ) : ℂ))
      (positive_real_avoids_nonpositive_poles (z := (1 / 2 : ℝ)) (by norm_num)) 3)
  have hHalfValue : (Complex.digamma (1 / 2)).re =
      (Complex.digamma 1).re - 2 * Real.log 2 := by
    rw [Complex.digamma_one_half, Complex.digamma_one]
    have hlog : (Complex.log (2 : ℂ)).re = Real.log 2 := by
      exact Complex.log_ofReal_re (2 : ℝ)
    norm_num [Complex.sub_re, Complex.neg_re, Complex.mul_re, hlog]
    <;> ring
  have hQValue : (Complex.digamma (9 / 4)).re =
      (Complex.digamma (1 / 4)).re + 24 / 5 := by
    norm_num [Finset.sum_range_succ] at hQ ⊢
    exact hQ
  have hHValue : (Complex.digamma (7 / 2)).re =
      (Complex.digamma (1 / 2)).re + 46 / 15 := by
    norm_num [Finset.sum_range_succ] at hH ⊢
    exact hH
  have hOne : (Complex.digamma 1).re = -Real.eulerMascheroniConstant := by
    rw [Complex.digamma_one]
    simp only [Complex.neg_re, Complex.ofReal_re]
  convert h using 1
  · ext n
    exact hRow n
  · norm_num only [show ((5 / 4 : ℝ) : ℂ) + 1 = 9 / 4 by norm_num,
      show ((5 / 2 : ℝ) : ℂ) + 1 = 7 / 2 by norm_num]
    rw [hQValue, hHValue, hHalfValue]
    linarith [hOne]

private theorem actual_gamma_resonant_coefficient_compression :
    (162 / 25 : ℝ) - (3 / 2) * (∑' n : ℕ, gammaTailScalar n) +
        (6 / 5) * ((Complex.digamma (1 / 4)).re - Real.log Real.pi) =
      (64 / 25 : ℝ) + (6 / 5) * ((Complex.digamma 1).re - Real.log (2 * Real.pi)) := by
  rw [gamma_tail_scalar_hasSum.tsum_eq,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  ring

def actualGammaPositiveTailTerm (u : ℝ → ℂ) (n : ℕ) : ℝ :=
  (1 + (3 / 2 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 7 / 2))) *
    Complex.normSq (literalSourceLaplace ((n : ℝ) + 9 / 4) u)

private theorem actual_gamma_actual_series_compression
    {u : ℝ → ℂ} (hu₁ : Integrable u halfline) (hu₂ : MemLp u 2 halfline) :
    Summable (actualGammaPositiveTailTerm u) ∧
    (D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.actualHankel (1 / 4) u).re +
        3 * (∑' n : ℕ, actualResidualLayerCrossValue (5 / 4) ((n : ℝ) + 1 / 4) u) +
        (6 / 5) * ((Complex.digamma (1 / 4)).re - Real.log Real.pi) *
          Complex.normSq (literalSourceLaplace (5 / 4) u) =
      (∑' n : ℕ, actualGammaPositiveTailTerm u n) +
        ((64 / 25 : ℝ) + (6 / 5) * ((Complex.digamma 1).re - Real.log (2 * Real.pi))) *
          Complex.normSq (literalSourceLaplace (5 / 4) u) -
        (6 / 5) * ((starRingEnd ℂ) (literalSourceLaplace (5 / 4) u) *
          literalSourceFirstLaplaceMoment (5 / 4) u).re := by
  let L : ℕ → ℝ := fun n => Complex.normSq (literalSourceLaplace ((n : ℝ) + 1 / 4) u)
  let V : ℕ → ℝ := fun n => actualResidualLayerCrossValue (5 / 4) ((n : ℝ) + 1 / 4) u
  let M : ℝ := ((starRingEnd ℂ) (literalSourceLaplace (5 / 4) u) *
    literalSourceFirstLaplaceMoment (5 / 4) u).re
  obtain ⟨_, _, _, _, hL₀, hH₀, _, _, _⟩ :=
    D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.positive_hankel_actual_l2_domain_quarter_sharp
      (k := (1 / 4 : ℝ)) (by norm_num) u hu₂
  have hL : Summable L := by
    simpa only [L, literalSourceLaplace,
      D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.literalLaplace,
      add_comm (1 / 4 : ℝ)] using hL₀
  have hH : (D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.actualHankel (1 / 4) u).re =
      ∑' n : ℕ, L n := by
    rw [hH₀, ← Complex.ofReal_tsum, Complex.ofReal_re]
    apply tsum_congr
    intro n
    simp only [L, literalSourceLaplace,
      D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.literalLaplace,
      add_comm (1 / 4 : ℝ)]
  have hV : Summable V :=
    (actual_residual_reflected_cross_complete_series (a := (5 / 4 : ℝ))
      (by norm_num) hu₁).2.summable
  have hLt : Summable (fun n : ℕ => L (n + 2)) := (summable_nat_add_iff 2).2 hL
  have hVt : Summable (fun n : ℕ => V (n + 2)) := (summable_nat_add_iff 2).2 hV
  have hT := gamma_tail_scalar_hasSum.summable
  have hL1 : L 1 = Complex.normSq (literalSourceLaplace (5 / 4) u) := by norm_num [L]
  have hV0 : V 0 = -(L 0) / 3 + (5 / 3 : ℝ) * L 1 := by
    norm_num [V, L, actualResidualLayerCrossValue]
    <;> ring
  have hV1 : V 1 = (4 / 25 : ℝ) * L 1 - (2 / 5 : ℝ) * M := by
    norm_num [V, L, M, actualResidualLayerCrossValue]
    <;> ring
  have hTailRow (n : ℕ) : actualGammaPositiveTailTerm u n =
      L (n + 2) + 3 * V (n + 2) + (3 / 2 : ℝ) * gammaTailScalar n * L 1 := by
    have hca : ((n + 2 : ℕ) : ℝ) + 1 / 4 ≠ (5 / 4 : ℝ) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hc : (n : ℝ) + 9 / 4 ≠ 0 := by positivity
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 7 / 2 ≠ 0 := by positivity
    have hd : ((n : ℝ) + 9 / 4) ^ 2 - (5 / 4 : ℝ) ^ 2 ≠ 0 := by
      have hp : 0 < ((n : ℝ) + 9 / 4) ^ 2 - (5 / 4 : ℝ) ^ 2 := by
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      exact hp.ne'
    dsimp [V]
    rw [actualResidualLayerCrossValue, if_neg hca]
    dsimp [actualGammaPositiveTailTerm, L, gammaTailScalar]
    push_cast
    norm_num only [show (1 : ℝ) + 1 / 4 = 5 / 4 by norm_num]
    have hShift : (n : ℝ) + 2 + 1 / 4 = (n : ℝ) + 9 / 4 := by ring
    simp_rw [hShift]
    have hfactor : ((n : ℝ) + 9 / 4) ^ 2 - (25 / 16 : ℝ) =
        ((n : ℝ) + 1) * ((n : ℝ) + 7 / 2) := by ring
    rw [hfactor]
    field_simp (disch := positivity)
    <;> ring
  have h3V := Summable.mul_left (3 : ℝ) hVt
  have h3T := Summable.mul_right (L 1) (Summable.mul_left (3 / 2 : ℝ) hT)
  have hP : Summable (actualGammaPositiveTailTerm u) :=
    ((hLt.add h3V).add h3T).congr (fun n => (hTailRow n).symm)
  have hPsum : (∑' n : ℕ, actualGammaPositiveTailTerm u n) =
      (∑' n : ℕ, L (n + 2)) + 3 * (∑' n : ℕ, V (n + 2)) +
        (3 / 2 : ℝ) * (∑' n : ℕ, gammaTailScalar n) * L 1 := by
    rw [tsum_congr hTailRow, (hLt.add h3V).tsum_add h3T, hLt.tsum_add h3V]
    simp_rw [tsum_mul_left, tsum_mul_right]
    rw [tsum_mul_left]
  have hLsplit := (hL.sum_add_tsum_nat_add 2).symm
  have hVsplit := (hV.sum_add_tsum_nat_add 2).symm
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hLsplit hVsplit
  refine ⟨hP, ?_⟩
  rw [hH]
  change (∑' n : ℕ, L n) + 3 * (∑' n : ℕ, V n) +
    (6 / 5) * ((Complex.digamma (1 / 4)).re - Real.log Real.pi) * _ = _
  rw [hLsplit, hVsplit, hV0, hV1, hPsum, ← hL1,
    ← actual_gamma_resonant_coefficient_compression]
  change _ = _ - (6 / 5 : ℝ) * M
  ring

/-- Final same-input Gamma difference with literal even extension, actual
Gamma graph and complete positive tail. The 1/4 pole cancels, while the
5/4 mixed moment remains. This is a source proof candidate, not a native
verification or RH-positivity claim. -/
theorem actual_gamma_literal_even_difference_positive_tail_and_resonance
    (c : ℝ) {u : ℝ → ℂ} (hu₁ : Integrable u halfline) (hu₂ : MemLp u 2 halfline)
    (hGamma : Integrable (fun ξ : ℝ =>
      (gammaWeight ξ + c) * ‖unitarySourceFourier (zeroExtension u) ξ‖ ^ 2) volume) :
    Summable (actualGammaPositiveTailTerm u) ∧
    Integrable (fun ξ : ℝ =>
      (gammaWeight ξ + c) * ‖unitarySourceFourier (fun t : ℝ => u |t|) ξ‖ ^ 2) volume ∧
    Real.sqrt Real.pi *
      ((∫ ξ : ℝ, (gammaWeight ξ + c) *
        ‖unitarySourceFourier (zeroExtension u) ξ‖ ^ 2) -
      (∫ ξ : ℝ, (gammaWeight ξ + c) *
        ‖unitarySourceFourier (fun t : ℝ => u |t|) ξ‖ ^ 2) / 2) =
      (∑' n : ℕ, actualGammaPositiveTailTerm u n) +
        ((64 / 25 : ℝ) + (6 / 5) * ((Complex.digamma 1).re - Real.log (2 * Real.pi))) *
          Complex.normSq (literalSourceLaplace (5 / 4) u) -
        (6 / 5) * ((starRingEnd ℂ) (literalSourceLaplace (5 / 4) u) *
          literalSourceFirstLaplaceMoment (5 / 4) u).re := by
  obtain ⟨hEven, hActual⟩ :=
    actual_gamma_literal_even_energy_difference_complete_series c hu₁ hu₂ hGamma
  obtain ⟨hTail, hCompressed⟩ := actual_gamma_actual_series_compression hu₁ hu₂
  exact ⟨hTail, hEven, hActual.trans hCompressed⟩

end D5.S3.Weil.ZetaGamma.FormCore.SourceActualGammaCross
