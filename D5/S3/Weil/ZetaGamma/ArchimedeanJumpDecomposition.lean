/- GID: D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Decompose the completed-zeta Archimedean term into continuous translation energy. -/

import D5.S3.Weil.PrimePoleTerms
import D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import D5.S3.Weil.ZetaGamma.GammaMu
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Archimedean jump decomposition

The jump density and translation energy are constructed independently of the
Archimedean term.  The proof derives the missing Levy representation from the
frozen digamma partial-fraction series and then applies Fourier inversion to a
convolution square.
-/

noncomputable section

open MeasureTheory Set
open D5.S3.Weil.Convention
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.PrimePoleTerms
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open scoped ComplexConjugate FourierTransform ENNReal

namespace D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition

/-- The continuous positive jump density of the completed-zeta Gamma factor. -/
def archimedeanJumpDensity (x : ℝ) : ℝ :=
  Real.exp (-x / 2) / (1 - Real.exp (-2 * x))

/-- Squared `L2` mass on the source real-line carrier. -/
def l2Mass (f : WeilTestFunction) : ℝ :=
  ∫ y : ℝ, Complex.normSq (f y)

/-- Squared displacement by the source translation `U_x f(y) = f(y-x)`. -/
def translationEnergy (f : WeilTestFunction) (x : ℝ) : ℝ :=
  ∫ y : ℝ, Complex.normSq (f y - f (y - x))

/-- The continuous Archimedean jump energy. -/
def archimedeanJumpEnergy (f : WeilTestFunction) : ℝ :=
  ∫ x : ℝ in Ioi 0, archimedeanJumpDensity x * translationEnergy f x

/-- The zero-frequency value of the canonical Archimedean multiplier. -/
def archimedeanConstant : ℝ :=
  (Complex.digamma (1 / 4)).re - Real.log Real.pi

private theorem jump_density_nonnegative {x : ℝ} (hx : 0 < x) :
    0 ≤ archimedeanJumpDensity x := by
  unfold archimedeanJumpDensity
  have hexp : Real.exp (-2 * x) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  exact div_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hexp.le)

private theorem translation_energy_nonnegative (f : WeilTestFunction) (x : ℝ) :
    0 ≤ translationEnergy f x := by
  unfold translationEnergy
  exact integral_nonneg fun _ => Complex.normSq_nonneg _

private theorem jump_energy_nonnegative (f : WeilTestFunction) :
    0 ≤ archimedeanJumpEnergy f := by
  unfold archimedeanJumpEnergy
  refine integral_nonneg_of_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  exact mul_nonneg (jump_density_nonnegative hx) (translation_energy_nonnegative f x)

private theorem integral_exp_neg_mul_cos {c t : ℝ} (hc : 0 < c) :
    (∫ x : ℝ in Ioi 0, Real.exp (-c * x) * Real.cos (t * x)) =
      c / (c ^ 2 + t ^ 2) := by
  have hInt : IntegrableOn
      (fun x : ℝ => Complex.exp
        ((((-c : ℝ) : ℂ) + Complex.I * (t : ℂ)) * (x : ℂ))) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (by simp; linarith) 0
  have hi := integral_exp_mul_complex_Ioi
    (a := ((-c : ℝ) : ℂ) + Complex.I * (t : ℂ)) (by simp; linarith) 0
  calc
    (∫ x : ℝ in Ioi 0, Real.exp (-c * x) * Real.cos (t * x)) =
        ∫ x : ℝ in Ioi 0,
          (Complex.exp ((((-c : ℝ) : ℂ) + Complex.I * (t : ℂ)) * (x : ℂ))).re := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Complex.exp_re]
      congr 2 <;> simp
    _ = (∫ x : ℝ in Ioi 0,
        Complex.exp ((((-c : ℝ) : ℂ) + Complex.I * (t : ℂ)) * (x : ℂ))).re := by
      exact integral_re hInt
    _ = (-Complex.exp
        ((((-c : ℝ) : ℂ) + Complex.I * (t : ℂ)) * (0 : ℂ)) /
          (((-c : ℝ) : ℂ) + Complex.I * (t : ℂ))).re := congrArg Complex.re hi
    _ = c / (c ^ 2 + t ^ 2) := by
      norm_num [Complex.div_re, Complex.normSq_apply]
      ring

private theorem integral_exp_neg_mul_one_sub_cos {c t : ℝ} (hc : 0 < c) :
    (∫ x : ℝ in Ioi 0,
      2 * Real.exp (-c * x) * (1 - Real.cos (t * x))) =
        2 * (1 / c - c / (c ^ 2 + t ^ 2)) := by
  have hExp : IntegrableOn (fun x : ℝ => Real.exp (-c * x)) (Ioi 0) := by
    simpa only [neg_mul] using integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0
  have hCos : IntegrableOn
      (fun x : ℝ => Real.exp (-c * x) * Real.cos (t * x)) (Ioi 0) := by
    refine hExp.mul_bdd (c := 1) (by fun_prop) ?_
    filter_upwards with x
    simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (t * x)
  rw [show (fun x : ℝ => 2 * Real.exp (-c * x) * (1 - Real.cos (t * x))) =
      fun x => 2 * (Real.exp (-c * x) -
        Real.exp (-c * x) * Real.cos (t * x)) by
    funext x
    ring]
  rw [integral_const_mul, integral_sub hExp hCos,
    integral_exp_neg_mul_cos hc]
  have hbase : (∫ x : ℝ in Ioi 0, Real.exp (-c * x)) = 1 / c := by
    calc
      _ = -Real.exp ((-c) * 0) / (-c) := by
        simpa only [neg_mul] using
          integral_exp_mul_Ioi (a := -c) (by linarith) 0
      _ = 1 / c := by
        norm_num
  rw [hbase]

private def digammaIncrement (t : ℝ) (n : ℕ) : ℝ :=
  let c : ℝ := n + 1 / 4
  1 / c - c / (c ^ 2 + (t / 2) ^ 2)

private theorem summable_digamma_increment (t : ℝ) :
    Summable (digammaIncrement t) := by
  have ht := Zeta23.MuFields.summable_re_terms
    (a := 1 / 4) (by norm_num) (by norm_num) (t / 2)
  have h0 := Zeta23.MuFields.summable_re_terms
    (a := 1 / 4) (by norm_num) (by norm_num) 0
  have htail := ht.sub h0
  have heq :
      (fun n : ℕ => digammaIncrement t (n + 1)) =
        fun n : ℕ =>
          (1 / ((n : ℝ) + 1) -
              ((n : ℝ) + 1 + 1 / 4) /
                (((n : ℝ) + 1 + 1 / 4) ^ 2 + (t / 2) ^ 2)) -
            (1 / ((n : ℝ) + 1) -
              ((n : ℝ) + 1 + 1 / 4) /
                (((n : ℝ) + 1 + 1 / 4) ^ 2 + (0 : ℝ) ^ 2)) := by
    funext n
    unfold digammaIncrement
    have hc : (0 : ℝ) < (n : ℝ) + 1 + 1 / 4 := by positivity
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp [hc.ne']
    ring
  rw [← heq] at htail
  exact (summable_nat_add_iff 1).mp htail

private theorem digamma_increment_sum (t : ℝ) :
    (Complex.digamma
        ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
        (Complex.digamma (1 / 4)).re =
      ∑' n : ℕ, digammaIncrement t n := by
  have ht := Zeta23.MuFields.re_digamma_vertical
    (a := 1 / 4) (by norm_num) (by norm_num) (t / 2)
  have h0 := Zeta23.MuFields.re_digamma_vertical
    (a := 1 / 4) (by norm_num) (by norm_num) 0
  norm_num at ht h0 ⊢
  have htail :
      (∑' n : ℕ,
        (1 / ((n : ℝ) + 1) -
          ((n : ℝ) + 1 + 1 / 4) /
            (((n : ℝ) + 1 + 1 / 4) ^ 2 + (t / 2) ^ 2))) -
        ∑' n : ℕ,
          (1 / ((n : ℝ) + 1) -
            ((n : ℝ) + 1 + 1 / 4) /
              (((n : ℝ) + 1 + 1 / 4) ^ 2 + (0 : ℝ) ^ 2)) =
        ∑' n : ℕ, digammaIncrement t (n + 1) := by
    rw [← (Zeta23.MuFields.summable_re_terms
      (a := 1 / 4) (by norm_num) (by norm_num) (t / 2)).tsum_sub
        (Zeta23.MuFields.summable_re_terms
          (a := 1 / 4) (by norm_num) (by norm_num) 0)]
    apply tsum_congr
    intro n
    unfold digammaIncrement
    have hc : (0 : ℝ) < (n : ℝ) + 1 + 1 / 4 := by positivity
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp [hc.ne']
    ring
  calc
    (Complex.digamma (1 / 4 + Complex.I * (t / 2))).re -
        (Complex.digamma (1 / 4)).re =
      digammaIncrement t 0 +
        ((∑' n : ℕ,
          (1 / ((n : ℝ) + 1) -
            ((n : ℝ) + 1 + 1 / 4) /
              (((n : ℝ) + 1 + 1 / 4) ^ 2 + (t / 2) ^ 2))) -
          ∑' n : ℕ,
            (1 / ((n : ℝ) + 1) -
              ((n : ℝ) + 1 + 1 / 4) /
                (((n : ℝ) + 1 + 1 / 4) ^ 2 + (0 : ℝ) ^ 2))) := by
      rw [ht, h0]
      unfold digammaIncrement
      norm_num
      ring
    _ = digammaIncrement t 0 +
        ∑' n : ℕ, digammaIncrement t (n + 1) := by rw [htail]
    _ = ∑' n : ℕ, digammaIncrement t n := by
      rw [← (summable_digamma_increment t).sum_add_tsum_nat_add 1]
      simp

private theorem jump_density_eq_tsum {x : ℝ} (hx : 0 < x) :
    archimedeanJumpDensity x =
      ∑' n : ℕ, Real.exp (-((2 : ℝ) * n + 1 / 2) * x) := by
  have hr0 : 0 ≤ Real.exp (-2 * x) := (Real.exp_pos _).le
  have hr1 : Real.exp (-2 * x) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  calc
    archimedeanJumpDensity x =
        Real.exp (-x / 2) * (1 - Real.exp (-2 * x))⁻¹ := by
      rw [archimedeanJumpDensity, div_eq_mul_inv]
    _ = Real.exp (-x / 2) * ∑' n : ℕ, (Real.exp (-2 * x)) ^ n := by
      rw [tsum_geometric_of_lt_one hr0 hr1]
    _ = ∑' n : ℕ, Real.exp (-x / 2) * (Real.exp (-2 * x)) ^ n := by
      rw [tsum_mul_left]
    _ = ∑' n : ℕ, Real.exp (-((2 : ℝ) * n + 1 / 2) * x) := by
      apply tsum_congr
      intro n
      rw [← Real.exp_nat_mul]
      rw [← Real.exp_add]
      congr 1
      ring

private def levyLayer (t : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  2 * Real.exp (-((2 : ℝ) * n + 1 / 2) * x) *
    (1 - Real.cos (t * x))

private theorem levy_layer_nonnegative (t : ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ levyLayer t n x := by
  unfold levyLayer
  exact mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
    (sub_nonneg.mpr (Real.cos_le_one _))

private theorem levy_layer_integrableOn (t : ℝ) (n : ℕ) :
    IntegrableOn (levyLayer t n) (Ioi 0) := by
  let c : ℝ := (2 : ℝ) * n + 1 / 2
  have hc : 0 < c := by positivity
  have hExp : IntegrableOn (fun x : ℝ => Real.exp (-c * x)) (Ioi 0) := by
    simpa only [neg_mul] using
      integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0
  have hOsc : IntegrableOn
      (fun x : ℝ => Real.exp (-c * x) * (1 - Real.cos (t * x))) (Ioi 0) := by
    refine hExp.mul_bdd (c := 2) (by fun_prop) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    have hnonneg : 0 ≤ 1 - Real.cos (t * x) := sub_nonneg.mpr (Real.cos_le_one _)
    rw [abs_of_nonneg hnonneg]
    linarith [Real.neg_one_le_cos (t * x)]
  refine (hOsc.const_mul 2).congr ?_
  filter_upwards with x
  unfold levyLayer
  dsimp [c]
  ring_nf

private theorem integral_levy_layer (t : ℝ) (n : ℕ) :
    (∫ x : ℝ in Ioi 0, levyLayer t n x) =
      digammaIncrement t n := by
  let c : ℝ := (2 : ℝ) * n + 1 / 2
  have hc : 0 < c := by positivity
  rw [show levyLayer t n = fun x : ℝ =>
      2 * Real.exp (-c * x) * (1 - Real.cos (t * x)) by rfl,
    integral_exp_neg_mul_one_sub_cos hc]
  unfold digammaIncrement
  dsimp [c]
  have hn : (0 : ℝ) < (n : ℝ) + 1 / 4 := by positivity
  field_simp [hn.ne']
  ring

private theorem levy_integral_eq_digamma_increment (t : ℝ) :
    (∫ x : ℝ in Ioi 0,
      2 * archimedeanJumpDensity x * (1 - Real.cos (t * x))) =
      (Complex.digamma
        ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
        (Complex.digamma (1 / 4)).re := by
  have hSumNorm : Summable
      (fun n : ℕ => ∫ x : ℝ in Ioi 0, ‖levyLayer t n x‖) := by
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (levy_layer_nonnegative t _ _), integral_levy_layer] using
      summable_digamma_increment t
  rw [digamma_increment_sum]
  calc
    (∫ x : ℝ in Ioi 0,
        2 * archimedeanJumpDensity x * (1 - Real.cos (t * x))) =
        ∫ x : ℝ in Ioi 0, ∑' n : ℕ, levyLayer t n x := by
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      rw [jump_density_eq_tsum hx]
      rw [← tsum_mul_left, ← tsum_mul_right]
      apply tsum_congr
      intro n
      unfold levyLayer
      ring
    _ = ∑' n : ℕ, ∫ x : ℝ in Ioi 0, levyLayer t n x :=
      (integral_tsum_of_summable_integral_norm
        (fun n => levy_layer_integrableOn t n) hSumNorm).symm
    _ = ∑' n : ℕ, digammaIncrement t n := by
      apply tsum_congr
      exact integral_levy_layer t

private theorem summable_levy_layer (t : ℝ) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => levyLayer t n x) := by
  have hr0 : 0 ≤ Real.exp (-2 * x) := (Real.exp_pos _).le
  have hr1 : Real.exp (-2 * x) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hGeom := (summable_geometric_of_lt_one hr0 hr1).mul_left
    (2 * Real.exp (-x / 2) * (1 - Real.cos (t * x)))
  refine hGeom.congr fun n => ?_
  unfold levyLayer
  rw [← Real.exp_nat_mul]
  have hExp : Real.exp ((n : ℝ) * (-2 * x)) * Real.exp (-x / 2) =
      Real.exp (-((2 : ℝ) * n + 1 / 2) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← hExp]
  ring

private theorem levy_kernel_integrableOn (t : ℝ) :
    IntegrableOn
      (fun x : ℝ =>
        2 * archimedeanJumpDensity x * (1 - Real.cos (t * x)))
      (Ioi 0) := by
  have hMeas : AEStronglyMeasurable
      (fun x : ℝ =>
        2 * archimedeanJumpDensity x * (1 - Real.cos (t * x)))
      (volume.restrict (Ioi 0)) := by
    unfold archimedeanJumpDensity
    fun_prop
  have hNonneg : ∀ᵐ x ∂(volume.restrict (Ioi 0)),
      0 ≤ 2 * archimedeanJumpDensity x * (1 - Real.cos (t * x)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact mul_nonneg (mul_nonneg (by norm_num) (jump_density_nonnegative hx))
      (sub_nonneg.mpr (Real.cos_le_one _))
  refine ⟨hMeas, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hNonneg]
  calc
    (∫⁻ x : ℝ in Ioi 0,
        ENNReal.ofReal
          (2 * archimedeanJumpDensity x * (1 - Real.cos (t * x)))) =
        ∫⁻ x : ℝ in Ioi 0,
          ∑' n : ℕ, ENNReal.ofReal (levyLayer t n x) := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hEq :
          2 * archimedeanJumpDensity x * (1 - Real.cos (t * x)) =
            ∑' n : ℕ, levyLayer t n x := by
        rw [jump_density_eq_tsum hx]
        rw [← tsum_mul_left, ← tsum_mul_right]
        apply tsum_congr
        intro n
        unfold levyLayer
        ring
      rw [hEq]
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun n => levy_layer_nonnegative t n x) (summable_levy_layer t hx)
    _ = ∑' n : ℕ,
        ∫⁻ x : ℝ in Ioi 0, ENNReal.ofReal (levyLayer t n x) := by
      rw [lintegral_tsum]
      intro n
      exact (ENNReal.measurable_ofReal.comp (by
        unfold levyLayer
        fun_prop)).aemeasurable
    _ < ∞ := by
      calc
        (∑' n : ℕ,
            ∫⁻ x : ℝ in Ioi 0, ENNReal.ofReal (levyLayer t n x)) =
            ∑' n : ℕ, ENNReal.ofReal (digammaIncrement t n) := by
          apply tsum_congr
          intro n
          calc
            (∫⁻ x : ℝ in Ioi 0, ENNReal.ofReal (levyLayer t n x)) =
                ENNReal.ofReal (∫ x : ℝ in Ioi 0, levyLayer t n x) :=
              (ofReal_integral_eq_lintegral_ofReal
                (levy_layer_integrableOn t n)
                (Filter.Eventually.of_forall fun x =>
                  levy_layer_nonnegative t n x)).symm
            _ = ENNReal.ofReal (digammaIncrement t n) := by
              rw [integral_levy_layer]
        _ < ∞ := (summable_digamma_increment t).tsum_ofReal_lt_top

private theorem integrable_normSq (f : WeilTestFunction) :
    Integrable (fun y : ℝ => Complex.normSq (f y)) := by
  exact (Complex.continuous_normSq.comp f.continuous).integrable_of_hasCompactSupport
    (f.hasCompactSupport.comp_left (by simp))

private theorem integrable_correlation (f : WeilTestFunction) (x : ℝ) :
    Integrable (fun y : ℝ => f y * conj (f (y - x))) := by
  apply Continuous.integrable_of_hasCompactSupport
  · have hf : Continuous (f : ℝ → ℂ) := f.continuous
    fun_prop
  · exact f.hasCompactSupport.mul_right

private theorem convolution_square_re (f : WeilTestFunction) (x : ℝ) :
    (convolutionSquare f x).re =
      ∫ y : ℝ, (f y * conj (f (y - x))).re := by
  rw [convolutionSquare_apply]
  exact (integral_re (integrable_correlation f x)).symm

private theorem convolution_square_zero_re (f : WeilTestFunction) :
    (convolutionSquare f 0).re = l2Mass f := by
  rw [convolution_square_re, l2Mass]
  apply integral_congr_ae
  filter_upwards with y
  simp [Complex.mul_conj]

private theorem translation_energy_eq_correlation (f : WeilTestFunction) (x : ℝ) :
    translationEnergy f x =
      2 * l2Mass f - 2 * (convolutionSquare f x).re := by
  have hNorm := integrable_normSq f
  have hShift : Integrable (fun y : ℝ => Complex.normSq (f (y - x))) := by
    simpa using hNorm.comp_sub_right x
  have hCorrRe := (integrable_correlation f x).re.const_mul 2
  rw [translationEnergy]
  simp_rw [Complex.normSq_sub]
  calc
    (∫ y : ℝ, Complex.normSq (f y) + Complex.normSq (f (y - x)) -
        2 * (f y * conj (f (y - x))).re) =
        (∫ y : ℝ, Complex.normSq (f y) + Complex.normSq (f (y - x))) -
          ∫ y : ℝ, 2 * (f y * conj (f (y - x))).re :=
      integral_sub (hNorm.add hShift) hCorrRe
    _ = ((∫ y : ℝ, Complex.normSq (f y)) +
          ∫ y : ℝ, Complex.normSq (f (y - x))) -
          2 * ∫ y : ℝ, (f y * conj (f (y - x))).re := by
      rw [integral_add hNorm hShift, integral_const_mul]
    _ = 2 * l2Mass f - 2 * (convolutionSquare f x).re := by
      rw [integral_sub_right_eq_self (fun y : ℝ => Complex.normSq (f y)) x]
      rw [← convolution_square_re]
      unfold l2Mass
      ring

private theorem convolution_square_fourier_cos (f : WeilTestFunction) (x : ℝ) :
    2 * (convolutionSquare f x).re =
      (1 / Real.pi) * ∫ t : ℝ,
        Complex.normSq (fourierLaplace f t) * Real.cos (t * x) := by
  let k : WeilTestFunction := convolutionSquare f
  have hkFourier : Integrable (𝓕 (k : ℝ → ℂ)) :=
    Zeta23.EF.integrable_fourier_of_contDiff_two
      (k.contDiff.of_le (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr le_top))
      k.hasCompactSupport
  have h := Zeta23.EF.k_add_k_neg k.continuous k.integrable hkFourier x
  have hRe := congrArg Complex.re h
  rw [k.even] at hRe
  simp_rw [paperFT_eq_fourierLaplace, show k = convolutionSquare f by rfl,
    fourierLaplace_convolutionSquare_real] at hRe
  rw [show (∫ t : ℝ,
      (Complex.normSq (fourierLaplace f t) : ℂ) *
        (Real.cos (t * x) : ℂ)) =
      ((∫ t : ℝ,
        Complex.normSq (fourierLaplace f t) * Real.cos (t * x) : ℝ) : ℂ) by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with t
    exact (Complex.ofReal_mul _ _).symm] at hRe
  norm_num at hRe
  calc
    2 * (convolutionSquare f x).re =
        (convolutionSquare f x).re + (convolutionSquare f x).re := two_mul _
    _ = (1 / Real.pi) * ∫ t : ℝ,
        Complex.normSq (fourierLaplace f t) * Real.cos (t * x) := by
      rw [convolutionSquare_apply]
      simpa only [one_div] using hRe

private theorem translation_energy_fourier (f : WeilTestFunction) (x : ℝ) :
    translationEnergy f x =
      (1 / (2 * Real.pi)) * ∫ t : ℝ,
        2 * (1 - Real.cos (t * x)) * Complex.normSq (fourierLaplace f t) := by
  rw [translation_energy_eq_correlation]
  rw [← convolution_square_zero_re]
  rw [convolution_square_fourier_cos f 0, convolution_square_fourier_cos f x]
  norm_num
  rw [← mul_sub]
  rw [mul_assoc]
  rw [← integral_sub]
  · congr 1
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    ring
  · exact (Zeta23.EF.integrable_paperFT_mul_cos
      (Zeta23.EF.integrable_fourier_of_contDiff_two
        ((convolutionSquare f).contDiff.of_le
          (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
            exact WithTop.coe_le_coe.mpr le_top))
        (convolutionSquare f).hasCompactSupport) 0).re.congr (by
          filter_upwards with t
          rw [paperFT_eq_fourierLaplace,
            fourierLaplace_convolutionSquare_real]
          norm_num)
  · exact (Zeta23.EF.integrable_paperFT_mul_cos
      (Zeta23.EF.integrable_fourier_of_contDiff_two
        ((convolutionSquare f).contDiff.of_le
          (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
            exact WithTop.coe_le_coe.mpr le_top))
        (convolutionSquare f).hasCompactSupport) x).re.congr (by
          filter_upwards with t
          rw [paperFT_eq_fourierLaplace,
            fourierLaplace_convolutionSquare_real]
          change (((Complex.normSq (fourierLaplace f t) : ℝ) : ℂ) *
            (Real.cos (t * x) : ℂ)).re =
              Complex.normSq (fourierLaplace f t) * Real.cos (t * x)
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            mul_zero, sub_zero])

private theorem integrable_spectral_normSq (f : WeilTestFunction) :
    Integrable (fun t : ℝ => Complex.normSq (fourierLaplace f t)) := by
  have hkFourier : Integrable (𝓕 ((convolutionSquare f : WeilTestFunction) : ℝ → ℂ)) :=
    Zeta23.EF.integrable_fourier_of_contDiff_two
      ((convolutionSquare f).contDiff.of_le
        (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
          exact WithTop.coe_le_coe.mpr le_top))
      (convolutionSquare f).hasCompactSupport
  exact (Zeta23.EF.integrable_paperFT_mul_cos hkFourier 0).re.congr (by
    filter_upwards with t
    rw [paperFT_eq_fourierLaplace,
      fourierLaplace_convolutionSquare_real]
    norm_num)

private theorem digamma_increment_nonnegative (t : ℝ) :
    0 ≤
      (Complex.digamma
        ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
        (Complex.digamma (1 / 4)).re := by
  rw [← levy_integral_eq_digamma_increment]
  refine integral_nonneg_of_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  exact mul_nonneg (mul_nonneg (by norm_num) (jump_density_nonnegative hx))
    (sub_nonneg.mpr (Real.cos_le_one _))

private theorem integrable_spectral_increment (f : WeilTestFunction)
    (hArch : ArchimedeanConvergent (convolutionSquare f)) :
    Integrable (fun t : ℝ =>
      ((Complex.digamma
        ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
          (Complex.digamma (1 / 4)).re) *
        Complex.normSq (fourierLaplace f t)) := by
  have hFull : Integrable (fun t : ℝ =>
      ((Complex.digamma
        ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
          Real.log Real.pi) * Complex.normSq (fourierLaplace f t)) := by
    refine hArch.re.congr ?_
    filter_upwards with t
    unfold archimedeanIntegrand
    rw [fourierLaplace_convolutionSquare_real]
    have hArg :
        (1 / 4 : ℂ) + Complex.I * (t : ℂ) / 2 =
          (1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hArg]
    change (((((Complex.digamma
        ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
          Real.log Real.pi : ℝ) : ℂ) *
        ((Complex.normSq (fourierLaplace f t) : ℝ) : ℂ))).re = _
    norm_num
  have hConst := (integrable_spectral_normSq f).const_mul archimedeanConstant
  refine (hFull.sub hConst).congr ?_
  filter_upwards with t
  unfold archimedeanConstant
  change (((Complex.digamma
      ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
        Real.log Real.pi) * Complex.normSq (fourierLaplace f t)) -
      (((Complex.digamma (1 / 4)).re - Real.log Real.pi) *
        Complex.normSq (fourierLaplace f t)) = _
  ring

private theorem jump_energy_spectral (f : WeilTestFunction)
    (hArch : ArchimedeanConvergent (convolutionSquare f)) :
    archimedeanJumpEnergy f =
      (1 / (2 * Real.pi)) * ∫ t : ℝ,
        ((Complex.digamma
          ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
            (Complex.digamma (1 / 4)).re) *
          Complex.normSq (fourierLaplace f t) := by
  let F : ℝ × ℝ → ℝ := fun p =>
    (1 / (2 * Real.pi)) * Complex.normSq (fourierLaplace f p.2) *
      (2 * archimedeanJumpDensity p.1 * (1 - Real.cos (p.2 * p.1)))
  have hDensity : AEStronglyMeasurable archimedeanJumpDensity
      (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    unfold archimedeanJumpDensity
    measurability
  have hSpec := (integrable_spectral_normSq f).aestronglyMeasurable
  have hFMeas : AEStronglyMeasurable F
      ((volume.restrict (Ioi 0)).prod volume) := by
    dsimp only [F]
    exact (hSpec.comp_snd.const_mul (1 / (2 * Real.pi))).mul
      ((hDensity.comp_fst.const_mul 2).mul (by fun_prop))
  have hSections (t : ℝ) : Integrable
      (fun x : ℝ => F (x, t)) (volume.restrict (Ioi 0)) := by
    have h := (levy_kernel_integrableOn t).const_mul
      ((1 / (2 * Real.pi)) * Complex.normSq (fourierLaplace f t))
    refine h.congr ?_
    filter_upwards with x
    dsimp only [F]
  have hInnerF (t : ℝ) :
      (∫ x : ℝ in Ioi 0, F (x, t)) =
        (1 / (2 * Real.pi)) * Complex.normSq (fourierLaplace f t) *
          ((Complex.digamma
            ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
              (Complex.digamma (1 / 4)).re) := by
    dsimp only [F]
    rw [integral_const_mul]
    rw [levy_integral_eq_digamma_increment]
  have hInnerNorm (t : ℝ) :
      (∫ x : ℝ in Ioi 0, ‖F (x, t)‖) =
        (1 / (2 * Real.pi)) * Complex.normSq (fourierLaplace f t) *
          ((Complex.digamma
            ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
              (Complex.digamma (1 / 4)).re) := by
    rw [← hInnerF]
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg]
    dsimp only [F]
    exact mul_nonneg
      (mul_nonneg (by positivity) (Complex.normSq_nonneg _))
      (mul_nonneg
        (mul_nonneg (by norm_num) (jump_density_nonnegative hx))
        (sub_nonneg.mpr (Real.cos_le_one _)))
  have hOuter : Integrable (fun t : ℝ =>
      ∫ x : ℝ in Ioi 0, ‖F (x, t)‖) := by
    refine ((integrable_spectral_increment f hArch).const_mul
      (1 / (2 * Real.pi))).congr ?_
    filter_upwards with t
    rw [hInnerNorm]
    ring
  have hFInt : Integrable F ((volume.restrict (Ioi 0)).prod volume) :=
    (integrable_prod_iff' hFMeas).2
      ⟨Filter.Eventually.of_forall hSections, hOuter⟩
  have hSwap :
      (∫ x : ℝ in Ioi 0, ∫ t : ℝ, F (x, t)) =
        ∫ t : ℝ, ∫ x : ℝ in Ioi 0, F (x, t) :=
    integral_integral_swap hFInt
  calc
    archimedeanJumpEnergy f =
        ∫ x : ℝ in Ioi 0, ∫ t : ℝ, F (x, t) := by
      unfold archimedeanJumpEnergy
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      rw [translation_energy_fourier]
      rw [← integral_const_mul]
      dsimp only [F]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      ring
    _ = ∫ t : ℝ, ∫ x : ℝ in Ioi 0, F (x, t) := hSwap
    _ = ∫ t : ℝ,
        (1 / (2 * Real.pi)) *
          (((Complex.digamma
            ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
              (Complex.digamma (1 / 4)).re) *
            Complex.normSq (fourierLaplace f t)) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [hInnerF]
      ring
    _ = (1 / (2 * Real.pi)) * ∫ t : ℝ,
        ((Complex.digamma
          ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
            (Complex.digamma (1 / 4)).re) *
          Complex.normSq (fourierLaplace f t) := by
      rw [integral_const_mul]

private theorem l2_mass_spectral (f : WeilTestFunction) :
    l2Mass f =
      (1 / (2 * Real.pi)) * ∫ t : ℝ,
        Complex.normSq (fourierLaplace f t) := by
  have h := convolution_square_fourier_cos f 0
  rw [convolution_square_zero_re] at h
  norm_num at h
  calc
    l2Mass f = (1 / 2 : ℝ) * (2 * l2Mass f) := by ring
    _ = (1 / 2 : ℝ) *
        (Real.pi⁻¹ * ∫ t : ℝ, Complex.normSq (fourierLaplace f t)) := by
      rw [h]
    _ = (1 / (2 * Real.pi)) * ∫ t : ℝ,
        Complex.normSq (fourierLaplace f t) := by
      field_simp [Real.pi_ne_zero]

private theorem archimedean_term_real (f : WeilTestFunction)
    (hArch : ArchimedeanConvergent (convolutionSquare f)) :
    archimedeanTerm (convolutionSquare f) hArch =
      (((1 / (2 * Real.pi)) * ∫ t : ℝ,
        ((Complex.digamma
          ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
            Real.log Real.pi) *
          Complex.normSq (fourierLaplace f t) : ℝ) : ℂ) := by
  unfold archimedeanTerm
  have hIntegral :
      (∫ t : ℝ, archimedeanIntegrand (convolutionSquare f) t) =
        Complex.ofReal (∫ t : ℝ,
        ((Complex.digamma
          ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
            Real.log Real.pi) *
          Complex.normSq (fourierLaplace f t)) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with t
    unfold archimedeanIntegrand
    rw [fourierLaplace_convolutionSquare_real]
    have hArg :
        (1 / 4 : ℂ) + Complex.I * (t : ℂ) / 2 =
          (1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hArg]
    norm_num
  rw [hIntegral]
  exact (Complex.ofReal_mul _ _).symm

/-- The completed-zeta Archimedean term is its zero-frequency mass plus the
continuous positive translation energy. -/
theorem archimedean_jump_decomposition
    (f : WeilTestFunction)
    (hArch : ArchimedeanConvergent (convolutionSquare f)) :
    archimedeanTerm (convolutionSquare f) hArch =
        ((archimedeanConstant * l2Mass f +
          archimedeanJumpEnergy f : ℝ) : ℂ) ∧
      0 ≤ archimedeanJumpEnergy f := by
  constructor
  · rw [archimedean_term_real]
    congr 1
    have hFull : Integrable (fun t : ℝ =>
        ((Complex.digamma
          ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
            Real.log Real.pi) *
          Complex.normSq (fourierLaplace f t)) := by
      refine hArch.re.congr ?_
      filter_upwards with t
      unfold archimedeanIntegrand
      rw [fourierLaplace_convolutionSquare_real]
      have hArg :
          (1 / 4 : ℂ) + Complex.I * (t : ℂ) / 2 =
            (1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hArg]
      norm_num
    have hConst := (integrable_spectral_normSq f).const_mul archimedeanConstant
    have hIncrement := integrable_spectral_increment f hArch
    calc
      (1 / (2 * Real.pi)) * ∫ t : ℝ,
          ((Complex.digamma
            ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
              Real.log Real.pi) *
            Complex.normSq (fourierLaplace f t) =
          (1 / (2 * Real.pi)) * ∫ t : ℝ,
            (archimedeanConstant * Complex.normSq (fourierLaplace f t) +
              (((Complex.digamma
                ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
                  (Complex.digamma (1 / 4)).re) *
                Complex.normSq (fourierLaplace f t))) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with t
        unfold archimedeanConstant
        ring
      _ = (1 / (2 * Real.pi)) *
            ((∫ t : ℝ,
              archimedeanConstant * Complex.normSq (fourierLaplace f t)) +
              ∫ t : ℝ,
                ((Complex.digamma
                  ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
                    (Complex.digamma (1 / 4)).re) *
                  Complex.normSq (fourierLaplace f t)) := by
        rw [integral_add hConst hIncrement]
      _ = archimedeanConstant * l2Mass f + archimedeanJumpEnergy f := by
        rw [integral_const_mul, l2_mass_spectral, jump_energy_spectral f hArch]
        ring
  · exact jump_energy_nonnegative f

end D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
