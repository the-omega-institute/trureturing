/- STATIC COMPLETE ORIGINAL-Ioc SPECTRAL CORE ASSEMBLY V2, 2026-10-18.
UNCOMPILED: this full source and both the spectral and diagonal consumer
proof terms have not been elaborated or kernel-accepted. The accepted-v433
v6 cutoff and whole-line v2 source constituents are reused, with one owner
body. Their individual receipts do not transfer to this assembly or v4.35.
The manifest pins all inputs and distinguishes accepted from unchecked work.

The endpoint keeps precisely original Ioc L2 and finite actual Gamma energy
of the existing zero extension as its domain assumptions. It constructs a
smooth compact approximant supported inside the original open interval,
with original Ioc physical mass error plus actual Gamma energy error small.
No smoothness, continuity, endpoint trace, logarithmic domain or extra
Fourier-L2 input is introduced. The raw Fourier bridge is source-local.

No compiler, worktree, canonical source or download was touched. Earlier
constituent preparation comments below are historical, not current receipts.
-/


import D5.S3.Weil.PrimePoleTerms
import D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import D5.S3.Weil.ZetaGamma.GammaMu
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/- ASSEMBLY CONSTITUENT: core_v6 -/
/- TRANSIENT CORE V6: v4.33 COMPATIBILITY ONLY; NOT LATEST DEV. -/

/- TRANSIENT ACTUAL-DIGAMMA FULL-DOMAIN APPLICATION ASSEMBLY, UNCOMPILED.
Original owner proofs are included exactly source-locally after import hoisting;
the original owner module is not imported. Existing old proofs are reused, not
counted as new mathematics. All constituent exact hashes are in the manifest.
The root frequency-domain unit is make-accepted and awaiting scoped acceptance
at assembly time. No canonical declarations, Describe, Reg, or owner edits.
-/


/- GID: D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Decompose the completed-zeta Archimedean term into continuous translation energy. -/







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

theorem integral_exp_neg_mul_cos {c t : ℝ} (hc : 0 < c) :
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

























/- UNCOMPILED COMBINED UNIT. Both component make checks accepted; combined consumer not yet checked.
No RH, Robin, or closed Fourier-domain realization is claimed. -/


/- TRANSIENT EXACT APPLICATION ONLY, uncompiled. No canonical/Describe/Reg addition.
Stage 3 adds actual same-epsilon cutoff integrability, complex DCT, and L1 convergence.
The historical prelude comments describe their stage-0 status; proofs follow below.
Combines frozen product core SHA12e66d1af9748f411b66a61a82cd69ab8ac3a60bce6f0bf7ad305d32a382a899
and transport prelude SHA3b963a3de779a9bbc6d7f7637940b7778f77f15cdd9ae1c344978e81e5da7c73.
Original research sources remain unchanged. New pullback segment is not kernel checked. -/
/-
RESEARCH CANDIDATE ONLY. Product-bound extension not compiled or kernel checked.
The preceding energy-sum segment was parent-compiled at r2662; its frozen source
SHA256 is 5efb7e58ce3428c8e59b276399a30cb292a9cda82d50d5851bbd01dda57d73f7.
Fixed trureturing source: 085435040a3cc09d77a8ffd7853046debc4085f4.
Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d.

FromLiterature: classical Hilbert/Carleman integral inequality, proved here
through its actual r^(-1/2) row integral and weighted Young inequality.
No mathematical novelty claim and no canonical GID/registration.

Actual consumer: m=+1 and m=-1 Gamma boundary images. The arbitrary L2
absolute integrability below is precisely what is needed before the DCT
passage B_epsilon -> B in equation (7) of the companion ordinary proof.
No row/column bound or arbitrary bounded kernel/operator is a premise.

This draft consumes the energy-sum theorem for all MemLp inputs to derive
the general pi*sqrt(E_u)*sqrt(E_v) bound, including the two zero-energy
a.e. pullbacks. The exact full Gamma-density/far-image assembly is not
claimed as a formal consequence of this file alone.
-/


noncomputable section

open MeasureTheory Set
open scoped ENNReal ComplexConjugate

namespace ActualCarlemanL2PairingDraft20261017

private abbrev positiveMeasure : Measure ℝ := volume.restrict (Ioi 0)

-- Explicit instance checks for the intended real Lebesgue carrier and
-- product measure. Lebesgue.Basic publicly imports Haar.OfBasis, whose
-- Real.measureSpace instance is the real measure-space supplier.
example : MeasureSpace ℝ := inferInstance
example : SigmaFinite (volume : Measure ℝ) := inferInstance
example : SigmaFinite positiveMeasure := inferInstance
example : SigmaFinite (positiveMeasure.prod positiveMeasure) := inferInstance

/-- The actual weight ratio times the actual Carleman kernel. -/
private def rowKernel (r s : ℝ) : ℝ :=
  Real.sqrt r / (Real.sqrt s * (r + s))

/-- Exact row supplier, not a Schur-row hypothesis. Both integrability and
its value are derived by the substitutions s=t^2 and t=sqrt(r)*z. -/
private theorem actual_row_integrable_integral {r : ℝ} (hr : 0 < r) :
    Integrable (rowKernel r) positiveMeasure ∧
      (∫ s, rowKernel r s ∂positiveMeasure) = Real.pi := by
  let R := Real.sqrt r
  have hR : 0 < R := Real.sqrt_pos.mpr hr
  have hR2 : R ^ 2 = r := Real.sq_sqrt hr.le
  let g : ℝ → ℝ := fun t => 2 * t * rowKernel r (t ^ 2)
  have hscaled (z : ℝ) (hz : 0 < z) :
      g (R * z) = (2 / R) * (1 + z ^ 2)⁻¹ := by
    change 2 * (R * z) *
      (R / (Real.sqrt ((R * z) ^ 2) * (r + (R * z) ^ 2))) =
        (2 / R) * (1 + z ^ 2)⁻¹
    rw [Real.sqrt_sq (mul_nonneg hR.le hz.le)]
    have hOne : 0 < 1 + z ^ 2 := by positivity
    rw [← hR2]
    have hDen : R ^ 2 + (R * z) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hR.ne', hz.ne', hOne.ne', hDen] <;> ring
  have hscaled_ae :
      (fun z => g (R * z)) =ᵐ[positiveMeasure]
        (fun z => (2 / R) * (1 + z ^ 2)⁻¹) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    exact hscaled z hz
  have hbase : Integrable (fun z : ℝ => (2 / R) * (1 + z ^ 2)⁻¹)
      positiveMeasure :=
    integrable_inv_one_add_sq.integrableOn.const_mul (2 / R)
  have hg : Integrable g positiveMeasure := by
    have hs : IntegrableOn (fun z => g (R * z)) (Ioi 0) :=
      hbase.congr hscaled_ae.symm
    have hi := (integrableOn_Ioi_comp_mul_left_iff g 0 hR).mp hs
    simpa only [mul_zero, IntegrableOn, positiveMeasure] using hi
  have hpow_int :
      Integrable (fun t : ℝ =>
        (|(2 : ℝ)| * t ^ ((2 : ℝ) - 1)) • rowKernel r (t ^ (2 : ℝ)))
        positiveMeasure := by
    simpa only [show |(2 : ℝ)| = 2 by norm_num,
      show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
      smul_eq_mul] using hg
  have hrow : Integrable (rowKernel r) positiveMeasure :=
    (integrableOn_Ioi_comp_rpow_iff (rowKernel r) (p := 2) (by norm_num)).mp hpow_int
  have hpow : (∫ t, g t ∂positiveMeasure) =
      ∫ s, rowKernel r s ∂positiveMeasure := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num,
      Real.rpow_one, Real.rpow_two, smul_eq_mul] using
      (integral_comp_rpow_Ioi_of_pos (g := rowKernel r) (p := 2) (by norm_num))
  have hscale : (∫ z, g (R * z) ∂positiveMeasure) =
      R⁻¹ * ∫ t, g t ∂positiveMeasure := by
    simpa only [mul_zero, smul_eq_mul] using integral_comp_mul_left_Ioi g 0 hR
  have hscaled_value : (∫ z, g (R * z) ∂positiveMeasure) =
      (2 / R) * (Real.pi / 2) := by
    rw [integral_congr_ae hscaled_ae, integral_const_mul]
    simp only [positiveMeasure, integral_Ioi_inv_one_add_sq,
      Real.arctan_zero, sub_zero]
  refine ⟨hrow, ?_⟩
  calc
    (∫ s, rowKernel r s ∂positiveMeasure) =
        ∫ t, g t ∂positiveMeasure := hpow.symm
    _ = R * ∫ z, g (R * z) ∂positiveMeasure := by
      rw [hscale, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
    _ = R * ((2 / R) * (Real.pi / 2)) := by rw [hscaled_value]
    _ = Real.pi := by field_simp [hR.ne'] <;> ring

private theorem row_nonneg {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    0 ≤ rowKernel r s := by
  exact div_nonneg (Real.sqrt_nonneg r)
    (mul_nonneg (Real.sqrt_nonneg s) (add_pos hr hs).le)

/-- Actual product-space majorant, with the singular weight integrated
before integrability of the pairing is asserted. -/
private def squareMajorant (u : ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ‖u p.1‖ ^ 2 * rowKernel p.1 p.2

private theorem square_majorant_integrable_integral
    {u : ℝ → ℂ} (hu : MemLp u 2 positiveMeasure) :
    Integrable (squareMajorant u) (positiveMeasure.prod positiveMeasure) ∧
      (∫ p, squareMajorant u p ∂positiveMeasure.prod positiveMeasure) =
        Real.pi * ∫ r, ‖u r‖ ^ 2 ∂positiveMeasure := by
  have hu2 : Integrable (fun r => ‖u r‖ ^ 2) positiveMeasure :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  have hK : Measurable (fun p : ℝ × ℝ => rowKernel p.1 p.2) := by
    dsimp [rowKernel]
    fun_prop
  have hM : AEStronglyMeasurable (squareMajorant u)
      (positiveMeasure.prod positiveMeasure) :=
    (hu2.aestronglyMeasurable.comp_fst).mul hK.aestronglyMeasurable
  have hInner (r : ℝ) (hr : 0 < r) :
      (∫ s, squareMajorant u (r, s) ∂positiveMeasure) = Real.pi * ‖u r‖ ^ 2 := by
    dsimp only [squareMajorant]
    rw [integral_const_mul, (actual_row_integrable_integral hr).2, mul_comm]
  have hNormInner (r : ℝ) (hr : 0 < r) :
      (∫ s, ‖squareMajorant u (r, s)‖ ∂positiveMeasure) = Real.pi * ‖u r‖ ^ 2 := by
    calc
      _ = ∫ s, squareMajorant u (r, s) ∂positiveMeasure := by
        apply integral_congr_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
        exact Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (row_nonneg hr hs))
      _ = _ := hInner r hr
  have hInt : Integrable (squareMajorant u)
      (positiveMeasure.prod positiveMeasure) := by
    apply (integrable_prod_iff hM).2
    constructor
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      exact ((actual_row_integrable_integral hr).1).const_mul (‖u r‖ ^ 2)
    · apply (hu2.const_mul Real.pi).congr
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      exact (hNormInner r hr).symm
  refine ⟨hInt, ?_⟩
  rw [integral_prod _ hInt]
  calc
    _ = ∫ r, Real.pi * ‖u r‖ ^ 2 ∂positiveMeasure := by
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      exact hInner r hr
    _ = _ := integral_const_mul _ _

/-- The actual Carleman absolute pairing; no double-integrability premise. -/
private theorem actual_carleman_l2_pairing
    {u v : ℝ → ℂ} (hu : MemLp u 2 positiveMeasure) (hv : MemLp v 2 positiveMeasure) :
    Integrable (fun p : ℝ × ℝ => ‖u p.1‖ * ‖v p.2‖ / (p.1 + p.2))
      (positiveMeasure.prod positiveMeasure) ∧
    (∫ p : ℝ × ℝ, ‖u p.1‖ * ‖v p.2‖ / (p.1 + p.2)
      ∂positiveMeasure.prod positiveMeasure) ≤
      (Real.pi / 2) * ((∫ r, ‖u r‖ ^ 2 ∂positiveMeasure) +
        ∫ s, ‖v s‖ ^ 2 ∂positiveMeasure) := by
  let F : ℝ × ℝ → ℝ := fun p => ‖u p.1‖ * ‖v p.2‖ / (p.1 + p.2)
  let A := squareMajorant u
  let B : ℝ × ℝ → ℝ := fun p => squareMajorant v p.swap
  have hA := square_majorant_integrable_integral hu
  have hV := square_majorant_integrable_integral hv
  have hB : Integrable B (positiveMeasure.prod positiveMeasure) := hV.1.swap
  have hBI : (∫ p, B p ∂positiveMeasure.prod positiveMeasure) =
      Real.pi * ∫ s, ‖v s‖ ^ 2 ∂positiveMeasure := by
    change (∫ p, squareMajorant v p.swap ∂positiveMeasure.prod positiveMeasure) = _
    rw [integral_prod_swap]
    exact hV.2
  have hPos : ∀ᵐ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
      0 < p.1 ∧ 0 < p.2 := by
    apply (MeasureTheory.Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact ⟨hr, hs⟩
  have hPoint (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
      2 * F (r, s) ≤ A (r, s) + B (r, s) := by
    have hR : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
    have hS : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
    have hD : 0 < Real.sqrt r * Real.sqrt s * (r + s) := by positivity
    have hEq : (A (r, s) + B (r, s) - 2 * F (r, s)) *
        (Real.sqrt r * Real.sqrt s * (r + s)) =
        (‖u r‖ * Real.sqrt r - ‖v s‖ * Real.sqrt s) ^ 2 := by
      dsimp [F, A, B, squareMajorant, rowKernel]
      field_simp [hR.ne', hS.ne', (add_pos hr hs).ne', (add_pos hs hr).ne'] <;> ring
    have hp : 0 ≤ (A (r, s) + B (r, s) - 2 * F (r, s)) *
        (Real.sqrt r * Real.sqrt s * (r + s)) := by
      rw [hEq]
      exact sq_nonneg _
    have hh : 0 ≤ A (r, s) + B (r, s) - 2 * F (r, s) :=
      nonneg_of_mul_nonneg_left hp hD
    linarith
  have hFm : AEStronglyMeasurable F (positiveMeasure.prod positiveMeasure) :=
    (hu.aestronglyMeasurable.norm.comp_fst.mul hv.aestronglyMeasurable.norm.comp_snd).div₀
      (measurable_fst.add measurable_snd).aestronglyMeasurable
  have hDomInt : Integrable (fun p => (1 / 2 : ℝ) * (A p + B p))
      (positiveMeasure.prod positiveMeasure) := (hA.1.add hB).const_mul (1 / 2)
  have hLe : ∀ᵐ p ∂positiveMeasure.prod positiveMeasure,
      F p ≤ (1 / 2 : ℝ) * (A p + B p) := by
    filter_upwards [hPos] with p hp
    have h := hPoint p.1 p.2 hp.1 hp.2
    nlinarith
  have hF : Integrable F (positiveMeasure.prod positiveMeasure) := by
    apply hDomInt.mono' hFm
    filter_upwards [hPos, hLe] with p hp hle
    rw [Real.norm_of_nonneg (div_nonneg
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (add_pos hp.1 hp.2).le)]
    exact hle
  refine ⟨hF, (integral_mono_ae hF hDomInt hLe).trans_eq ?_⟩
  rw [integral_const_mul, integral_add hA.1 hB, hA.2, hBI]
  ring

/-- Classical Carleman inequality on the actual positive Lebesgue half-line.
The conclusion includes absolute-pairing integrability for arbitrary complex L2
inputs. Its product bound consumes the energy-sum theorem above; zero energies
are handled by a.e. vanishing pulled back along the product projections. -/
theorem carleman_integrable_and_integral_le
    {u v : ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict (Ioi 0)))
    (hv : MemLp v 2 (volume.restrict (Ioi 0))) :
    Integrable (fun p : ℝ × ℝ => ‖u p.1‖ * ‖v p.2‖ / (p.1 + p.2))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) ∧
    (∫ p : ℝ × ℝ, ‖u p.1‖ * ‖v p.2‖ / (p.1 + p.2)
      ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) ≤
      Real.pi * Real.sqrt (∫ r, ‖u r‖ ^ 2 ∂volume.restrict (Ioi 0)) *
        Real.sqrt (∫ s, ‖v s‖ ^ 2 ∂volume.restrict (Ioi 0)) := by
  refine ⟨(actual_carleman_l2_pairing hu hv).1, ?_⟩
  let F : ℝ × ℝ → ℝ := fun p => ‖u p.1‖ * ‖v p.2‖ / (p.1 + p.2)
  let J : ℝ := ∫ p, F p ∂positiveMeasure.prod positiveMeasure
  let Eu : ℝ := ∫ r, ‖u r‖ ^ 2 ∂positiveMeasure
  let Ev : ℝ := ∫ s, ‖v s‖ ^ 2 ∂positiveMeasure
  change J ≤ Real.pi * Real.sqrt Eu * Real.sqrt Ev
  have hu2 : Integrable (fun r => ‖u r‖ ^ 2) positiveMeasure :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  have hv2 : Integrable (fun s => ‖v s‖ ^ 2) positiveMeasure :=
    (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  have hEu0 : 0 ≤ Eu := integral_nonneg (fun r => sq_nonneg ‖u r‖)
  have hEv0 : 0 ≤ Ev := integral_nonneg (fun s => sq_nonneg ‖v s‖)
  by_cases hEu : Eu = 0
  · have huZeroSq : ∀ᵐ r ∂positiveMeasure, ‖u r‖ ^ 2 = 0 :=
      (integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall fun r => sq_nonneg ‖u r‖) hu2).mp hEu
    have huZero : ∀ᵐ r ∂positiveMeasure, ‖u r‖ = 0 := by
      filter_upwards [huZeroSq] with r hr
      exact sq_eq_zero_iff.mp hr
    have huProdZero : ∀ᵐ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
        ‖u p.1‖ = 0 :=
      MeasureTheory.Measure.quasiMeasurePreserving_fst.ae huZero
    have hJ : J = 0 := by
      change (∫ p, F p ∂positiveMeasure.prod positiveMeasure) = 0
      calc
        _ = ∫ _p : ℝ × ℝ, (0 : ℝ) ∂positiveMeasure.prod positiveMeasure := by
          apply integral_congr_ae
          filter_upwards [huProdZero] with p hp
          simp [F, hp]
        _ = 0 := by simp
    rw [hJ, hEu]
    simp
  by_cases hEv : Ev = 0
  · have hvZeroSq : ∀ᵐ s ∂positiveMeasure, ‖v s‖ ^ 2 = 0 :=
      (integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall fun s => sq_nonneg ‖v s‖) hv2).mp hEv
    have hvZero : ∀ᵐ s ∂positiveMeasure, ‖v s‖ = 0 := by
      filter_upwards [hvZeroSq] with s hs
      exact sq_eq_zero_iff.mp hs
    have hvProdZero : ∀ᵐ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
        ‖v p.2‖ = 0 :=
      MeasureTheory.Measure.quasiMeasurePreserving_snd.ae hvZero
    have hJ : J = 0 := by
      change (∫ p, F p ∂positiveMeasure.prod positiveMeasure) = 0
      calc
        _ = ∫ _p : ℝ × ℝ, (0 : ℝ) ∂positiveMeasure.prod positiveMeasure := by
          apply integral_congr_ae
          filter_upwards [hvProdZero] with p hp
          simp [F, hp]
        _ = 0 := by simp
    rw [hJ, hEv]
    simp
  let a : ℝ := Real.sqrt Eu
  let b : ℝ := Real.sqrt Ev
  have ha : 0 < a := Real.sqrt_pos.mpr (lt_of_le_of_ne hEu0 (Ne.symm hEu))
  have hb : 0 < b := Real.sqrt_pos.mpr (lt_of_le_of_ne hEv0 (Ne.symm hEv))
  have ha2 : a ^ 2 = Eu := Real.sq_sqrt hEu0
  have hb2 : b ^ 2 = Ev := Real.sq_sqrt hEv0
  have hEnergy (c : ℝ) (hc : 0 ≤ c) (f : ℝ → ℂ) :
      (∫ r, ‖(c • f) r‖ ^ 2 ∂positiveMeasure) =
        c ^ 2 * ∫ r, ‖f r‖ ^ 2 ∂positiveMeasure := by
    simp only [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hc, mul_pow]
    exact integral_const_mul _ _
  have hPairScale :
      (∫ p : ℝ × ℝ, ‖(b • u) p.1‖ * ‖(a • v) p.2‖ / (p.1 + p.2)
        ∂positiveMeasure.prod positiveMeasure) = (b * a) * J := by
    calc
      _ = ∫ p, (b * a) * F p ∂positiveMeasure.prod positiveMeasure := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun p => by
          dsimp only [F]
          simp only [Pi.smul_apply, norm_smul,
            Real.norm_of_nonneg hb.le, Real.norm_of_nonneg ha.le]
          ring
      _ = _ := integral_const_mul _ _
  have hBalanced :=
    (actual_carleman_l2_pairing (hu.const_smul b) (hv.const_smul a)).2
  rw [hPairScale, hEnergy b hb.le u, hEnergy a ha.le v] at hBalanced
  change (b * a) * J ≤ (Real.pi / 2) * (b ^ 2 * Eu + a ^ 2 * Ev) at hBalanced
  change J ≤ Real.pi * a * b
  apply (mul_le_mul_iff_of_pos_left (mul_pos hb ha)).mp
  refine hBalanced.trans_eq ?_
  rw [← ha2, ← hb2]
  ring

end ActualCarlemanL2PairingDraft20261017

namespace ActualGammaCornerTransportDraft20261017

abbrev intervalMeasure (a : ℝ) : Measure ℝ := volume.restrict (Ioo (-a) a)
abbrev shortMeasure (a : ℝ) : Measure ℝ := volume.restrict (Ioo 0 (2 * a))
abbrev positiveMeasure : Measure ℝ := volume.restrict (Ioi 0)

def shiftEquiv (a : ℝ) : ℝ ≃ᵐ ℝ := MeasurableEquiv.addRight a
def reflectEquiv (a : ℝ) : ℝ ≃ᵐ ℝ := MeasurableEquiv.subLeft a

theorem shift_preimage_window (a : ℝ) :
    (fun x : ℝ => x + a) ⁻¹' Ioo 0 (2 * a) = Ioo (-a) a := by
  ext x
  change (0 < x + a ∧ x + a < 2 * a) ↔ (-a < x ∧ x < a)
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem reflect_preimage_window (a : ℝ) :
    (fun x : ℝ => a - x) ⁻¹' Ioo 0 (2 * a) = Ioo (-a) a := by
  ext x
  change (0 < a - x ∧ a - x < 2 * a) ↔ (-a < x ∧ x < a)
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem shift_interval_measurePreserving (a : ℝ) :
    MeasurePreserving (shiftEquiv a) (intervalMeasure a) (shortMeasure a) := by
  change MeasurePreserving (fun x : ℝ => x + a)
    (volume.restrict (Ioo (-a) a)) (volume.restrict (Ioo 0 (2 * a)))
  rw [← shift_preimage_window a]
  exact (measurePreserving_add_right (volume : Measure ℝ) a).restrict_preimage
    measurableSet_Ioo

theorem reflect_interval_measurePreserving (a : ℝ) :
    MeasurePreserving (reflectEquiv a) (intervalMeasure a) (shortMeasure a) := by
  change MeasurePreserving (fun x : ℝ => a - x)
    (volume.restrict (Ioo (-a) a)) (volume.restrict (Ioo 0 (2 * a)))
  rw [← reflect_preimage_window a]
  exact (Measure.measurePreserving_sub_left (volume : Measure ℝ) a).restrict_preimage
    measurableSet_Ioo

theorem short_restrict_positive (a : ℝ) :
    positiveMeasure.restrict (Ioo 0 (2 * a)) = shortMeasure a := by
  exact Measure.restrict_restrict_of_subset (fun _ hx => hx.1)

/-- Inverse transport on the finite positive interval, followed by zero extension. -/
def transported (a : ℝ) (e : ℝ ≃ᵐ ℝ) (u : ℝ → ℂ) : ℝ → ℂ :=
  (Ioo 0 (2 * a)).indicator (u ∘ e.symm)

theorem transported_memLp (a : ℝ) (e : ℝ ≃ᵐ ℝ)
    (he : MeasurePreserving e (intervalMeasure a) (shortMeasure a))
    {u : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a)) :
    MemLp (transported a e u) 2 positiveMeasure := by
  unfold transported
  apply (memLp_indicator_iff_restrict (μ := positiveMeasure)
    measurableSet_Ioo.nullMeasurableSet).2
  rw [short_restrict_positive]
  exact hu.comp_measurePreserving (MeasurePreserving.symm e he)

/-- This identity uses only actual measure transport. In applications,
`transported_memLp` supplies square integrability before analytic estimates. -/
theorem transported_square_integral (a : ℝ) (e : ℝ ≃ᵐ ℝ)
    (he : MeasurePreserving e (intervalMeasure a) (shortMeasure a)) (u : ℝ → ℂ) :
    (∫ r, ‖transported a e u r‖ ^ 2 ∂positiveMeasure) =
      ∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a := by
  calc
    _ = ∫ r, (Ioo 0 (2 * a)).indicator
        (fun r => ‖u (e.symm r)‖ ^ 2) r ∂positiveMeasure := by
      apply integral_congr_ae
      filter_upwards with r
      by_cases hr : r ∈ Ioo 0 (2 * a) <;> simp [transported, hr]
    _ = ∫ r, ‖u (e.symm r)‖ ^ 2 ∂shortMeasure a := by
      rw [integral_indicator measurableSet_Ioo, short_restrict_positive]
    _ = _ := (MeasurePreserving.symm e he).integral_comp'
      (fun x => ‖u x‖ ^ 2)

def plusEquiv (a : ℝ) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  (shiftEquiv a).prodCongr (reflectEquiv a)

def minusEquiv (a : ℝ) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  (reflectEquiv a).prodCongr (shiftEquiv a)

theorem plus_interval_measurePreserving (a : ℝ) :
    MeasurePreserving (plusEquiv a)
      ((intervalMeasure a).prod (intervalMeasure a))
      ((shortMeasure a).prod (shortMeasure a)) := by
  change MeasurePreserving (Prod.map (shiftEquiv a) (reflectEquiv a)) _ _
  exact (shift_interval_measurePreserving a).prod
    (reflect_interval_measurePreserving a)

theorem minus_interval_measurePreserving (a : ℝ) :
    MeasurePreserving (minusEquiv a)
      ((intervalMeasure a).prod (intervalMeasure a))
      ((shortMeasure a).prod (shortMeasure a)) := by
  change MeasurePreserving (Prod.map (reflectEquiv a) (shiftEquiv a)) _ _
  exact (reflect_interval_measurePreserving a).prod
    (shift_interval_measurePreserving a)

def plusDistance (a : ℝ) (p : ℝ × ℝ) : ℝ := p.1 - p.2 + 2 * a
def minusDistance (a : ℝ) (p : ℝ × ℝ) : ℝ := p.2 - p.1 + 2 * a

theorem plus_distance_coordinates (a : ℝ) (p : ℝ × ℝ) :
    plusDistance a p = (plusEquiv a p).1 + (plusEquiv a p).2 := by
  change p.1 - p.2 + 2 * a = (p.1 + a) + (a - p.2)
  ring

theorem minus_distance_coordinates (a : ℝ) (p : ℝ × ℝ) :
    minusDistance a p = (minusEquiv a p).1 + (minusEquiv a p).2 := by
  change p.2 - p.1 + 2 * a = (a - p.1) + (p.2 + a)
  ring

theorem distances_pos {a : ℝ} {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    0 < plusDistance a p ∧ 0 < minusDistance a p := by
  dsimp [plusDistance, minusDistance]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

abbrev actualDensity :=
  D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity

def plusPair (a : ℝ) (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  conj (u p.1) * (actualDensity (plusDistance a p) : ℂ) * v p.2

def minusPair (a : ℝ) (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  conj (u p.1) * (actualDensity (minusDistance a p) : ℂ) * v p.2

/-- The same epsilon cuts the original distance in each actual image. -/
def twoCornerCutoffPair (a ε : ℝ) (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  {q | ε < plusDistance a q}.indicator (plusPair a u v) p +
    {q | ε < minusDistance a q}.indicator (minusPair a u v) p

-- Actual density domination, Carleman pullback, complex integrability,
-- and the same-epsilon DCT are intentionally not represented by an
-- assumed bound, an axiom, a sorry, or a purported proved theorem here.
-- Their exact proof and next Lean obligations are in the companion note.

end ActualGammaCornerTransportDraft20261017

namespace ActualGammaCornerTransportDraft20261017

open Filter
open scoped Topology

private theorem interval_product_membership (a : ℝ) :
    ∀ᵐ p : ℝ × ℝ ∂(intervalMeasure a).prod (intervalMeasure a),
      p.1 ∈ Ioo (-a) a ∧ p.2 ∈ Ioo (-a) a := by
  exact (Measure.quasiMeasurePreserving_fst.ae
    (self_mem_ae_restrict measurableSet_Ioo)).and
      (Measure.quasiMeasurePreserving_snd.ae
        (self_mem_ae_restrict measurableSet_Ioo))

private theorem shortMeasure_le_positive (a : ℝ) : shortMeasure a ≤ positiveMeasure := by
  rw [← short_restrict_positive a]
  exact Measure.restrict_le_self

/-- Only structural measure-preservation premises enter this internal transport
helper. The actual affine maps supply them below; no analytic bound is assumed. -/
private theorem transported_carleman_pullback (a : ℝ) (e f : ℝ ≃ᵐ ℝ)
    (he : MeasurePreserving e (intervalMeasure a) (shortMeasure a))
    (hf : MeasurePreserving f (intervalMeasure a) (shortMeasure a))
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (fun p : ℝ × ℝ =>
      ‖u p.1‖ * ‖v p.2‖ / (e p.1 + f p.2))
      ((intervalMeasure a).prod (intervalMeasure a)) ∧
    (∫ p : ℝ × ℝ, ‖u p.1‖ * ‖v p.2‖ / (e p.1 + f p.2)
      ∂(intervalMeasure a).prod (intervalMeasure a)) ≤
      Real.pi * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
        Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a) := by
  let U := transported a e u
  let V := transported a f v
  let F : ℝ × ℝ → ℝ := fun p => ‖U p.1‖ * ‖V p.2‖ / (p.1 + p.2)
  have hU : MemLp U 2 positiveMeasure := transported_memLp a e he hu
  have hV : MemLp V 2 positiveMeasure := transported_memLp a f hf hv
  obtain ⟨hF, hBound⟩ :=
    ActualCarlemanL2PairingDraft20261017.carleman_integrable_and_integral_le hU hV
  have hFi : Integrable F (positiveMeasure.prod positiveMeasure) := hF
  have hprod : (shortMeasure a).prod (shortMeasure a) ≤
      positiveMeasure.prod positiveMeasure :=
    Measure.prod_mono (shortMeasure_le_positive a) (shortMeasure_le_positive a)
  have hFshort : Integrable F ((shortMeasure a).prod (shortMeasure a)) :=
    hFi.mono_measure hprod
  have hPos : ∀ᵐ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
      0 < p.1 ∧ 0 < p.2 :=
    (Measure.quasiMeasurePreserving_fst.ae
      (self_mem_ae_restrict measurableSet_Ioi)).and
        (Measure.quasiMeasurePreserving_snd.ae
          (self_mem_ae_restrict measurableSet_Ioi))
  have hFnonneg : ∀ᵐ p ∂positiveMeasure.prod positiveMeasure, 0 ≤ F p := by
    filter_upwards [hPos] with p hp
    exact div_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (add_pos hp.1 hp.2).le
  change (∫ p, F p ∂positiveMeasure.prod positiveMeasure) ≤
    Real.pi * Real.sqrt (∫ x, ‖transported a e u x‖ ^ 2 ∂positiveMeasure) *
      Real.sqrt (∫ y, ‖transported a f v y‖ ^ 2 ∂positiveMeasure) at hBound
  rw [transported_square_integral a e he u,
    transported_square_integral a f hf v] at hBound
  have hShortBound : (∫ p, F p ∂(shortMeasure a).prod (shortMeasure a)) ≤
      Real.pi * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
        Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a) :=
    (integral_mono_measure hprod hFnonneg hFi).trans hBound
  have hmap : MeasurePreserving (e.prodCongr f)
      ((intervalMeasure a).prod (intervalMeasure a))
      ((shortMeasure a).prod (shortMeasure a)) := by
    change MeasurePreserving (Prod.map e f) _ _
    exact he.prod hf
  have hEJ : ∀ᵐ p : ℝ × ℝ ∂(intervalMeasure a).prod (intervalMeasure a),
      e p.1 ∈ Ioo 0 (2 * a) ∧ f p.2 ∈ Ioo 0 (2 * a) :=
    (Measure.quasiMeasurePreserving_fst.ae
      (he.quasiMeasurePreserving.ae (self_mem_ae_restrict measurableSet_Ioo))).and
        (Measure.quasiMeasurePreserving_snd.ae
          (hf.quasiMeasurePreserving.ae (self_mem_ae_restrict measurableSet_Ioo)))
  have hEq : (fun p : ℝ × ℝ => F ((e.prodCongr f) p)) =ᵐ[
      (intervalMeasure a).prod (intervalMeasure a)]
      (fun p => ‖u p.1‖ * ‖v p.2‖ / (e p.1 + f p.2)) := by
    filter_upwards [hEJ] with p hp
    have hEu : transported a e u (e p.1) = u p.1 := by
      change (Ioo 0 (2 * a)).indicator (u ∘ e.symm) (e p.1) = u p.1
      rw [indicator_of_mem hp.1]
      exact congrArg u (e.symm_apply_apply p.1)
    have hFv : transported a f v (f p.2) = v p.2 := by
      change (Ioo 0 (2 * a)).indicator (v ∘ f.symm) (f p.2) = v p.2
      rw [indicator_of_mem hp.2]
      exact congrArg v (f.symm_apply_apply p.2)
    change ‖transported a e u (e p.1)‖ * ‖transported a f v (f p.2)‖ /
      (e p.1 + f p.2) = _
    rw [hEu, hFv]
  refine ⟨(hmap.integrable_comp_of_integrable hFshort).congr hEq, ?_⟩
  calc
    _ = ∫ p, F ((e.prodCongr f) p)
        ∂(intervalMeasure a).prod (intervalMeasure a) := (integral_congr_ae hEq).symm
    _ = ∫ p, F p ∂(shortMeasure a).prod (shortMeasure a) := hmap.integral_comp' F
    _ ≤ _ := hShortBound

private def plusMajorant (a : ℝ) (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ‖u p.1‖ * ‖v p.2‖ / plusDistance a p

private def minusMajorant (a : ℝ) (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ‖u p.1‖ * ‖v p.2‖ / minusDistance a p

private theorem plus_carleman_integrable_and_le (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (plusMajorant a u v) ((intervalMeasure a).prod (intervalMeasure a)) ∧
    (∫ p, plusMajorant a u v p ∂(intervalMeasure a).prod (intervalMeasure a)) ≤
      Real.pi * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
        Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a) := by
  have ht := transported_carleman_pullback a (shiftEquiv a) (reflectEquiv a)
    (shift_interval_measurePreserving a) (reflect_interval_measurePreserving a) hu hv
  have hfun : (fun p : ℝ × ℝ =>
      ‖u p.1‖ * ‖v p.2‖ / (shiftEquiv a p.1 + reflectEquiv a p.2)) =
      plusMajorant a u v := by
    funext p
    unfold plusMajorant
    rw [plus_distance_coordinates]
    rfl
  simpa only [hfun] using ht

private theorem minus_carleman_integrable_and_le (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (minusMajorant a u v) ((intervalMeasure a).prod (intervalMeasure a)) ∧
    (∫ p, minusMajorant a u v p ∂(intervalMeasure a).prod (intervalMeasure a)) ≤
      Real.pi * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
        Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a) := by
  have ht := transported_carleman_pullback a (reflectEquiv a) (shiftEquiv a)
    (reflect_interval_measurePreserving a) (shift_interval_measurePreserving a) hu hv
  have hfun : (fun p : ℝ × ℝ =>
      ‖u p.1‖ * ‖v p.2‖ / (reflectEquiv a p.1 + shiftEquiv a p.2)) =
      minusMajorant a u v := by
    funext p
    unfold minusMajorant
    rw [minus_distance_coordinates]
    rfl
  simpa only [hfun] using ht

-- Both actual corner suppliers, with no assumed row bound, corner
-- integrability, or smooth/core/Fourier premise. No new canonical object.
example (a : ℝ) (_ha : 0 < a) {u v : ℝ → ℂ}
    (hu : MemLp u 2 (intervalMeasure a)) (hv : MemLp v 2 (intervalMeasure a)) :
    (Integrable (plusMajorant a u v) ((intervalMeasure a).prod (intervalMeasure a)) ∧
      (∫ p, plusMajorant a u v p ∂(intervalMeasure a).prod (intervalMeasure a)) ≤
        Real.pi * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
          Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a)) ∧
    (Integrable (minusMajorant a u v) ((intervalMeasure a).prod (intervalMeasure a)) ∧
      (∫ p, minusMajorant a u v p ∂(intervalMeasure a).prod (intervalMeasure a)) ≤
        Real.pi * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
          Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a)) :=
  ⟨plus_carleman_integrable_and_le a hu hv, minus_carleman_integrable_and_le a hu hv⟩

end ActualGammaCornerTransportDraft20261017


namespace ActualGammaCornerTransportDraft20261017

private def gammaCk : ℝ := (1 - Real.exp (-2))⁻¹

private theorem gamma_delta_pos : 0 < 1 - Real.exp (-2) := by
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))

private theorem gammaCk_pos : 0 < gammaCk := inv_pos.mpr gamma_delta_pos

private theorem actual_density_pos {t : ℝ} (ht : 0 < t) : 0 < actualDensity t := by
  change 0 < Real.exp (-t / 2) / (1 - Real.exp (-2 * t))
  have hden : 0 < 1 - Real.exp (-2 * t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  exact div_pos (Real.exp_pos _) hden

/-- The actual exp quotient is bounded here, rather than assuming a corner
or Schur estimate. The small argument uses convexity; the tail uses the
classical bound on t*exp(-t/2). -/
private theorem actual_density_le_gammaCk_div {t : ℝ} (ht : 0 < t) :
    actualDensity t ≤ gammaCk / t := by
  let δ : ℝ := 1 - Real.exp (-2)
  have hδ : 0 < δ := gamma_delta_pos
  by_cases ht1 : t ≤ 1
  · have hconv : Real.exp ((1 - t) • (0 : ℝ) + t • (-2 : ℝ)) ≤
        (1 - t) • Real.exp 0 + t • Real.exp (-2) :=
      convexOn_exp.2 (mem_univ _) (mem_univ _)
        (sub_nonneg.mpr ht1) ht.le (by ring)
    simp only [smul_eq_mul] at hconv
    rw [show (1 - t) * 0 + t * (-2) = -2 * t by ring,
      Real.exp_zero, mul_one] at hconv
    have hden : t * δ ≤ 1 - Real.exp (-2 * t) := by
      dsimp only [δ]
      linarith
    have hnum : Real.exp (-t / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    calc
      actualDensity t = Real.exp (-t / 2) / (1 - Real.exp (-2 * t)) := rfl
      _ ≤ 1 / (t * δ) := div_le_div₀ zero_le_one hnum (mul_pos ht hδ) hden
      _ = gammaCk / t := by
        dsimp only [gammaCk, δ]
        simp only [one_div, mul_inv_rev, div_eq_mul_inv]
        ring
  · have htge : 1 ≤ t := (lt_of_not_ge ht1).le
    have hexp : Real.exp (-2 * t) ≤ Real.exp (-2) :=
      Real.exp_le_exp.mpr (by linarith)
    have hden : δ ≤ 1 - Real.exp (-2 * t) := sub_le_sub_left hexp 1
    have htwo : 2 * Real.exp (-1) ≤ 1 := by
      rw [Real.exp_neg]
      change 2 / Real.exp 1 ≤ 1
      exact (div_le_iff₀ (Real.exp_pos 1)).2 (by
        have hx := Real.add_one_le_exp (1 : ℝ)
        linarith)
    have hmul : t * Real.exp (-t / 2) ≤ 1 := by
      calc
        _ = 2 * ((t / 2) * Real.exp (-(t / 2))) := by rw [neg_div]; ring
        _ ≤ 2 * Real.exp (-1) :=
          mul_le_mul_of_nonneg_left
            (Real.mul_exp_neg_le_exp_neg_one (t / 2)) (by norm_num)
        _ ≤ 1 := htwo
    have hnum : Real.exp (-t / 2) ≤ 1 / t :=
      (le_div_iff₀ ht).2 (by nlinarith)
    calc
      actualDensity t = Real.exp (-t / 2) / (1 - Real.exp (-2 * t)) := rfl
      _ ≤ (1 / t) / δ :=
        div_le_div₀ (div_nonneg zero_le_one ht.le) hnum hδ hden
      _ = gammaCk / t := by
        dsimp only [gammaCk, δ]
        simp only [one_div, div_eq_mul_inv]
        ring

private theorem actual_density_measurable : Measurable actualDensity := by
  change Measurable (fun t : ℝ => Real.exp (-t / 2) / (1 - Real.exp (-2 * t)))
  fun_prop

private theorem plusPair_aestronglyMeasurable (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    AEStronglyMeasurable (plusPair a u v)
      ((intervalMeasure a).prod (intervalMeasure a)) := by
  have hK : Measurable (fun p : ℝ × ℝ => actualDensity (plusDistance a p)) :=
    actual_density_measurable.comp (by unfold plusDistance; fun_prop)
  have hKc : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (actualDensity (plusDistance a p) : ℂ))
      ((intervalMeasure a).prod (intervalMeasure a)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hK.aestronglyMeasurable
  exact ((Complex.continuous_conj.comp_aestronglyMeasurable hu.aestronglyMeasurable.comp_fst).mul hKc).mul
    hv.aestronglyMeasurable.comp_snd

private theorem minusPair_aestronglyMeasurable (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    AEStronglyMeasurable (minusPair a u v)
      ((intervalMeasure a).prod (intervalMeasure a)) := by
  have hK : Measurable (fun p : ℝ × ℝ => actualDensity (minusDistance a p)) :=
    actual_density_measurable.comp (by unfold minusDistance; fun_prop)
  have hKc : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (actualDensity (minusDistance a p) : ℂ))
      ((intervalMeasure a).prod (intervalMeasure a)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hK.aestronglyMeasurable
  exact ((Complex.continuous_conj.comp_aestronglyMeasurable hu.aestronglyMeasurable.comp_fst).mul hKc).mul
    hv.aestronglyMeasurable.comp_snd

private theorem plusPair_norm_le {a : ℝ} {u v : ℝ → ℂ} {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    ‖plusPair a u v p‖ ≤ gammaCk * plusMajorant a u v p := by
  have hd : 0 < plusDistance a p := (distances_pos hx hy).1
  have hk0 : 0 ≤ actualDensity (plusDistance a p) := (actual_density_pos hd).le
  have hk := actual_density_le_gammaCk_div hd
  dsimp only [plusPair, plusMajorant]
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_of_nonneg hk0]
  calc
    _ ≤ ‖u p.1‖ * (gammaCk / plusDistance a p) * ‖v p.2‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hk (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

private theorem minusPair_norm_le {a : ℝ} {u v : ℝ → ℂ} {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    ‖minusPair a u v p‖ ≤ gammaCk * minusMajorant a u v p := by
  have hd : 0 < minusDistance a p := (distances_pos hx hy).2
  have hk0 : 0 ≤ actualDensity (minusDistance a p) := (actual_density_pos hd).le
  have hk := actual_density_le_gammaCk_div hd
  dsimp only [minusPair, minusMajorant]
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_of_nonneg hk0]
  calc
    _ ≤ ‖u p.1‖ * (gammaCk / minusDistance a p) * ‖v p.2‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hk (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

private theorem plus_actual_corner_integrable_and_le (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (plusPair a u v) ((intervalMeasure a).prod (intervalMeasure a)) ∧
    (∫ p, ‖plusPair a u v p‖ ∂(intervalMeasure a).prod (intervalMeasure a)) ≤
      gammaCk * (Real.pi * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
        Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a)) := by
  have hc := plus_carleman_integrable_and_le a hu hv
  have hDom : Integrable (fun p => gammaCk * plusMajorant a u v p)
      ((intervalMeasure a).prod (intervalMeasure a)) := hc.1.const_mul gammaCk
  have hLe : ∀ᵐ p ∂(intervalMeasure a).prod (intervalMeasure a),
      ‖plusPair a u v p‖ ≤ gammaCk * plusMajorant a u v p := by
    filter_upwards [interval_product_membership a] with p hp
    exact plusPair_norm_le hp.1 hp.2
  have hInt : Integrable (plusPair a u v)
      ((intervalMeasure a).prod (intervalMeasure a)) :=
    hDom.mono' (plusPair_aestronglyMeasurable a hu hv) hLe
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ p, gammaCk * plusMajorant a u v p
        ∂(intervalMeasure a).prod (intervalMeasure a) :=
      integral_mono_ae hInt.norm hDom hLe
    _ = gammaCk * ∫ p, plusMajorant a u v p
        ∂(intervalMeasure a).prod (intervalMeasure a) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hc.2 gammaCk_pos.le

private theorem minus_actual_corner_integrable_and_le (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (minusPair a u v) ((intervalMeasure a).prod (intervalMeasure a)) ∧
    (∫ p, ‖minusPair a u v p‖ ∂(intervalMeasure a).prod (intervalMeasure a)) ≤
      gammaCk * (Real.pi * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
        Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a)) := by
  have hc := minus_carleman_integrable_and_le a hu hv
  have hDom : Integrable (fun p => gammaCk * minusMajorant a u v p)
      ((intervalMeasure a).prod (intervalMeasure a)) := hc.1.const_mul gammaCk
  have hLe : ∀ᵐ p ∂(intervalMeasure a).prod (intervalMeasure a),
      ‖minusPair a u v p‖ ≤ gammaCk * minusMajorant a u v p := by
    filter_upwards [interval_product_membership a] with p hp
    exact minusPair_norm_le hp.1 hp.2
  have hInt : Integrable (minusPair a u v)
      ((intervalMeasure a).prod (intervalMeasure a)) :=
    hDom.mono' (minusPair_aestronglyMeasurable a hu hv) hLe
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ p, gammaCk * minusMajorant a u v p
        ∂(intervalMeasure a).prod (intervalMeasure a) :=
      integral_mono_ae hInt.norm hDom hLe
    _ = gammaCk * ∫ p, minusMajorant a u v p
        ∂(intervalMeasure a).prod (intervalMeasure a) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hc.2 gammaCk_pos.le

example (a : ℝ) (_ha : 0 < a) {u v : ℝ → ℂ}
    (hu : MemLp u 2 (intervalMeasure a)) (hv : MemLp v 2 (intervalMeasure a)) :
    (Integrable (plusPair a u v) ((intervalMeasure a).prod (intervalMeasure a)) ∧
      (∫ p, ‖plusPair a u v p‖ ∂(intervalMeasure a).prod (intervalMeasure a)) ≤
        gammaCk * (Real.pi * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
          Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a))) ∧
    (Integrable (minusPair a u v) ((intervalMeasure a).prod (intervalMeasure a)) ∧
      (∫ p, ‖minusPair a u v p‖ ∂(intervalMeasure a).prod (intervalMeasure a)) ≤
        gammaCk * (Real.pi * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
          Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a))) :=
  ⟨plus_actual_corner_integrable_and_le a hu hv,
    minus_actual_corner_integrable_and_le a hu hv⟩

end ActualGammaCornerTransportDraft20261017


namespace ActualGammaCornerTransportDraft20261017

open Filter
open scoped Topology

private def twoCornerPair (a : ℝ) (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  plusPair a u v p + minusPair a u v p

private def twoCornerMajorant (a : ℝ) (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  gammaCk * (plusMajorant a u v p + minusMajorant a u v p)

private theorem twoCornerMajorant_integrable (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (twoCornerMajorant a u v)
      ((intervalMeasure a).prod (intervalMeasure a)) := by
  exact ((plus_carleman_integrable_and_le a hu hv).1.add
    (minus_carleman_integrable_and_le a hu hv).1).const_mul gammaCk

private theorem twoCornerPair_integrable (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (twoCornerPair a u v)
      ((intervalMeasure a).prod (intervalMeasure a)) := by
  exact (plus_actual_corner_integrable_and_le a hu hv).1.add
    (minus_actual_corner_integrable_and_le a hu hv).1

/-- Both masks use the same epsilon and the original two distances.
No smoothness or endpoint vanishing is required of the L2 inputs. -/
private theorem twoCornerCutoffPair_integrable (a ε : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (twoCornerCutoffPair a ε u v)
      ((intervalMeasure a).prod (intervalMeasure a)) := by
  have hDp : Measurable (plusDistance a) := by unfold plusDistance; fun_prop
  have hDm : Measurable (minusDistance a) := by unfold minusDistance; fun_prop
  exact ((plus_actual_corner_integrable_and_le a hu hv).1.indicator
    (measurableSet_lt measurable_const hDp)).add
      ((minus_actual_corner_integrable_and_le a hu hv).1.indicator
        (measurableSet_lt measurable_const hDm))

private theorem twoCornerCutoffPair_norm_le {a ε : ℝ} {u v : ℝ → ℂ}
    {p : ℝ × ℝ} (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    ‖twoCornerCutoffPair a ε u v p‖ ≤ twoCornerMajorant a u v p := by
  calc
    _ ≤ ‖{q | ε < plusDistance a q}.indicator (plusPair a u v) p‖ +
        ‖{q | ε < minusDistance a q}.indicator (minusPair a u v) p‖ :=
      norm_add_le _ _
    _ ≤ ‖plusPair a u v p‖ + ‖minusPair a u v p‖ :=
      add_le_add
        (norm_indicator_le_norm_self (s := {q | ε < plusDistance a q})
          (plusPair a u v) p)
        (norm_indicator_le_norm_self (s := {q | ε < minusDistance a q})
          (minusPair a u v) p)
    _ ≤ gammaCk * plusMajorant a u v p + gammaCk * minusMajorant a u v p :=
      add_le_add (plusPair_norm_le hx hy) (minusPair_norm_le hx hy)
    _ = twoCornerMajorant a u v p := by unfold twoCornerMajorant; ring

private theorem indicator_sub_norm_le {s : Set (ℝ × ℝ)}
    (f : (ℝ × ℝ) → ℂ) (p : ℝ × ℝ) :
    ‖s.indicator f p - f p‖ ≤ ‖f p‖ := by
  by_cases hp : p ∈ s <;> simp [hp]

/-- The omitted tails obey the same integrable majorant, with no extra
factor of two: each individual omitted mask has modulus at most one. -/
private theorem twoCornerCutoffPair_sub_norm_le {a ε : ℝ} {u v : ℝ → ℂ}
    {p : ℝ × ℝ} (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    ‖twoCornerCutoffPair a ε u v p - twoCornerPair a u v p‖ ≤
      twoCornerMajorant a u v p := by
  have heq : twoCornerCutoffPair a ε u v p - twoCornerPair a u v p =
      ({q | ε < plusDistance a q}.indicator (plusPair a u v) p -
        plusPair a u v p) +
      ({q | ε < minusDistance a q}.indicator (minusPair a u v) p -
        minusPair a u v p) := by
    unfold twoCornerCutoffPair twoCornerPair
    ring
  rw [heq]
  calc
    _ ≤ ‖{q | ε < plusDistance a q}.indicator (plusPair a u v) p -
          plusPair a u v p‖ +
        ‖{q | ε < minusDistance a q}.indicator (minusPair a u v) p -
          minusPair a u v p‖ := norm_add_le _ _
    _ ≤ ‖plusPair a u v p‖ + ‖minusPair a u v p‖ :=
      add_le_add (indicator_sub_norm_le (plusPair a u v) p)
        (indicator_sub_norm_le (minusPair a u v) p)
    _ ≤ gammaCk * plusMajorant a u v p + gammaCk * minusMajorant a u v p :=
      add_le_add (plusPair_norm_le hx hy) (minusPair_norm_le hx hy)
    _ = twoCornerMajorant a u v p := by unfold twoCornerMajorant; ring

/-- At every interior pair the two original distances are positive, so a
single sufficiently small epsilon makes both actual masks equal to one. -/
private theorem twoCornerCutoffPair_tendsto {a : ℝ} {u v : ℝ → ℂ}
    {p : ℝ × ℝ} (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    Tendsto (fun ε : ℝ => twoCornerCutoffPair a ε u v p)
      (𝓝[Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 (twoCornerPair a u v p)) := by
  have hd := distances_pos hx hy
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[Ioi (0 : ℝ)] (0 : ℝ),
      ε < min (plusDistance a p) (minusDistance a p) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_min hd.1 hd.2))
  apply tendsto_const_nhds.congr'
  filter_upwards [hsmall] with ε hε
  have hp : ε < plusDistance a p := lt_of_lt_of_le hε (min_le_left _ _)
  have hm : ε < minusDistance a p := lt_of_lt_of_le hε (min_le_right _ _)
  simp [twoCornerCutoffPair, twoCornerPair, hp, hm]

private theorem twoCornerCutoffPair_integral_tendsto (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Tendsto
      (fun ε : ℝ => ∫ p, twoCornerCutoffPair a ε u v p
        ∂(intervalMeasure a).prod (intervalMeasure a))
      (𝓝[Ioi (0 : ℝ)] (0 : ℝ))
      (𝓝 (∫ p, twoCornerPair a u v p
        ∂(intervalMeasure a).prod (intervalMeasure a))) := by
  apply tendsto_integral_filter_of_dominated_convergence (twoCornerMajorant a u v)
  · exact Eventually.of_forall fun ε =>
      (twoCornerCutoffPair_integrable a ε hu hv).aestronglyMeasurable
  · apply Eventually.of_forall
    intro ε
    filter_upwards [interval_product_membership a] with p hp
    exact twoCornerCutoffPair_norm_le hp.1 hp.2
  · exact twoCornerMajorant_integrable a hu hv
  · filter_upwards [interval_product_membership a] with p hp
    exact twoCornerCutoffPair_tendsto hp.1 hp.2

/-- Fixed-input L1 convergence of the actual two-corner pairing densities.
This is not operator-norm convergence, which the endpoint concentration
counterexample rules out. -/
private theorem twoCornerCutoffPair_L1_tendsto (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Tendsto
      (fun ε : ℝ => ∫ p,
        ‖twoCornerCutoffPair a ε u v p - twoCornerPair a u v p‖
        ∂(intervalMeasure a).prod (intervalMeasure a))
      (𝓝[Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hFull := (twoCornerPair_integrable a hu hv).aestronglyMeasurable
  have hDCT : Tendsto
      (fun ε : ℝ => ∫ p,
        ‖twoCornerCutoffPair a ε u v p - twoCornerPair a u v p‖
        ∂(intervalMeasure a).prod (intervalMeasure a))
      (𝓝[Ioi (0 : ℝ)] (0 : ℝ))
      (𝓝 (∫ _p : ℝ × ℝ, (0 : ℝ)
        ∂(intervalMeasure a).prod (intervalMeasure a))) := by
    apply tendsto_integral_filter_of_dominated_convergence (twoCornerMajorant a u v)
    · exact Eventually.of_forall fun ε =>
        ((twoCornerCutoffPair_integrable a ε hu hv).aestronglyMeasurable.sub hFull).norm
    · apply Eventually.of_forall
      intro ε
      filter_upwards [interval_product_membership a] with p hp
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact twoCornerCutoffPair_sub_norm_le hp.1 hp.2
    · exact twoCornerMajorant_integrable a hu hv
    · filter_upwards [interval_product_membership a] with p hp
      have hPoint := twoCornerCutoffPair_tendsto (u := u) (v := v) hp.1 hp.2
      simpa only [sub_self, norm_zero] using (hPoint.sub (tendsto_const_nhds (x := twoCornerPair a u v p))).norm
  simpa only [integral_zero] using hDCT

-- Actual end-to-end application: the only analytic input hypotheses are
-- MemLp on the interval. The Carleman bound, actual density bound,
-- absolute integrability, common-cutoff domination, and limits are proved
-- in the preceding segments. No kernel/operator/domain supplier is assumed.
example (a : ℝ) (_ha : 0 < a) {u v : ℝ → ℂ}
    (hu : MemLp u 2 (intervalMeasure a)) (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (twoCornerPair a u v)
        ((intervalMeasure a).prod (intervalMeasure a)) ∧
    (∀ ε : ℝ, Integrable (twoCornerCutoffPair a ε u v)
      ((intervalMeasure a).prod (intervalMeasure a))) ∧
    Tendsto
      (fun ε : ℝ => ∫ p, twoCornerCutoffPair a ε u v p
        ∂(intervalMeasure a).prod (intervalMeasure a))
      (𝓝[Ioi (0 : ℝ)] (0 : ℝ))
      (𝓝 (∫ p, twoCornerPair a u v p
        ∂(intervalMeasure a).prod (intervalMeasure a))) ∧
    Tendsto
      (fun ε : ℝ => ∫ p,
        ‖twoCornerCutoffPair a ε u v p - twoCornerPair a u v p‖
        ∂(intervalMeasure a).prod (intervalMeasure a))
      (𝓝[Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  exact ⟨twoCornerPair_integrable a hu hv,
    (fun ε => twoCornerCutoffPair_integrable a ε hu hv),
    twoCornerCutoffPair_integral_tendsto a hu hv,
    twoCornerCutoffPair_L1_tendsto a hu hv⟩

end ActualGammaCornerTransportDraft20261017


/- UNCOMPILED TRANSIENT FRAGMENT. Append after the corrected stage3 source,
with the same namespace/private helpers in one Lean file. Required extra imports:
Mathlib.Analysis.SpecificLimits.Normed
Mathlib.Topology.Algebra.InfiniteSum.NatInt
Mathlib.MeasureTheory.Constructions.Polish.Basic
No canonical/Describe/Reg additions. Uses only the actual Gamma density. -/

namespace ActualGammaCornerTransportDraft20261017

open Filter
open scoped Topology ComplexConjugate

private def farRatio (a : ℝ) : ℝ := Real.exp (-a)
private def farDenominator (a : ℝ) : ℝ := 1 - Real.exp (-4 * a)
private def farWeight (a : ℝ) (n : ℕ) : ℝ :=
  (farRatio a / farDenominator a) * farRatio a ^ n
private def actualCtail (a : ℝ) : ℝ :=
  2 * Real.exp (-a) / ((1 - Real.exp (-a)) * (1 - Real.exp (-4 * a)))

private def farDistance (a : ℝ) (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  p.1 - p.2 + ((n : ℝ) + 2) * (2 * a)

private def farCutoffKernel (a ε : ℝ) (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  if ε < farDistance a n p then actualDensity (farDistance a n p) else 0

private theorem farRatio_pos (a : ℝ) : 0 < farRatio a := Real.exp_pos _
private theorem farRatio_lt_one {a : ℝ} (ha : 0 < a) : farRatio a < 1 :=
  Real.exp_lt_one_iff.mpr (by linarith)
private theorem farDenominator_pos {a : ℝ} (ha : 0 < a) :
    0 < farDenominator a := by
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))

private theorem farWeight_nonneg {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 ≤ farWeight a n :=
  mul_nonneg (div_nonneg (farRatio_pos a).le (farDenominator_pos ha).le)
    (pow_nonneg (farRatio_pos a).le _)

private theorem farWeight_summable {a : ℝ} (ha : 0 < a) :
    Summable (farWeight a) := by
  exact (summable_geometric_of_norm_lt_one (by
    rw [Real.norm_of_nonneg (farRatio_pos a).le]
    exact farRatio_lt_one ha)).mul_left (farRatio a / farDenominator a)

private theorem two_farWeight_tsum {a : ℝ} (ha : 0 < a) :
    2 * (∑' n : ℕ, farWeight a n) = actualCtail a := by
  have hq : ‖farRatio a‖ < 1 := by
    rw [Real.norm_of_nonneg (farRatio_pos a).le]
    exact farRatio_lt_one ha
  rw [show (∑' n : ℕ, farWeight a n) =
      (farRatio a / farDenominator a) * (1 - farRatio a)⁻¹ by
    unfold farWeight
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hq]]
  unfold actualCtail farRatio farDenominator
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem actualCtail_nonneg {a : ℝ} (ha : 0 < a) : 0 ≤ actualCtail a := by
  rw [← two_farWeight_tsum ha]
  exact mul_nonneg (by norm_num) (tsum_nonneg fun n => farWeight_nonneg ha n)

private theorem farDistance_lower {a : ℝ} {p : ℝ × ℝ} (n : ℕ)
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    ((n : ℝ) + 1) * (2 * a) ≤ farDistance a n p := by
  unfold farDistance
  linarith [hx.1, hy.2]

private theorem farDistance_ge_period {a : ℝ} (ha : 0 < a)
    {p : ℝ × ℝ} (n : ℕ)
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    2 * a ≤ farDistance a n p := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have h := farDistance_lower n hx hy
  nlinarith

/-- The actual exp quotient, at the actual nth far-image distance, has
this explicit geometric bound. No generic kernel majorant is assumed. -/
private theorem actual_far_density_le_weight {a : ℝ} (ha : 0 < a)
    {p : ℝ × ℝ} (n : ℕ)
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    actualDensity (farDistance a n p) ≤ farWeight a n := by
  have hd := farDistance_ge_period ha n hx hy
  have hden : farDenominator a ≤ 1 - Real.exp (-2 * farDistance a n p) := by
    unfold farDenominator
    exact sub_le_sub_left (Real.exp_le_exp.mpr (by nlinarith)) 1
  have hexp : Real.exp (-farDistance a n p / 2) ≤
      Real.exp (-(((n : ℝ) + 1) * (2 * a)) / 2) := by
    apply Real.exp_le_exp.mpr
    linarith [farDistance_lower n hx hy]
  have hident : Real.exp (-(((n : ℝ) + 1) * (2 * a)) / 2) =
      farRatio a * farRatio a ^ n := by
    rw [show -(((n : ℝ) + 1) * (2 * a)) / 2 = -a + (n : ℝ) * (-a) by ring,
      Real.exp_add, Real.exp_nat_mul]
    rfl
  calc
    _ = Real.exp (-farDistance a n p / 2) /
        (1 - Real.exp (-2 * farDistance a n p)) := rfl
    _ ≤ Real.exp (-(((n : ℝ) + 1) * (2 * a)) / 2) / farDenominator a :=
      div_le_div₀ (Real.exp_pos _).le hexp (farDenominator_pos ha) hden
    _ = farWeight a n := by rw [hident]; unfold farWeight; ring

private theorem farCutoffKernel_nonneg {a ε : ℝ} (ha : 0 < a)
    {p : ℝ × ℝ} (n : ℕ)
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    0 ≤ farCutoffKernel a ε n p := by
  unfold farCutoffKernel
  split_ifs
  · exact (actual_density_pos (lt_of_lt_of_le (by linarith : 0 < 2 * a)
      (farDistance_ge_period ha n hx hy))).le
  · exact le_rfl

private theorem farCutoffKernel_le_weight {a ε : ℝ} (ha : 0 < a)
    {p : ℝ × ℝ} (n : ℕ)
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    farCutoffKernel a ε n p ≤ farWeight a n := by
  unfold farCutoffKernel
  split_ifs
  · exact actual_far_density_le_weight ha n hx hy
  · exact farWeight_nonneg ha n

private theorem farCutoffKernel_summable {a ε : ℝ} (ha : 0 < a)
    {p : ℝ × ℝ} (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    Summable (fun n : ℕ => farCutoffKernel a ε n p) := by
  apply (farWeight_summable ha).of_norm_bounded
  intro n
  rw [Real.norm_of_nonneg (farCutoffKernel_nonneg ha n hx hy)]
  exact farCutoffKernel_le_weight ha n hx hy

private def actualFarKernel (a ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  (∑' n : ℕ, farCutoffKernel a ε n p) +
    ∑' n : ℕ, farCutoffKernel a ε n p.swap

private theorem actualFarKernel_nonneg {a ε : ℝ} (ha : 0 < a)
    {p : ℝ × ℝ} (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    0 ≤ actualFarKernel a ε p := by
  exact add_nonneg (tsum_nonneg fun n => farCutoffKernel_nonneg ha n hx hy)
    (tsum_nonneg fun n => farCutoffKernel_nonneg ha n hy hx)

private theorem actualFarKernel_le_Ctail {a ε : ℝ} (ha : 0 < a)
    {p : ℝ × ℝ} (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    actualFarKernel a ε p ≤ actualCtail a := by
  calc
    _ ≤ (∑' n : ℕ, farWeight a n) + ∑' n : ℕ, farWeight a n := by
      exact add_le_add
        ((farCutoffKernel_summable ha hx hy).tsum_le_tsum
          (fun n => farCutoffKernel_le_weight ha n hx hy) (farWeight_summable ha))
        ((farCutoffKernel_summable ha hy hx).tsum_le_tsum
          (fun n => farCutoffKernel_le_weight ha n hy hx) (farWeight_summable ha))
    _ = actualCtail a := by rw [← two_mul, two_farWeight_tsum ha]

/-- All far-image cutoff masks are simultaneously one below the period. -/
private theorem actualFarKernel_eq_of_small {a ε : ℝ} (ha : 0 < a)
    (hε : ε < 2 * a) {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    actualFarKernel a ε p = actualFarKernel a 0 p := by
  have hmask (n : ℕ) {q : ℝ × ℝ}
      (hqx : q.1 ∈ Ioo (-a) a) (hqy : q.2 ∈ Ioo (-a) a) :
      farCutoffKernel a ε n q = farCutoffKernel a 0 n q := by
    have hd := farDistance_ge_period ha n hqx hqy
    simp [farCutoffKernel, lt_of_lt_of_le hε hd,
      lt_of_lt_of_le (by linarith : 0 < 2 * a) hd]
  unfold actualFarKernel
  congr 1 <;> apply tsum_congr <;> intro n
  · exact hmask n hx hy
  · exact hmask n hy hx

end ActualGammaCornerTransportDraft20261017


/- UNCOMPILED TRANSIENT FRAGMENT. Append after corrected stage3 and the
geometric-stage4 fragment in the same Lean file. No new assumptions supply
a kernel bound, integrability, or domain membership. -/

namespace ActualGammaCornerTransportDraft20261017

open Filter
open scoped Topology ComplexConjugate

private theorem intervalMeasure_mass (a : ℝ) (ha : 0 < a) :
    (intervalMeasure a).real univ = 2 * a := by
  have hsub : a - -a = 2 * a := by ring
  simp [intervalMeasure, measureReal_def, Real.volume_Ioo, hsub, ha.le]

private theorem interval_L1_le_sqrt_energy (a : ℝ) (ha : 0 < a)
    {u : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a)) :
    (∫ x, ‖u x‖ ∂intervalMeasure a) ≤
      Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) * Real.sqrt (2 * a) := by
  have hU : MemLp u (ENNReal.ofReal (2 : ℝ)) (intervalMeasure a) := by
    simpa using hu
  have hOne : MemLp (fun _ : ℝ => (1 : ℂ))
      (ENNReal.ofReal (2 : ℝ)) (intervalMeasure a) := memLp_const _
  have hHolder := integral_mul_norm_le_Lp_mul_Lq
    Real.HolderConjugate.two_two hU hOne
  simpa only [norm_one, mul_one, Real.rpow_two, one_pow, integral_const,
    smul_eq_mul, mul_one, ← Real.sqrt_eq_rpow, intervalMeasure_mass a ha] using hHolder

private def normProduct (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ‖u p.1‖ * ‖v p.2‖

private theorem normProduct_integrable (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (normProduct u v) ((intervalMeasure a).prod (intervalMeasure a)) := by
  exact (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) hu).norm.mul_prod
    (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) hv).norm

private theorem normProduct_integral_le (a : ℝ) (ha : 0 < a)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    (∫ p, normProduct u v p ∂(intervalMeasure a).prod (intervalMeasure a)) ≤
      (2 * a) * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
        Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a) := by
  change (∫ p : ℝ × ℝ, ‖u p.1‖ * ‖v p.2‖
      ∂(intervalMeasure a).prod (intervalMeasure a)) ≤ _
  rw [integral_prod_mul (fun x : ℝ => ‖u x‖) (fun y : ℝ => ‖v y‖)]
  calc
    _ ≤ (Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) * Real.sqrt (2 * a)) *
        (Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a) * Real.sqrt (2 * a)) :=
      mul_le_mul (interval_L1_le_sqrt_energy a ha hu)
        (interval_L1_le_sqrt_energy a ha hv)
        (integral_nonneg fun y => norm_nonneg (v y))
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = (Real.sqrt (2 * a)) ^ 2 *
        Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
        Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a) := by ring
    _ = _ := by rw [Real.sq_sqrt (by linarith : 0 ≤ 2 * a)]

private def actualFarPair (a ε : ℝ) (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  conj (u p.1) * (actualFarKernel a ε p : ℂ) * v p.2

private theorem actualFarKernel_measurable (a ε : ℝ) :
    Measurable (actualFarKernel a ε) := by
  have hTerm (n : ℕ) : Measurable (farCutoffKernel a ε n) := by
    have hd : Measurable (farDistance a n) := by unfold farDistance; fun_prop
    unfold farCutoffKernel
    exact Measurable.ite (measurableSet_lt measurable_const hd)
      (actual_density_measurable.comp hd) measurable_const
  exact (Measurable.tsum hTerm).add
    (Measurable.tsum fun n => (hTerm n).comp measurable_swap)

private theorem actualFarPair_aestronglyMeasurable (a ε : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    AEStronglyMeasurable (actualFarPair a ε u v)
      ((intervalMeasure a).prod (intervalMeasure a)) := by
  have hK : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (actualFarKernel a ε p : ℂ))
      ((intervalMeasure a).prod (intervalMeasure a)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (actualFarKernel_measurable a ε).aestronglyMeasurable
  exact ((Complex.continuous_conj.comp_aestronglyMeasurable hu.aestronglyMeasurable.comp_fst).mul hK).mul
    hv.aestronglyMeasurable.comp_snd

private theorem actualFarPair_norm_le {a ε : ℝ} (ha : 0 < a)
    {u v : ℝ → ℂ} {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    ‖actualFarPair a ε u v p‖ ≤ actualCtail a * normProduct u v p := by
  unfold actualFarPair
  rw [norm_mul, norm_mul, Complex.norm_conj,
    Complex.norm_of_nonneg (actualFarKernel_nonneg ha hx hy)]
  calc
    _ ≤ ‖u p.1‖ * actualCtail a * ‖v p.2‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (actualFarKernel_le_Ctail ha hx hy)
          (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by unfold normProduct; ring

private theorem actualFarPair_integrable_and_le (a ε : ℝ) (ha : 0 < a)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (actualFarPair a ε u v) ((intervalMeasure a).prod (intervalMeasure a)) ∧
    (∫ p, ‖actualFarPair a ε u v p‖ ∂(intervalMeasure a).prod (intervalMeasure a)) ≤
      actualCtail a * ((2 * a) * Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂intervalMeasure a) *
        Real.sqrt (∫ y, ‖v y‖ ^ 2 ∂intervalMeasure a)) := by
  have hDom := (normProduct_integrable a hu hv).const_mul (actualCtail a)
  have hLe : ∀ᵐ p ∂(intervalMeasure a).prod (intervalMeasure a),
      ‖actualFarPair a ε u v p‖ ≤ actualCtail a * normProduct u v p := by
    filter_upwards [interval_product_membership a] with p hp
    exact actualFarPair_norm_le ha hp.1 hp.2
  have hInt := hDom.mono' (actualFarPair_aestronglyMeasurable a ε hu hv) hLe
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ p, actualCtail a * normProduct u v p
        ∂(intervalMeasure a).prod (intervalMeasure a) :=
      integral_mono_ae hInt.norm hDom hLe
    _ = actualCtail a * ∫ p, normProduct u v p
        ∂(intervalMeasure a).prod (intervalMeasure a) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (normProduct_integral_le a ha hu hv)
      (actualCtail_nonneg ha)

private theorem actualFarPair_eq_of_small {a ε : ℝ} (ha : 0 < a)
    (hε : ε < 2 * a) {u v : ℝ → ℂ} {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    actualFarPair a ε u v p = actualFarPair a 0 u v p := by
  unfold actualFarPair
  rw [actualFarKernel_eq_of_small ha hε hx hy]

end ActualGammaCornerTransportDraft20261017


/- UNCOMPILED TRANSIENT FRAGMENT. Append after corrected stage3,
geometric-stage4, and L1-stage5-v2 in one file. This segment uses the entire
actual integer image sum, not only the two endpoint corners. -/

namespace ActualGammaCornerTransportDraft20261017

open Filter
open scoped Topology ComplexConjugate

private def integerImageTerm (a ε : ℝ) (m : ℤ) (p : ℝ × ℝ) : ℝ :=
  if m = 0 then 0 else
    if ε < |p.1 - p.2 + m • (2 * a)| then
      actualDensity |p.1 - p.2 + m • (2 * a)| else 0

private def integerImageKernel (a ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  ∑' m : ℤ, integerImageTerm a ε m p

private def integerImagePair (a ε : ℝ) (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  conj (u p.1) * (integerImageKernel a ε p : ℂ) * v p.2

private theorem integerImageTerm_pos_far {a ε : ℝ} (ha : 0 < a)
    {p : ℝ × ℝ} (n : ℕ)
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    integerImageTerm a ε ((n + 2 : ℕ) : ℤ) p = farCutoffKernel a ε n p := by
  have hn : ((n + 2 : ℕ) : ℤ) ≠ 0 := by omega
  have hd : 0 < farDistance a n p :=
    lt_of_lt_of_le (by linarith : 0 < 2 * a) (farDistance_ge_period ha n hx hy)
  have harg : p.1 - p.2 + ((n + 2 : ℕ) : ℤ) • (2 * a) =
      farDistance a n p := by
    simp [farDistance, zsmul_eq_mul, Nat.cast_add]
  simp only [integerImageTerm, hn, ↓reduceIte, harg, abs_of_pos hd, farCutoffKernel]

private theorem integerImageTerm_neg_far {a ε : ℝ} (ha : 0 < a)
    {p : ℝ × ℝ} (n : ℕ)
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    integerImageTerm a ε (-((n + 2 : ℕ) : ℤ)) p =
      farCutoffKernel a ε n p.swap := by
  have hn : -((n + 2 : ℕ) : ℤ) ≠ 0 := by omega
  have hd : 0 < farDistance a n p.swap :=
    lt_of_lt_of_le (by linarith : 0 < 2 * a) (farDistance_ge_period ha n hy hx)
  have harg : p.1 - p.2 + (-((n + 2 : ℕ) : ℤ)) • (2 * a) =
      -farDistance a n p.swap := by
    simp [farDistance, zsmul_eq_mul, Nat.cast_add]
    ring
  simp only [integerImageTerm, hn, ↓reduceIte, harg, abs_neg, abs_of_pos hd,
    farCutoffKernel]

private theorem integerImageTerm_one {a ε : ℝ} {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    integerImageTerm a ε 1 p =
      if ε < plusDistance a p then actualDensity (plusDistance a p) else 0 := by
  simp only [integerImageTerm, one_ne_zero, ↓reduceIte, one_zsmul]
  change (if ε < |plusDistance a p| then actualDensity |plusDistance a p| else 0) = _
  rw [abs_of_pos (distances_pos hx hy).1]

private theorem integerImageTerm_neg_one {a ε : ℝ} {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    integerImageTerm a ε (-1) p =
      if ε < minusDistance a p then actualDensity (minusDistance a p) else 0 := by
  have harg : p.1 - p.2 + (-1 : ℤ) • (2 * a) = -minusDistance a p := by
    simp only [neg_one_zsmul]
    unfold minusDistance
    ring
  simp only [integerImageTerm, neg_ne_zero.mpr one_ne_zero, ↓reduceIte, harg,
    abs_neg, abs_of_pos (distances_pos hx hy).2]

/-- Summability is proved for the actual whole lattice before rearranging
its tsum. The two Nat tails are exactly + (n+2) and - (n+2). -/
private theorem integerImageKernel_split {a ε : ℝ} (ha : 0 < a)
    {p : ℝ × ℝ} (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    Summable (fun m : ℤ => integerImageTerm a ε m p) ∧
    integerImageKernel a ε p =
      (if ε < plusDistance a p then actualDensity (plusDistance a p) else 0) +
      (if ε < minusDistance a p then actualDensity (minusDistance a p) else 0) +
      actualFarKernel a ε p := by
  let F : ℤ → ℝ := fun m => integerImageTerm a ε m p
  have hPosTerm (n : ℕ) : F ((n + 2 : ℕ) : ℤ) = farCutoffKernel a ε n p :=
    integerImageTerm_pos_far ha n hx hy
  have hNegTerm (n : ℕ) : F (-(((n + 1 : ℕ) : ℤ) + 1)) =
      farCutoffKernel a ε n p.swap := by
    have hidx : -(((n + 1 : ℕ) : ℤ) + 1) = -((n + 2 : ℕ) : ℤ) := by omega
    rw [hidx]
    exact integerImageTerm_neg_far ha n hx hy
  have hPos : Summable (fun n : ℕ => F (n : ℤ)) := by
    apply Summable.comp_nat_add (k := 2)
    exact (farCutoffKernel_summable ha hx hy).congr fun n => (hPosTerm n).symm
  have hNeg : Summable (fun n : ℕ => F (-((n : ℤ) + 1))) := by
    apply Summable.comp_nat_add (k := 1)
    exact (farCutoffKernel_summable ha hy hx).congr fun n => (hNegTerm n).symm
  have hAll : Summable F := hPos.of_nat_of_neg_add_one hNeg
  have hPosSum : (∑' n : ℕ, F (n : ℤ)) =
      (F 0 + F 1) + ∑' n : ℕ, farCutoffKernel a ε n p := by
    rw [← hPos.sum_add_tsum_nat_add 2]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.cast_zero, Nat.cast_one, hPosTerm]
  have hNegSum : (∑' n : ℕ, F (-((n : ℤ) + 1))) =
      F (-1) + ∑' n : ℕ, farCutoffKernel a ε n p.swap := by
    rw [hNeg.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_add, hNegTerm]
  refine ⟨hAll, ?_⟩
  change (∑' m : ℤ, F m) = _
  rw [tsum_of_nat_of_neg_add_one hPos hNeg, hPosSum, hNegSum]
  have hzero : F 0 = 0 := by simp [F, integerImageTerm]
  have hone := integerImageTerm_one (ε := ε) hx hy
  have hnegone := integerImageTerm_neg_one (ε := ε) hx hy
  change F 1 = _ at hone
  change F (-1) = _ at hnegone
  rw [hzero, hone, hnegone]
  unfold actualFarKernel
  ring

private theorem integerImagePair_split {a ε : ℝ} (ha : 0 < a)
    {u v : ℝ → ℂ} {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    integerImagePair a ε u v p =
      twoCornerCutoffPair a ε u v p + actualFarPair a ε u v p := by
  unfold integerImagePair
  rw [(integerImageKernel_split ha hx hy).2]
  unfold twoCornerCutoffPair actualFarPair plusPair minusPair
  by_cases hp : ε < plusDistance a p <;>
    by_cases hm : ε < minusDistance a p <;>
      simp [hp, hm] <;> ring

private def fullImageMajorant (a : ℝ) (u v : ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  twoCornerMajorant a u v p + actualCtail a * normProduct u v p

private theorem fullImageMajorant_integrable (a : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (fullImageMajorant a u v)
      ((intervalMeasure a).prod (intervalMeasure a)) := by
  exact (twoCornerMajorant_integrable a hu hv).add
    ((normProduct_integrable a hu hv).const_mul (actualCtail a))

private theorem integerImagePair_norm_le {a ε : ℝ} (ha : 0 < a)
    {u v : ℝ → ℂ} {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    ‖integerImagePair a ε u v p‖ ≤ fullImageMajorant a u v p := by
  rw [integerImagePair_split ha hx hy]
  exact (norm_add_le _ _).trans (add_le_add
    (twoCornerCutoffPair_norm_le hx hy) (actualFarPair_norm_le ha hx hy))

private theorem integerImageKernel_measurable (a ε : ℝ) :
    Measurable (integerImageKernel a ε) := by
  apply Measurable.tsum
  intro m
  unfold integerImageTerm
  by_cases hm : m = 0
  · simp only [hm, ↓reduceIte]
    exact measurable_const
  · simp only [hm, ↓reduceIte]
    have hD : Measurable (fun p : ℝ × ℝ => |p.1 - p.2 + m • (2 * a)|) := by
      fun_prop
    exact Measurable.ite (measurableSet_lt measurable_const hD)
      (actual_density_measurable.comp hD) measurable_const

private theorem integerImagePair_aestronglyMeasurable (a ε : ℝ)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    AEStronglyMeasurable (integerImagePair a ε u v)
      ((intervalMeasure a).prod (intervalMeasure a)) := by
  have hK : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (integerImageKernel a ε p : ℂ))
      ((intervalMeasure a).prod (intervalMeasure a)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (integerImageKernel_measurable a ε).aestronglyMeasurable
  exact ((Complex.continuous_conj.comp_aestronglyMeasurable hu.aestronglyMeasurable.comp_fst).mul hK).mul
    hv.aestronglyMeasurable.comp_snd

private theorem integerImagePair_integrable (a ε : ℝ) (ha : 0 < a)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Integrable (integerImagePair a ε u v)
      ((intervalMeasure a).prod (intervalMeasure a)) := by
  apply (fullImageMajorant_integrable a hu hv).mono'
    (integerImagePair_aestronglyMeasurable a ε hu hv)
  filter_upwards [interval_product_membership a] with p hp
  exact integerImagePair_norm_le ha hp.1 hp.2

private theorem integerImagePair_tendsto {a : ℝ} (ha : 0 < a)
    {u v : ℝ → ℂ} {p : ℝ × ℝ}
    (hx : p.1 ∈ Ioo (-a) a) (hy : p.2 ∈ Ioo (-a) a) :
    Tendsto (fun ε : ℝ => integerImagePair a ε u v p)
      (𝓝[Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 (integerImagePair a 0 u v p)) := by
  have hd := distances_pos hx hy
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[Ioi (0 : ℝ)] (0 : ℝ),
      ε < min (min (plusDistance a p) (minusDistance a p)) (2 * a) :=
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (lt_min (lt_min hd.1 hd.2) (by linarith)))
  apply (tendsto_const_nhds (x := integerImagePair a 0 u v p)).congr'
  filter_upwards [hsmall] with ε hε
  have hp : ε < plusDistance a p := lt_of_lt_of_le hε
    ((min_le_left _ _).trans (min_le_left _ _))
  have hm : ε < minusDistance a p := lt_of_lt_of_le hε
    ((min_le_left _ _).trans (min_le_right _ _))
  have he : ε < 2 * a := lt_of_lt_of_le hε (min_le_right _ _)
  rw [integerImagePair_split ha hx hy, integerImagePair_split ha hx hy,
    actualFarPair_eq_of_small ha he hx hy]
  simp [twoCornerCutoffPair, hp, hm, hd.1, hd.2]

private theorem integerImagePair_integral_tendsto (a : ℝ) (ha : 0 < a)
    {u v : ℝ → ℂ} (hu : MemLp u 2 (intervalMeasure a))
    (hv : MemLp v 2 (intervalMeasure a)) :
    Tendsto
      (fun ε : ℝ => ∫ p, integerImagePair a ε u v p
        ∂(intervalMeasure a).prod (intervalMeasure a))
      (𝓝[Ioi (0 : ℝ)] (0 : ℝ))
      (𝓝 (∫ p, integerImagePair a 0 u v p
        ∂(intervalMeasure a).prod (intervalMeasure a))) := by
  apply tendsto_integral_filter_of_dominated_convergence (fullImageMajorant a u v)
  · exact Eventually.of_forall fun ε =>
      (integerImagePair_integrable a ε ha hu hv).aestronglyMeasurable
  · apply Eventually.of_forall
    intro ε
    filter_upwards [interval_product_membership a] with p hp
    exact integerImagePair_norm_le ha hp.1 hp.2
  · exact fullImageMajorant_integrable a hu hv
  · filter_upwards [interval_product_membership a] with p hp
    exact integerImagePair_tendsto ha hp.1 hp.2

-- The full ℤ-image pairing is integrable, and its actual common-epsilon
-- integral has the required limit for every original interval L2 pair.
example (a : ℝ) (ha : 0 < a) {u v : ℝ → ℂ}
    (hu : MemLp u 2 (intervalMeasure a)) (hv : MemLp v 2 (intervalMeasure a)) :
    (∀ ε : ℝ, Integrable (integerImagePair a ε u v)
      ((intervalMeasure a).prod (intervalMeasure a))) ∧
    Tendsto
      (fun ε : ℝ => ∫ p, integerImagePair a ε u v p
        ∂(intervalMeasure a).prod (intervalMeasure a))
      (𝓝[Ioi (0 : ℝ)] (0 : ℝ))
      (𝓝 (∫ p, integerImagePair a 0 u v p
        ∂(intervalMeasure a).prod (intervalMeasure a))) :=
  ⟨(fun ε => integerImagePair_integrable a ε ha hu hv),
    integerImagePair_integral_tendsto a ha hu hv⟩

end ActualGammaCornerTransportDraft20261017


/- UNCOMPILED TRANSIENT FRAGMENT. Append after corrected stage3 and
far-image stages4-v2/5-v2/6. This supplies the full boundary limit on the
same Ioc carrier as ActualGammaDomainPassage.actual-energies, with d=2a. -/

namespace ActualGammaCornerTransportDraft20261017

open Filter
open scoped Topology ComplexConjugate

private def actualIocBoundaryPair (a ε : ℝ) (u : ℝ → ℂ) : ℝ :=
  (∫ p : ℝ × ℝ, conj (u p.1) *
    ((∑' m : ℤ, if m = 0 then 0 else
      if ε < |p.1 - p.2 + m • (2 * a)| then
        actualDensity |p.1 - p.2 + m • (2 * a)| else 0) : ℂ) * u p.2
    ∂(volume.restrict (Ioc (-a) a)).prod (volume.restrict (Ioc (-a) a))).re

private theorem actualIocBoundaryPair_tendsto (a : ℝ) (ha : 0 < a)
    {u : ℝ → ℂ} (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    Tendsto (fun ε : ℝ => actualIocBoundaryPair a ε u)
      (𝓝[Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 (actualIocBoundaryPair a 0 u)) := by
  have hμ : intervalMeasure a = volume.restrict (Ioc (-a) a) :=
    restrict_Ioo_eq_restrict_Ioc
  have hu' : MemLp u 2 (intervalMeasure a) := by rw [hμ]; exact hu
  have hkernel (ε : ℝ) (p : ℝ × ℝ) :
      (integerImageKernel a ε p : ℂ) =
        ∑' m : ℤ, if m = 0 then (0 : ℂ) else
          if ε < |p.1 - p.2 + m • (2 * a)| then
            (actualDensity |p.1 - p.2 + m • (2 * a)| : ℂ) else 0 := by
    unfold integerImageKernel
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro m
    by_cases hm : m = 0
    · simp only [integerImageTerm, hm, ↓reduceIte, Complex.ofReal_zero]
    · simp only [integerImageTerm, hm, ↓reduceIte]
      split_ifs <;> rfl
  have hDCT := integerImagePair_integral_tendsto a ha hu' hu'
  have hReal := (Complex.continuous_re.tendsto _).comp hDCT
  simpa only [actualIocBoundaryPair, integerImagePair, hμ, hkernel,
    Function.comp_def] using hReal

private theorem actualIocBoundaryPair_nat_tendsto (a : ℝ) (ha : 0 < a)
    {u : ℝ → ℂ} (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    Tendsto
      (fun n : ℕ => actualIocBoundaryPair a (1 / ((n : ℝ) + 1)) u)
      atTop (𝓝 (actualIocBoundaryPair a 0 u)) := by
  have hε : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop
      (𝓝[Ioi (0 : ℝ)] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Eventually.of_forall fun n => by change 0 < 1 / ((n : ℝ) + 1); positivity
  exact (actualIocBoundaryPair_tendsto a ha hu).comp hε

-- This is the full actual integer-image boundary limit. To instantiate
-- ActualGammaDomainPassageDraft's d,t notation, take d=2a and t=-a;
-- (-a)+(2a)=a. The centered-Ioc measure equality above is exact, not a
-- pointwise endpoint identification of arbitrary L2 representatives.
example (a : ℝ) (ha : 0 < a)
    {u : ℝ → ℂ} (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    Tendsto
      (fun n : ℕ => actualIocBoundaryPair a (1 / ((n : ℝ) + 1)) u)
      atTop (𝓝 (actualIocBoundaryPair a 0 u)) :=
  actualIocBoundaryPair_nat_tendsto a ha hu

end ActualGammaCornerTransportDraft20261017

/-
TRANSIENT, UNCOMPILED CANDIDATE. No kernel acceptance claimed.
Pinned Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d.
These are bind-only exact applications and normalization steps for the actual
common-cutoff consumer, not a new standalone content/escape witness.
This assembled candidate includes the final all-L2 common-cutoff proof script.
It is UNCOMPILED and establishes no formal acceptance until the actual check passes.
-/

noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate ENNReal

namespace ActualGammaCommonCutoffDraft20261017

private abbrev density :=
  D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity

private def zeroExtension (d t : ℝ) (u : ℝ → ℂ) : ℝ → ℂ :=
  (Ioc t (t + d)).indicator u

private def periodicExtension (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (z : ℝ) : ℂ := AddCircle.liftIoc d t u (z : AddCircle d)

/-- There is one exact half-open copy, including at every endpoint. -/
private theorem periodic_copy_and_zero_cancellation
    (d t : ℝ) [hd : Fact (0 < d)] (u : ℝ → ℂ) (z : ℝ) :
    periodicExtension d t u z =
      (∑' m : ℤ, zeroExtension d t u (z + m • d)) ∧
    periodicExtension d t u z - zeroExtension d t u z =
      ∑' m : ℤ, if m = 0 then 0 else zeroExtension d t u (z + m • d) := by
  classical
  obtain ⟨m, hm, hUnique⟩ := existsUnique_add_zsmul_mem_Ioc hd.out z t
  have hOnly (n : ℤ) (hn : n ≠ m) :
      zeroExtension d t u (z + n • d) = 0 := by
    apply Set.indicator_of_notMem
    intro hmem
    exact hn (hUnique n hmem)
  have hCoe : ((z + m • d : ℝ) : AddCircle d) = (z : AddCircle d) := by
    rw [AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period,
      smul_zero, add_zero]
  have hLift : periodicExtension d t u z = zeroExtension d t u (z + m • d) := by
    have h := AddCircle.liftIoc_coe_apply (p := d) (a := t) (f := u) hm
    rw [hCoe] at h
    simpa only [periodicExtension, zeroExtension, Set.indicator_of_mem hm] using h
  have hSum : (∑' n : ℤ, zeroExtension d t u (z + n • d)) =
      zeroExtension d t u (z + m • d) := tsum_eq_single m hOnly
  have hSumNonzero :
      (∑' n : ℤ, if n = 0 then 0 else zeroExtension d t u (z + n • d)) =
        if m = 0 then 0 else zeroExtension d t u (z + m • d) := by
    apply tsum_eq_single m
    intro n hn
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [if_neg hn0, hOnly n hn]
  refine ⟨hLift.trans hSum.symm, ?_⟩
  rw [hLift, hSumNonzero]
  by_cases hm0 : m = 0
  · subst m
    simp
  · have hz : zeroExtension d t u z = 0 := by
      simpa using hOnly 0 (Ne.symm hm0)
    simp only [if_neg hm0, hz, sub_zero]

/-- The same epsilon is applied to the signed shift and to every image. -/
private def cutoffKernel (ε s : ℝ) : ℝ :=
  if ε < |s| then density |s| else 0

example (d t ε : ℝ) [Fact (0 < d)] (u : ℝ → ℂ) (x s : ℝ) :
    (cutoffKernel ε s : ℂ) * conj (u x) *
        (periodicExtension d t u (x - s) - zeroExtension d t u (x - s)) =
      ∑' m : ℤ, if m = 0 then 0 else
        (cutoffKernel ε s : ℂ) * conj (u x) *
          zeroExtension d t u (x - s + m • d) := by
  rw [(periodic_copy_and_zero_cancellation d t u (x - s)).2]
  calc
    _ = ∑' m : ℤ, ((cutoffKernel ε s : ℂ) * conj (u x)) *
        (if m = 0 then 0 else zeroExtension d t u (x - s + m • d)) :=
      (tsum_mul_left).symm
    _ = _ := tsum_congr fun m => by split_ifs <;> simp

-- y = x - s + m*d gives s = x - y + m*d, with no epsilon change.
example (d ε x s : ℝ) (m : ℤ) :
    cutoffKernel ε (x - (x - s + m • d) + m • d) = cutoffKernel ε s := by
  congr 1
  ring

-- This coefficient 2 and the minus sign are retained in both carrier energies.
example (z w : ℂ) : Complex.normSq (z - w) =
    Complex.normSq z + Complex.normSq w - 2 * (conj z * w).re := by
  simp only [Complex.normSq_sub, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

-- Actual Gamma tail integrability follows from epsilon > 0, not a premise.
private theorem actual_density_tail_integrable {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn density (Ioi ε) := by
  let D : ℝ := 1 - Real.exp (-2 * ε)
  have hD : 0 < D := by
    dsimp only [D]
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hExp : IntegrableOn (fun s : ℝ => Real.exp (-s / 2)) (Ioi ε) := by
    convert integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) ε using 1
    ext s
    congr 1
    ring
  have hDom := hExp.div_const D
  have hMeas : Measurable density := by
    change Measurable (fun x : ℝ => Real.exp (-x / 2) / (1 - Real.exp (-2 * x)))
    fun_prop
  apply hDom.mono' hMeas.aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  have hs' : ε < s := hs
  have hDen : D ≤ 1 - Real.exp (-2 * s) := by
    dsimp only [D]
    have he : Real.exp (-2 * s) ≤ Real.exp (-2 * ε) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have hDs : 0 < 1 - Real.exp (-2 * s) := hD.trans_le hDen
  have hk : 0 ≤ density s := by
    exact div_nonneg (Real.exp_pos _).le hDs.le
  rw [Real.norm_of_nonneg hk]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hD hDen


/-- The actual Gamma density is nonnegative on positive arguments. -/
private theorem actual_density_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ density s := by
  have hden : 0 < 1 - Real.exp (-2 * s) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  exact div_nonneg (Real.exp_pos _).le hden.le

/-- Removing the central copy either removes the whole value or removes zero. -/
private theorem periodic_minus_zero_norm_le
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ) (z : ℝ) :
    ‖periodicExtension d t u z - zeroExtension d t u z‖ ≤
      ‖periodicExtension d t u z‖ := by
  by_cases hz : z ∈ Ioc t (t + d)
  · have hlift := AddCircle.liftIoc_coe_apply (p := d) (a := t) (f := u) hz
    simp only [periodicExtension, zeroExtension, Set.indicator_of_mem hz, hlift,
      sub_self, norm_zero, norm_nonneg]
  · simp only [zeroExtension, Set.indicator_of_notMem hz, sub_zero, le_refl]

/-- A chosen half-open copy supplies both the lift value and every other copy's zero. -/
private theorem periodic_copy_at_mem
    (d t : ℝ) [hd : Fact (0 < d)] (u : ℝ → ℂ) (z : ℝ) (m : ℤ)
    (hm : z + m • d ∈ Ioc t (t + d)) :
    periodicExtension d t u z = zeroExtension d t u (z + m • d) ∧
      ∀ n : ℤ, n ≠ m → zeroExtension d t u (z + n • d) = 0 := by
  obtain ⟨j, hj, hUnique⟩ := existsUnique_add_zsmul_mem_Ioc hd.out z t
  have hmj : m = j := hUnique m hm
  have hOnly (n : ℤ) (hn : n ≠ m) :
      zeroExtension d t u (z + n • d) = 0 := by
    apply Set.indicator_of_notMem
    intro hmem
    exact hn ((hUnique n hmem).trans hmj.symm)
  refine ⟨?_, hOnly⟩
  have hCoe : ((z + m • d : ℝ) : AddCircle d) = (z : AddCircle d) := by
    rw [AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period,
      smul_zero, add_zero]
  have h := AddCircle.liftIoc_coe_apply (p := d) (a := t) (f := u) hm
  rw [hCoe] at h
  simpa only [periodicExtension, zeroExtension, Set.indicator_of_mem hm] using h

/-- Absolute values also have exactly one copy; this is the Tonelli input. -/
private theorem weighted_mask_enorm_tsum
    (d t : ℝ) [hd : Fact (0 < d)] (u : ℝ → ℂ) (z : ℝ) (c : ℂ) :
    (∑' m : ℤ, ‖if m = 0 then 0 else c * zeroExtension d t u (z + m • d)‖ₑ) =
      ‖c * (periodicExtension d t u z - zeroExtension d t u z)‖ₑ := by
  classical
  obtain ⟨m, hm, _⟩ := existsUnique_add_zsmul_mem_Ioc hd.out z t
  obtain ⟨hlift, hOnly⟩ := periodic_copy_at_mem d t u z m hm
  have hDiff : periodicExtension d t u z - zeroExtension d t u z =
      if m = 0 then 0 else zeroExtension d t u (z + m • d) := by
    rw [hlift]
    by_cases hm0 : m = 0
    · subst m
      simp
    · have hz : zeroExtension d t u z = 0 := by
        simpa using hOnly 0 (Ne.symm hm0)
      simp only [if_neg hm0, hz, sub_zero]
  rw [tsum_eq_single m, hDiff]
  · split_ifs <;> simp
  · intro n hnm
    by_cases hn0 : n = 0
    · simp only [if_pos hn0, enorm_zero]
    · simp only [if_neg hn0, hOnly n hnm, mul_zero, enorm_zero]

private abbrev windowMeasure (d t : ℝ) : Measure ℝ :=
  volume.restrict (Ioc t (t + d))

-- Product coordinates in these definitions are (x,s), not (s,x).
private def differenceCorrelation
    (d t ε : ℝ) [Fact (0 < d)] (u : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (cutoffKernel ε p.2 : ℂ) * conj (u p.1) *
    (periodicExtension d t u (p.1 - p.2) - zeroExtension d t u (p.1 - p.2))

private def latticeCopy (d t ε : ℝ) (u : ℝ → ℂ) (m : ℤ) (p : ℝ × ℝ) : ℂ :=
  if m = 0 then 0 else
    (cutoffKernel ε p.2 : ℂ) * conj (u p.1) *
      zeroExtension d t u (p.1 - p.2 + m • d)

private def imageCopy (d ε : ℝ) (u : ℝ → ℂ) (m : ℤ) (p : ℝ × ℝ) : ℂ :=
  if m = 0 then 0 else
    (cutoffKernel ε (p.1 - p.2 + m • d) : ℂ) * conj (u p.1) * u p.2

private def imageKernel (d ε x y : ℝ) : ℝ :=
  ∑' m : ℤ, if m = 0 then 0 else cutoffKernel ε (x - y + m • d)

private theorem latticeCopy_tsum
    (d t ε : ℝ) [Fact (0 < d)] (u : ℝ → ℂ) (p : ℝ × ℝ) :
    (∑' m : ℤ, latticeCopy d t ε u m p) = differenceCorrelation d t ε u p := by
  simp only [latticeCopy, differenceCorrelation]
  rw [(periodic_copy_and_zero_cancellation d t u (p.1 - p.2)).2]
  rw [← tsum_mul_left]
  exact tsum_congr fun m => by split_ifs <;> simp

private theorem latticeCopy_enorm_tsum
    (d t ε : ℝ) [Fact (0 < d)] (u : ℝ → ℂ) (p : ℝ × ℝ) :
    (∑' m : ℤ, ‖latticeCopy d t ε u m p‖ₑ) =
      ‖differenceCorrelation d t ε u p‖ₑ := by
  exact weighted_mask_enorm_tsum d t u (p.1 - p.2)
    ((cutoffKernel ε p.2 : ℂ) * conj (u p.1))

/-- Every copy is an indicator of the same actual difference correlation.
No independent integrability premise for a copy is needed. -/
private theorem latticeCopy_eq_indicator
    (d t ε : ℝ) [hd : Fact (0 < d)] (u : ℝ → ℂ) (m : ℤ) (hm : m ≠ 0) :
    latticeCopy d t ε u m =
      {p : ℝ × ℝ | p.1 - p.2 + m • d ∈ Ioc t (t + d)}.indicator
        (differenceCorrelation d t ε u) := by
  classical
  funext p
  by_cases hp : p.1 - p.2 + m • d ∈ Ioc t (t + d)
  · have hpSet : p ∈ {q : ℝ × ℝ | q.1 - q.2 + m • d ∈ Ioc t (t + d)} := hp
    obtain ⟨hlift, hOnly⟩ := periodic_copy_at_mem d t u (p.1 - p.2) m hp
    have hzero : zeroExtension d t u (p.1 - p.2) = 0 := by
      simpa using hOnly 0 (Ne.symm hm)
    simp only [latticeCopy, if_neg hm, Set.indicator_of_mem hpSet,
      differenceCorrelation, hlift, hzero, sub_zero]
  · have hpSet : p ∉ {q : ℝ × ℝ | q.1 - q.2 + m • d ∈ Ioc t (t + d)} := hp
    simp only [latticeCopy, if_neg hm, zeroExtension,
      Set.indicator_of_notMem hp, Set.indicator_of_notMem hpSet, mul_zero]

private theorem latticeCopy_integrable
    (d t ε : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hF : Integrable (differenceCorrelation d t ε u)
      ((windowMeasure d t).prod volume)) (m : ℤ) :
    Integrable (latticeCopy d t ε u m) ((windowMeasure d t).prod volume) := by
  classical
  by_cases hm : m = 0
  · subst m
    change Integrable (fun _ : ℝ × ℝ => (0 : ℂ)) ((windowMeasure d t).prod volume)
    exact integrable_zero (ℝ × ℝ) ℂ ((windowMeasure d t).prod volume)
  · rw [latticeCopy_eq_indicator d t ε u m hm]
    apply hF.indicator
    exact measurableSet_Ioc.preimage (by fun_prop)

/-- The signed-cutoff L² majorant pays the entire countable Tonelli sum. -/
private theorem latticeCopy_lintegral_norm_sum_ne_top
    (d t ε : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hF : Integrable (differenceCorrelation d t ε u)
      ((windowMeasure d t).prod volume)) :
    (∑' m : ℤ, ∫⁻ p, ‖latticeCopy d t ε u m p‖ₑ
      ∂((windowMeasure d t).prod volume)) ≠ ∞ := by
  rw [← lintegral_tsum (fun m =>
    (latticeCopy_integrable d t ε u hF m).aestronglyMeasurable.enorm)]
  simpa only [latticeCopy_enorm_tsum] using hF.hasFiniteIntegral.ne

private theorem integral_difference_eq_tsum_copies
    (d t ε : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hF : Integrable (differenceCorrelation d t ε u)
      ((windowMeasure d t).prod volume)) :
    (∫ p, differenceCorrelation d t ε u p ∂((windowMeasure d t).prod volume)) =
      ∑' m : ℤ, ∫ p, latticeCopy d t ε u m p
        ∂((windowMeasure d t).prod volume) := by
  have h := integral_tsum
    (fun m => (latticeCopy_integrable d t ε u hF m).aestronglyMeasurable)
    (latticeCopy_lintegral_norm_sum_ne_top d t ε u hF)
  simpa only [latticeCopy_tsum] using h

/-- Single-copy change of variables. This exact application is valid even before
integrability is supplied; no hidden finite-sum approximation is involved. -/
private theorem integral_lattice_copy_eq_image_slice
    (d t ε : ℝ) (u : ℝ → ℂ) (x : ℝ) (m : ℤ) :
    (∫ s : ℝ, latticeCopy d t ε u m (x, s)) =
      ∫ y in Ioc t (t + d), imageCopy d ε u m (x, y) := by
  classical
  by_cases hm : m = 0
  · subst m
    simp [latticeCopy, imageCopy]
  · let F : ℝ → ℂ := fun y =>
      (cutoffKernel ε (x - y + m • d) : ℂ) * conj (u x) * zeroExtension d t u y
    have hreflection := integral_sub_left_eq_self F volume (x + m • d)
    have harg (s : ℝ) : x - (x + m • d - s) + m • d = s := by ring
    have hpos (s : ℝ) : x + m • d - s = x - s + m • d := by ring
    have hF : F = (Ioc t (t + d)).indicator (fun y => imageCopy d ε u m (x, y)) := by
      funext y
      by_cases hy : y ∈ Ioc t (t + d)
      · simp only [F, zeroExtension, Set.indicator_of_mem hy, imageCopy, if_neg hm]
      · simp only [F, zeroExtension, Set.indicator_of_notMem hy, mul_zero]
    calc
      (∫ s : ℝ, latticeCopy d t ε u m (x, s)) =
          ∫ s : ℝ, F (x + m • d - s) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun s => by
              dsimp only [latticeCopy, F]
              rw [if_neg hm, harg, hpos]
      _ = ∫ y : ℝ, F y := hreflection
      _ = ∫ y in Ioc t (t + d), imageCopy d ε u m (x, y) := by
        rw [hF, integral_indicator measurableSet_Ioc]


private def copyReflection (d : ℝ) (m : ℤ) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun p := (p.1, p.1 + m • d - p.2)
  invFun p := (p.1, p.1 + m • d - p.2)
  left_inv := by
    rintro ⟨x, y⟩
    ext <;> dsimp <;> ring
  right_inv := by
    rintro ⟨x, y⟩
    ext <;> dsimp <;> ring
  measurable_toFun := by
    change Measurable (fun p : ℝ × ℝ => (p.1, p.1 + m • d - p.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : ℝ × ℝ => (p.1, p.1 + m • d - p.2))
    fun_prop

private theorem copyReflection_measurePreserving (d t : ℝ) (m : ℤ) :
    MeasurePreserving (copyReflection d m)
      ((windowMeasure d t).prod volume) ((windowMeasure d t).prod volume) := by
  change MeasurePreserving (fun p : ℝ × ℝ => (p.1, p.1 + m • d - p.2))
    ((windowMeasure d t).prod volume) ((windowMeasure d t).prod volume)
  exact (MeasurePreserving.id (windowMeasure d t)).skew_product
    (g := fun x y : ℝ => x + m • d - y) (by fun_prop)
    (Filter.Eventually.of_forall fun x =>
      (Measure.measurePreserving_sub_left volume (x + m • d)).map_eq)

private theorem windowMeasure_prod_windowMeasure (d t : ℝ) :
    (windowMeasure d t).prod (windowMeasure d t) =
      ((windowMeasure d t).prod volume).restrict (univ ×ˢ Ioc t (t + d)) := by
  simpa only [Measure.restrict_univ] using
    (Measure.prod_restrict (μ := windowMeasure d t) (ν := volume)
      univ (Ioc t (t + d)))

private theorem copy_reflection_eq_indicator_image
    (d t ε : ℝ) (u : ℝ → ℂ) (m : ℤ) :
    latticeCopy d t ε u m ∘ copyReflection d m =
      (univ ×ˢ Ioc t (t + d)).indicator (imageCopy d ε u m) := by
  classical
  funext p
  change (if m = 0 then 0 else
    (cutoffKernel ε (p.1 + m • d - p.2) : ℂ) * conj (u p.1) *
      zeroExtension d t u (p.1 - (p.1 + m • d - p.2) + m • d)) = _
  have hs : p.1 + m • d - p.2 = p.1 - p.2 + m • d := by ring
  have hy : p.1 - (p.1 + m • d - p.2) + m • d = p.2 := by ring
  rw [hy, hs]
  by_cases hm : m = 0
  · have hzero : imageCopy d ε u m = 0 := by
      funext q
      simp [imageCopy, hm]
    rw [hzero]
    simp [hm]
  · by_cases hp : p.2 ∈ Ioc t (t + d)
    · have hpProd : p ∈ univ ×ˢ Ioc t (t + d) := ⟨Set.mem_univ _, hp⟩
      simp only [if_neg hm, zeroExtension, Set.indicator_of_mem hp,
        Set.indicator_of_mem hpProd, imageCopy]
    · have hpProd : p ∉ univ ×ˢ Ioc t (t + d) := fun h => hp h.2
      simp only [if_neg hm, zeroExtension, Set.indicator_of_notMem hp,
        mul_zero, Set.indicator_of_notMem hpProd]

private theorem imageCopy_integrable
    (d t ε : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hF : Integrable (differenceCorrelation d t ε u)
      ((windowMeasure d t).prod volume)) (m : ℤ) :
    Integrable (imageCopy d ε u m) ((windowMeasure d t).prod (windowMeasure d t)) := by
  have hcomp := (copyReflection_measurePreserving d t m).integrable_comp_of_integrable
    (latticeCopy_integrable d t ε u hF m)
  rw [copy_reflection_eq_indicator_image d t ε u m] at hcomp
  rw [windowMeasure_prod_windowMeasure]
  exact (integrable_indicator_iff (MeasurableSet.prod (MeasurableSet.univ : MeasurableSet (univ : Set ℝ)) measurableSet_Ioc)).mp hcomp

/-- Both the complex integral and the nonnegative absolute integral are transported
by the same reflection; the second equality pays the image-side Tonelli exchange. -/
private theorem latticeCopy_integrals_eq_imageCopy
    (d t ε : ℝ) (u : ℝ → ℂ) (m : ℤ) :
    ((∫ p, latticeCopy d t ε u m p ∂((windowMeasure d t).prod volume)) =
      ∫ p, imageCopy d ε u m p ∂((windowMeasure d t).prod (windowMeasure d t))) ∧
    ((∫⁻ p, ‖latticeCopy d t ε u m p‖ₑ ∂((windowMeasure d t).prod volume)) =
      ∫⁻ p, ‖imageCopy d ε u m p‖ₑ
        ∂((windowMeasure d t).prod (windowMeasure d t))) := by
  have hMP := copyReflection_measurePreserving d t m
  have hEq := copy_reflection_eq_indicator_image d t ε u m
  have hEqNorm :
      (fun p => ‖latticeCopy d t ε u m (copyReflection d m p)‖ₑ) =
        (univ ×ˢ Ioc t (t + d)).indicator (fun p => ‖imageCopy d ε u m p‖ₑ) := by
    funext p
    change ‖(latticeCopy d t ε u m ∘ copyReflection d m) p‖ₑ = _
    rw [hEq]
    exact enorm_indicator_eq_indicator_enorm _ _
  constructor
  · calc
      _ = ∫ p, latticeCopy d t ε u m (copyReflection d m p)
          ∂((windowMeasure d t).prod volume) :=
        (hMP.integral_comp' (latticeCopy d t ε u m)).symm
      _ = ∫ p, (univ ×ˢ Ioc t (t + d)).indicator (imageCopy d ε u m) p
          ∂((windowMeasure d t).prod volume) := congrArg (fun F => ∫ p, F p
            ∂((windowMeasure d t).prod volume)) hEq
      _ = _ := by
        rw [integral_indicator (MeasurableSet.prod (MeasurableSet.univ : MeasurableSet (univ : Set ℝ)) measurableSet_Ioc),
          ← windowMeasure_prod_windowMeasure]
  · calc
      _ = ∫⁻ p, ‖latticeCopy d t ε u m (copyReflection d m p)‖ₑ
          ∂((windowMeasure d t).prod volume) :=
        (hMP.lintegral_comp_emb (copyReflection d m).measurableEmbedding
          (fun p => ‖latticeCopy d t ε u m p‖ₑ)).symm
      _ = ∫⁻ p, (univ ×ˢ Ioc t (t + d)).indicator (fun p => ‖imageCopy d ε u m p‖ₑ) p
          ∂((windowMeasure d t).prod volume) := congrArg (fun F => ∫⁻ p, F p
            ∂((windowMeasure d t).prod volume)) hEqNorm
      _ = _ := by
        rw [lintegral_indicator (MeasurableSet.prod (MeasurableSet.univ : MeasurableSet (univ : Set ℝ)) measurableSet_Ioc),
          ← windowMeasure_prod_windowMeasure]

private theorem imageCopy_tsum (d ε : ℝ) (u : ℝ → ℂ) (p : ℝ × ℝ) :
    (∑' m : ℤ, imageCopy d ε u m p) =
      conj (u p.1) * (imageKernel d ε p.1 p.2 : ℂ) * u p.2 := by
  classical
  simp only [imageKernel, Complex.ofReal_tsum]
  rw [← tsum_mul_left, ← tsum_mul_right]
  apply tsum_congr
  intro m
  by_cases hm : m = 0
  · simp only [imageCopy, if_pos hm, Complex.ofReal_zero, mul_zero, zero_mul]
  · simp only [imageCopy, if_neg hm]
    ring

/-- The actual lattice/Fubini composition. The only upstream payment is the
joint integrability of the actual difference correlation, derived from L² in the
independent correlation fragment. It is not an assumed image-pairing conclusion. -/
private theorem lattice_image_integrable_and_identity
    (d t ε : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hF : Integrable (differenceCorrelation d t ε u)
      ((windowMeasure d t).prod volume)) :
    Integrable (fun p : ℝ × ℝ =>
      conj (u p.1) * (imageKernel d ε p.1 p.2 : ℂ) * u p.2)
      ((windowMeasure d t).prod (windowMeasure d t)) ∧
    ((∫ p, differenceCorrelation d t ε u p ∂((windowMeasure d t).prod volume)) =
      ∫ p, conj (u p.1) * (imageKernel d ε p.1 p.2 : ℂ) * u p.2
        ∂((windowMeasure d t).prod (windowMeasure d t))) := by
  have hI := imageCopy_integrable d t ε u hF
  have hsum : (∑' m : ℤ, ∫⁻ p, ‖imageCopy d ε u m p‖ₑ
      ∂((windowMeasure d t).prod (windowMeasure d t))) ≠ ∞ := by
    have hEq : (fun m : ℤ => ∫⁻ p, ‖imageCopy d ε u m p‖ₑ
        ∂((windowMeasure d t).prod (windowMeasure d t))) =
        (fun m : ℤ => ∫⁻ p, ‖latticeCopy d t ε u m p‖ₑ
          ∂((windowMeasure d t).prod volume)) := by
      funext m
      exact (latticeCopy_integrals_eq_imageCopy d t ε u m).2.symm
    rw [hEq]
    exact latticeCopy_lintegral_norm_sum_ne_top d t ε u hF
  have hSumInt : Integrable (fun p => ∑' m : ℤ, imageCopy d ε u m p)
      ((windowMeasure d t).prod (windowMeasure d t)) := by
    refine ⟨AEStronglyMeasurable.tsum (fun m => (hI m).aestronglyMeasurable), ?_⟩
    apply lt_of_le_of_lt (lintegral_mono (fun p => enorm_tsum_le_tsum_enorm))
    rw [lintegral_tsum (fun m => (hI m).aestronglyMeasurable.enorm)]
    exact hsum.lt_top
  refine ⟨by simpa only [imageCopy_tsum] using hSumInt, ?_⟩
  calc
    _ = ∑' m : ℤ, ∫ p, latticeCopy d t ε u m p
        ∂((windowMeasure d t).prod volume) :=
      integral_difference_eq_tsum_copies d t ε u hF
    _ = ∑' m : ℤ, ∫ p, imageCopy d ε u m p
        ∂((windowMeasure d t).prod (windowMeasure d t)) :=
      tsum_congr fun m => (latticeCopy_integrals_eq_imageCopy d t ε u m).1
    _ = ∫ p, ∑' m : ℤ, imageCopy d ε u m p
        ∂((windowMeasure d t).prod (windowMeasure d t)) :=
      (integral_tsum (fun m => (hI m).aestronglyMeasurable) hsum).symm
    _ = _ := by simp only [imageCopy_tsum]

/-
TRANSIENT, UNCOMPILED APPLICATION FRAGMENT. No kernel acceptance claimed.
Pinned Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d.

Append this fragment inside namespace ActualGammaCommonCutoffDraft20261017,
before its final `end`, in ActualGammaCommonCutoff.lattice.v2.transient.draft.lean.
It consumes that file's private definitions and actual density-tail supplier.
It is not an independently importable module or a canonical admission proposal.

The product in the lattice file has coordinates (x,s). Internal Fubini arguments
below use (s,x), and the final theorem transports back by Prod.swap.
-/

open MeasureTheory.Measure

private def windowEnergy (d t : ℝ) (u : ℝ → ℂ) : ℝ :=
  ∫ x, ‖u x‖ ^ 2 ∂windowMeasure d t

/-- Every real shift is the pullback of a Haar translation on the actual circle.
No global measurability of the representative u is required. -/
private theorem periodic_shift_memLp
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    MemLp (fun x => periodicExtension d t u (x - s)) 2
      (windowMeasure d t) := by
  have hcircle : MemLp (AddCircle.liftIoc d t u) 2 := by
    exact hu.memLp_liftIoc
  have hshift : MeasurePreserving
      (fun x : ℝ => (x : AddCircle d) - (s : AddCircle d))
      (windowMeasure d t) volume :=
    (measurePreserving_sub_right (volume : Measure (AddCircle d))
      (s : AddCircle d)).comp (AddCircle.measurePreserving_mk d t)
  simpa only [periodicExtension, Function.comp_def, AddCircle.coe_sub] using
    hcircle.comp_measurePreserving hshift

/-- The circle volume has total mass d, rather than normalized mass one.
Consequently the shift preserves exactly the unnormalized Lebesgue energy. -/
private theorem periodic_shift_energy_eq
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ) (s : ℝ) :
    (∫ x, ‖periodicExtension d t u (x - s)‖ ^ 2 ∂windowMeasure d t) =
      windowEnergy d t u := by
  calc
    _ = ∫ c : AddCircle d,
        ‖AddCircle.liftIoc d t u (c - (s : AddCircle d))‖ ^ 2 := by
      simpa only [windowMeasure, periodicExtension, AddCircle.coe_sub] using
        AddCircle.integral_preimage d t
          (fun c : AddCircle d =>
            ‖AddCircle.liftIoc d t u (c - (s : AddCircle d))‖ ^ 2)
    _ = ∫ c : AddCircle d, ‖AddCircle.liftIoc d t u c‖ ^ 2 :=
      integral_sub_right_eq_self (μ := (volume : Measure (AddCircle d)))
        (fun c : AddCircle d => ‖AddCircle.liftIoc d t u c‖ ^ 2) (s : AddCircle d)
    _ = windowEnergy d t u := by
      rw [← AddCircle.integral_preimage d t]
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
      rw [AddCircle.liftIoc_coe_apply (p := d) (a := t) (f := u) hx]

/-- First pay the actual correlation's integrability, then its energy bound. -/
private theorem periodic_correlation_integrable_le
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    Integrable (fun x => ‖u x‖ * ‖periodicExtension d t u (x - s)‖)
      (windowMeasure d t) ∧
    (∫ x, ‖u x‖ * ‖periodicExtension d t u (x - s)‖ ∂windowMeasure d t) ≤
      windowEnergy d t u := by
  have hp := periodic_shift_memLp d t u hu s
  have hu2 := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  have hp2 := (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp
  have hmajor := (hu2.add hp2).div_const 2
  have hpoint (x : ℝ) :
      ‖u x‖ * ‖periodicExtension d t u (x - s)‖ ≤
        (‖u x‖ ^ 2 + ‖periodicExtension d t u (x - s)‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖u x‖ - ‖periodicExtension d t u (x - s)‖)]
  have hc : Integrable
      (fun x => ‖u x‖ * ‖periodicExtension d t u (x - s)‖)
      (windowMeasure d t) := by
    apply hmajor.mono' (hu.aestronglyMeasurable.norm.mul hp.aestronglyMeasurable.norm)
    exact Filter.Eventually.of_forall fun x => by
      simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact hpoint x
  refine ⟨hc, ?_⟩
  calc
    _ ≤ ∫ x,
        (‖u x‖ ^ 2 + ‖periodicExtension d t u (x - s)‖ ^ 2) / 2
          ∂windowMeasure d t := integral_mono hc hmajor hpoint
    _ = (windowEnergy d t u + windowEnergy d t u) / 2 := by
      simp only [integral_div, integral_add hu2 hp2,
        periodic_shift_energy_eq, windowEnergy]
    _ = windowEnergy d t u := by ring

private theorem zero_extension_memLp
    (d t : ℝ) (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t)) :
    MemLp (zeroExtension d t u) 2 volume := by
  exact (memLp_indicator_iff_restrict (μ := volume)
    measurableSet_Ioc.nullMeasurableSet).mpr hu

private theorem zero_extension_energy_eq (d t : ℝ) (u : ℝ → ℂ) :
    (∫ x : ℝ, ‖zeroExtension d t u x‖ ^ 2) = windowEnergy d t u := by
  calc
    _ = ∫ x : ℝ, (Ioc t (t + d)).indicator (fun z => ‖u z‖ ^ 2) x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        by_cases hx : x ∈ Ioc t (t + d)
        · simp only [zeroExtension, Set.indicator_of_mem hx]
        · simp only [zeroExtension, Set.indicator_of_notMem hx, norm_zero, zero_pow
            (by decide : (2 : ℕ) ≠ 0)]
    _ = windowEnergy d t u := integral_indicator measurableSet_Ioc

private theorem zero_shift_energy_eq (d t : ℝ) (u : ℝ → ℂ) (s : ℝ) :
    (∫ x : ℝ, ‖zeroExtension d t u (x - s)‖ ^ 2) = windowEnergy d t u := by
  calc
    _ = ∫ x : ℝ, ‖zeroExtension d t u x‖ ^ 2 := integral_sub_right_eq_self _ _
    _ = windowEnergy d t u := zero_extension_energy_eq d t u

/-- Reusable unnormalized shift identity for an actual circle pullback. -/
private theorem circle_pullback_shift_integral_eq
    (d t : ℝ) [Fact (0 < d)] (f : AddCircle d → ℂ) (s : ℝ) :
    (∫ x, f ((x - s : ℝ) : AddCircle d) ∂windowMeasure d t) =
      ∫ x, f (x : AddCircle d) ∂windowMeasure d t := by
  calc
    _ = ∫ c : AddCircle d, f (c - (s : AddCircle d)) := by
      simpa only [windowMeasure, AddCircle.coe_sub] using
        AddCircle.integral_preimage d t (fun c : AddCircle d => f (c - (s : AddCircle d)))
    _ = ∫ c : AddCircle d, f c :=
      integral_sub_right_eq_self (μ := (volume : Measure (AddCircle d))) f (s : AddCircle d)
    _ = ∫ x, f (x : AddCircle d) ∂windowMeasure d t :=
      (AddCircle.integral_preimage d t f).symm

private theorem zero_shift_memLp
    (d t : ℝ) (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    MemLp (fun x => zeroExtension d t u (x - s)) 2 (windowMeasure d t) := by
  have hzero := (zero_extension_memLp d t u hu).comp_measurePreserving
    (measurePreserving_sub_right (volume : Measure ℝ) s)
  exact hzero.restrict (Ioc t (t + d))

/-- Joint AE measurability follows from the actual measurable quotient map and
its measure-preserving real-shift fibres, not from iterated AE statements. -/
private theorem periodic_shift_joint_aestronglyMeasurable
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => periodicExtension d t u (p.2 - p.1))
      (volume.prod (windowMeasure d t)) := by
  have hq : QuasiMeasurePreserving
      (fun p : ℝ × ℝ => (p.2 : AddCircle d) - (p.1 : AddCircle d))
      (volume.prod (windowMeasure d t)) volume := by
    apply QuasiMeasurePreserving.prod_of_right (by fun_prop)
    exact Filter.Eventually.of_forall fun s =>
      ((measurePreserving_sub_right (volume : Measure (AddCircle d))
        (s : AddCircle d)).comp
          (AddCircle.measurePreserving_mk d t)).quasiMeasurePreserving
  have hcircle : MemLp (AddCircle.liftIoc d t u) 2 := hu.memLp_liftIoc
  simpa only [Function.comp_def, periodicExtension, AddCircle.coe_sub] using
    hcircle.aestronglyMeasurable.comp_quasiMeasurePreserving hq

private theorem zero_shift_joint_aestronglyMeasurable
    (d t : ℝ) (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t)) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => zeroExtension d t u (p.2 - p.1))
      (volume.prod (windowMeasure d t)) := by
  have hq : QuasiMeasurePreserving (fun p : ℝ × ℝ => p.2 - p.1)
      (volume.prod (windowMeasure d t)) volume := by
    apply QuasiMeasurePreserving.prod_of_right (by fun_prop)
    exact Filter.Eventually.of_forall fun s =>
      (measurePreserving_sub_right (volume : Measure ℝ) s).quasiMeasurePreserving.mono_left
        Measure.absolutelyContinuous_restrict
  exact (zero_extension_memLp d t u hu).aestronglyMeasurable.comp_quasiMeasurePreserving hq

/-- The unique-copy bound removes the central copy without introducing a
factor two into the correlation estimate. -/
private theorem mask_correlation_integrable_le
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    Integrable (fun x => ‖u x‖ *
      ‖periodicExtension d t u (x - s) - zeroExtension d t u (x - s)‖)
      (windowMeasure d t) ∧
    (∫ x, ‖u x‖ *
      ‖periodicExtension d t u (x - s) - zeroExtension d t u (x - s)‖
        ∂windowMeasure d t) ≤ windowEnergy d t u := by
  obtain ⟨hc, hcle⟩ := periodic_correlation_integrable_le d t u hu s
  have hm := ((periodic_shift_memLp d t u hu s).sub
    (zero_shift_memLp d t u hu s)).norm
  have hpoint (x : ℝ) :
      ‖u x‖ * ‖periodicExtension d t u (x - s) - zeroExtension d t u (x - s)‖ ≤
        ‖u x‖ * ‖periodicExtension d t u (x - s)‖ :=
    mul_le_mul_of_nonneg_left (periodic_minus_zero_norm_le d t u (x - s))
      (norm_nonneg _)
  have hi : Integrable (fun x => ‖u x‖ *
      ‖periodicExtension d t u (x - s) - zeroExtension d t u (x - s)‖)
      (windowMeasure d t) := by
    apply hc.mono' (hu.aestronglyMeasurable.norm.mul hm.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact hpoint x
  exact ⟨hi, (integral_mono hi hc hpoint).trans hcle⟩

private theorem cutoffKernel_nonneg {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    0 ≤ cutoffKernel ε s := by
  by_cases hs : ε < |s|
  · simpa only [cutoffKernel, if_pos hs] using actual_density_nonneg (hε.trans hs)
  · simp only [cutoffKernel, if_neg hs, le_refl]

/-- This pointwise decomposition retains the same strict epsilon cutoff on
both signed tails. In particular, neither endpoint is counted. -/
private theorem cutoffKernel_eq_tail_plus_reflection {ε : ℝ} (hε : 0 < ε) :
    cutoffKernel ε = fun s =>
      (Ioi ε).indicator density s + (Ioi ε).indicator density (-s) := by
  funext s
  by_cases hs : 0 ≤ s
  · have hn : ¬ ε < -s := by linarith
    simp [cutoffKernel, Set.indicator, abs_of_nonneg hs, hn]
  · have hs' : s ≤ 0 := le_of_not_ge hs
    have hn : ¬ ε < s := by linarith
    simp [cutoffKernel, Set.indicator, abs_of_nonpos hs', hn]

private theorem cutoffKernel_integrable_mass {ε : ℝ} (hε : 0 < ε) :
    Integrable (cutoffKernel ε) volume ∧
      (∫ s : ℝ, cutoffKernel ε s) = 2 * ∫ s in Ioi ε, density s := by
  have hg : Integrable ((Ioi ε).indicator density) volume :=
    (actual_density_tail_integrable hε).integrable_indicator measurableSet_Ioi
  have hgn := hg.comp_neg
  have heq := cutoffKernel_eq_tail_plus_reflection hε
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hg.add hgn
  · rw [heq, integral_add hg hgn,
      integral_neg_eq_self ((Ioi ε).indicator density) volume,
      integral_indicator measurableSet_Ioi]
    ring

private theorem differenceCorrelation_swapped_aestronglyMeasurable
    (d t ε : ℝ) [Fact (0 < d)] (hε : 0 < ε) (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => differenceCorrelation d t ε u p.swap)
      (volume.prod (windowMeasure d t)) := by
  have hk := (cutoffKernel_integrable_mass hε).1.1
  have hkc : AEStronglyMeasurable (fun s => (cutoffKernel ε s : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hk
  have huj : AEStronglyMeasurable (fun p : ℝ × ℝ => conj (u p.2))
      (volume.prod (windowMeasure d t)) :=
    Complex.continuous_conj.comp_aestronglyMeasurable hu.aestronglyMeasurable.comp_snd
  exact (hkc.comp_fst.mul huj).mul
    ((periodic_shift_joint_aestronglyMeasurable d t u hu).sub
      (zero_shift_joint_aestronglyMeasurable d t u hu))

/-- Fixed-epsilon all-L2 input for the actual lattice consumer. Integrability
of the target is a conclusion; the only analytic input is MemLp u 2 on Ioc. -/
private theorem differenceCorrelation_integrable_and_bound
    (d t ε : ℝ) [Fact (0 < d)] (hε : 0 < ε) (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) :
    Integrable (differenceCorrelation d t ε u) ((windowMeasure d t).prod volume) ∧
    (∫ p, ‖differenceCorrelation d t ε u p‖ ∂((windowMeasure d t).prod volume)) ≤
      2 * windowEnergy d t u * ∫ s in Ioi ε, density s := by
  let F : ℝ × ℝ → ℂ := fun p => differenceCorrelation d t ε u p.swap
  let N : ℝ → ℝ := fun s => ∫ x, ‖F (s, x)‖ ∂windowMeasure d t
  obtain ⟨hk, hkmass⟩ := cutoffKernel_integrable_mass hε
  have hFm : AEStronglyMeasurable F (volume.prod (windowMeasure d t)) :=
    differenceCorrelation_swapped_aestronglyMeasurable d t ε hε u hu
  have hnorm (s x : ℝ) : ‖F (s, x)‖ = cutoffKernel ε s *
      (‖u x‖ * ‖periodicExtension d t u (x - s) - zeroExtension d t u (x - s)‖) := by
    simp only [F, differenceCorrelation, Prod.swap_prod_mk, norm_mul,
      Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (cutoffKernel_nonneg hε s)]
    ring
  have hSlice (s : ℝ) : Integrable (fun x => F (s, x)) (windowMeasure d t) := by
    have hc : Integrable (fun x => cutoffKernel ε s *
        (‖u x‖ * ‖periodicExtension d t u (x - s) - zeroExtension d t u (x - s)‖))
        (windowMeasure d t) :=
      (mask_correlation_integrable_le d t u hu s).1.const_mul (cutoffKernel ε s)
    have hsm : AEStronglyMeasurable (fun x => F (s, x)) (windowMeasure d t) := by
      change AEStronglyMeasurable (fun x : ℝ => (cutoffKernel ε s : ℂ) * conj (u x) *
        (periodicExtension d t u (x - s) - zeroExtension d t u (x - s)))
        (windowMeasure d t)
      have hconstant : AEStronglyMeasurable (fun _ : ℝ => (cutoffKernel ε s : ℂ))
          (windowMeasure d t) := aestronglyMeasurable_const
      have hconj : AEStronglyMeasurable (fun x => conj (u x)) (windowMeasure d t) :=
        Complex.continuous_conj.comp_aestronglyMeasurable hu.aestronglyMeasurable
      have hdiff : AEStronglyMeasurable (fun x =>
          periodicExtension d t u (x - s) - zeroExtension d t u (x - s))
          (windowMeasure d t) :=
        ((periodic_shift_memLp d t u hu s).sub
          (zero_shift_memLp d t u hu s)).aestronglyMeasurable
      exact (hconstant.mul hconj).mul hdiff
    apply hc.mono' hsm
    exact Filter.Eventually.of_forall fun x => (hnorm s x).le
  have hNm : AEStronglyMeasurable N volume := hFm.norm.integral_prod_right'
  have hNnonneg (s : ℝ) : 0 ≤ N s := integral_nonneg fun _ => norm_nonneg _
  have hNle (s : ℝ) : N s ≤ cutoffKernel ε s * windowEnergy d t u := by
    dsimp only [N]
    simp_rw [hnorm s]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (mask_correlation_integrable_le d t u hu s).2 (cutoffKernel_nonneg hε s)
  have hNint : Integrable N volume := by
    apply (hk.const_mul (windowEnergy d t u)).mono' hNm
    exact Filter.Eventually.of_forall fun s => by
      change ‖N s‖ ≤ windowEnergy d t u * cutoffKernel ε s
      rw [Real.norm_of_nonneg (hNnonneg s), mul_comm (windowEnergy d t u)]
      exact hNle s
  have hFint : Integrable F (volume.prod (windowMeasure d t)) :=
    (integrable_prod_iff hFm).mpr
      ⟨Filter.Eventually.of_forall hSlice, hNint⟩
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_def, F, Prod.swap_swap] using hFint.swap
  · calc
      _ = ∫ p, ‖F p‖ ∂(volume.prod (windowMeasure d t)) :=
        (integral_prod_swap
          (μ := windowMeasure d t) (ν := (volume : Measure ℝ))
          (fun p => ‖differenceCorrelation d t ε u p‖)).symm
      _ = ∫ s, N s := integral_prod (fun p => ‖F p‖) hFint.norm
      _ ≤ ∫ s, windowEnergy d t u * cutoffKernel ε s :=
        integral_mono hNint (hk.const_mul _) fun s => by
          simpa only [mul_comm] using hNle s
      _ = windowEnergy d t u * (2 * ∫ s in Ioi ε, density s) := by
        rw [integral_const_mul, hkmass]
      _ = 2 * windowEnergy d t u * ∫ s in Ioi ε, density s := by ring

/-- Consume the new L2 payment at the existing actual lattice/Fubini boundary.
There is no target-integrability premise and no abstract replacement kernel. -/
example (d t ε : ℝ) [Fact (0 < d)] (hε : 0 < ε) (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) :
    Integrable (fun p : ℝ × ℝ =>
      conj (u p.1) * (imageKernel d ε p.1 p.2 : ℂ) * u p.2)
      ((windowMeasure d t).prod (windowMeasure d t)) ∧
    ((∫ p, differenceCorrelation d t ε u p ∂((windowMeasure d t).prod volume)) =
      ∫ p, conj (u p.1) * (imageKernel d ε p.1 p.2 : ℂ) * u p.2
        ∂((windowMeasure d t).prod (windowMeasure d t))) := by
  exact lattice_image_integrable_and_identity d t ε u
    (differenceCorrelation_integrable_and_bound d t ε hε u hu).1

/-- Exact actual window: d=2a and t=-a reduce the interval to Ioc (-a) a. -/
example (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    letI : Fact (0 < 2 * a) := ⟨by linarith⟩
    Integrable (differenceCorrelation (2 * a) (-a) ε u)
      ((volume.restrict (Ioc (-a) a)).prod volume) ∧
    (∫ p, ‖differenceCorrelation (2 * a) (-a) ε u p‖
      ∂((volume.restrict (Ioc (-a) a)).prod volume)) ≤
      2 * (∫ x in Ioc (-a) a, ‖u x‖ ^ 2) * ∫ s in Ioi ε, density s := by
  letI : Fact (0 < 2 * a) := ⟨by linarith⟩
  have hend : -a + 2 * a = a := by ring
  have hu' : MemLp u 2 (windowMeasure (2 * a) (-a)) := by
    simpa only [windowMeasure, hend] using hu
  simpa only [windowMeasure, windowEnergy, hend] using
    differenceCorrelation_integrable_and_bound (2 * a) (-a) ε hε u hu'

/-
TRANSIENT, UNCOMPILED APPLICATION FRAGMENT. No kernel acceptance claimed.
Append after the correlation fragment inside ActualGammaCommonCutoffDraft20261017.
Only existing L2, Haar translation, Fubini and norm-square APIs are composed.
-/

private def zeroCorrelation (d t : ℝ) (u : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∫ x : ℝ, conj (zeroExtension d t u x) * zeroExtension d t u (x - s)

private def periodicCorrelation (d t : ℝ) [Fact (0 < d)]
    (u : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∫ x, conj (u x) * periodicExtension d t u (x - s) ∂windowMeasure d t

private def zeroTranslationEnergy (d t : ℝ) (u : ℝ → ℂ) (s : ℝ) : ℝ :=
  ∫ x : ℝ, Complex.normSq (zeroExtension d t u x - zeroExtension d t u (x - s))

private def periodicTranslationEnergy (d t : ℝ) [Fact (0 < d)]
    (u : ℝ → ℂ) (s : ℝ) : ℝ :=
  ∫ x, Complex.normSq (u x - periodicExtension d t u (x - s)) ∂windowMeasure d t

private def zeroCutoffEnergy (d t ε : ℝ) (u : ℝ → ℂ) : ℝ :=
  ∫ s in Ioi ε, density s * zeroTranslationEnergy d t u s

private def periodicCutoffEnergy (d t ε : ℝ) [Fact (0 < d)] (u : ℝ → ℂ) : ℝ :=
  ∫ s in Ioi ε, density s * periodicTranslationEnergy d t u s

private theorem l2_complex_correlation_integrable
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => conj (f x) * g x) μ := by
  have hnorm : Integrable (fun x => ‖f x‖ * ‖g x‖) μ :=
    hf.norm.integrable_mul hg.norm
  apply hnorm.mono'
    ((Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable).mul hg.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    change ‖conj (f x) * g x‖ ≤ ‖f x‖ * ‖g x‖
    simp only [norm_mul, Complex.norm_conj, le_refl]

private theorem l2_normSq_integrable
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 μ) : Integrable (fun x => Complex.normSq (f x)) μ := by
  simpa only [Complex.normSq_eq_norm_sq] using
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf

private theorem l2_normSq_difference_expansion
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, Complex.normSq (f x - g x) ∂μ) =
      (∫ x, Complex.normSq (f x) ∂μ) + (∫ x, Complex.normSq (g x) ∂μ) -
        2 * (∫ x, conj (f x) * g x ∂μ).re := by
  have hF := l2_normSq_integrable hf
  have hG := l2_normSq_integrable hg
  have hC := l2_complex_correlation_integrable hf hg
  have hpoint (x : α) : Complex.normSq (f x - g x) =
      Complex.normSq (f x) + Complex.normSq (g x) - 2 * (conj (f x) * g x).re := by
    simp only [Complex.normSq_sub, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hFG : Integrable (fun x => Complex.normSq (f x) + Complex.normSq (g x)) μ :=
    hF.add hG
  have h2Cr : Integrable (fun x => 2 * (conj (f x) * g x).re) μ := hC.re.const_mul 2
  simp_rw [hpoint]
  have hCre : (∫ x, (conj (f x) * g x).re ∂μ) = (∫ x, conj (f x) * g x ∂μ).re :=
    integral_re hC
  rw [integral_sub hFG h2Cr, integral_add hF hG, integral_const_mul, hCre]

private theorem l2_normSq_difference_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, Complex.normSq (f x - g x) ∂μ) ≤
      2 * ((∫ x, ‖f x‖ ^ 2 ∂μ) + (∫ x, ‖g x‖ ^ 2 ∂μ)) := by
  have hF := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hG := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hD := l2_normSq_integrable (hf.sub hg)
  have hpoint (x : α) : Complex.normSq (f x - g x) ≤
      2 * (‖f x‖ ^ 2 + ‖g x‖ ^ 2) := by
    rw [Complex.normSq_eq_norm_sq]
    have htriangle := norm_sub_le (f x) (g x)
    have hsquare : ‖f x - g x‖ ^ 2 ≤ (‖f x‖ + ‖g x‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr htriangle
    nlinarith [sq_nonneg (‖f x‖ - ‖g x‖)]
  calc
    _ ≤ ∫ x, 2 * (‖f x‖ ^ 2 + ‖g x‖ ^ 2) ∂μ :=
      integral_mono hD ((hF.add hG).const_mul 2) hpoint
    _ = _ := by rw [integral_const_mul, integral_add hF hG]

private theorem zeroCorrelation_eq_window (d t : ℝ) (u : ℝ → ℂ) (s : ℝ) :
    zeroCorrelation d t u s =
      ∫ x, conj (u x) * zeroExtension d t u (x - s) ∂windowMeasure d t := by
  have hfun : (fun x => conj (zeroExtension d t u x) * zeroExtension d t u (x - s)) =
      (Ioc t (t + d)).indicator
        (fun x => conj (u x) * zeroExtension d t u (x - s)) := by
    funext x
    by_cases hx : x ∈ Ioc t (t + d) <;> simp [zeroExtension, hx]
  unfold zeroCorrelation
  rw [hfun]
  exact integral_indicator measurableSet_Ioc

private theorem zeroTranslationEnergy_expansion
    (d t : ℝ) (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    zeroTranslationEnergy d t u s =
      2 * windowEnergy d t u - 2 * (zeroCorrelation d t u s).re := by
  have hz := zero_extension_memLp d t u hu
  have hzs := hz.comp_measurePreserving (measurePreserving_sub_right volume s)
  have h := l2_normSq_difference_expansion hz hzs
  simpa only [Complex.normSq_eq_norm_sq, zero_extension_energy_eq,
    zero_shift_energy_eq, zeroTranslationEnergy, zeroCorrelation, Function.comp_def, two_mul] using h

private theorem periodicTranslationEnergy_expansion
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    periodicTranslationEnergy d t u s =
      2 * windowEnergy d t u - 2 * (periodicCorrelation d t u s).re := by
  have h := l2_normSq_difference_expansion hu (periodic_shift_memLp d t u hu s)
  simpa only [Complex.normSq_eq_norm_sq, periodic_shift_energy_eq,
    windowEnergy, periodicTranslationEnergy, periodicCorrelation, two_mul] using h

private theorem zeroCorrelation_neg (d t : ℝ) (u : ℝ → ℂ) (s : ℝ) :
    zeroCorrelation d t u (-s) = conj (zeroCorrelation d t u s) := by
  let f := zeroExtension d t u
  let F : ℝ → ℂ := fun x => conj (conj (f x) * f (x - s))
  calc
    _ = ∫ x : ℝ, F (x + s) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp [zeroCorrelation, F, f, sub_neg_eq_add, mul_comm]
    _ = ∫ x : ℝ, F x := integral_add_right_eq_self F s
    _ = _ := integral_conj

private theorem periodicCorrelation_eq_circle
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ) (s : ℝ) :
    periodicCorrelation d t u s =
      ∫ c : AddCircle d, conj (AddCircle.liftIoc d t u c) *
        AddCircle.liftIoc d t u (c - (s : AddCircle d)) := by
  calc
    _ = ∫ x, conj (AddCircle.liftIoc d t u (x : AddCircle d)) *
        AddCircle.liftIoc d t u ((x : AddCircle d) - (s : AddCircle d))
          ∂windowMeasure d t := by
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
      simp only [periodicCorrelation, periodicExtension, AddCircle.coe_sub,
        AddCircle.liftIoc_coe_apply (p := d) (a := t) (f := u) hx]
    _ = _ := by
      simpa only [windowMeasure] using AddCircle.integral_preimage d t
        (fun c : AddCircle d => conj (AddCircle.liftIoc d t u c) *
          AddCircle.liftIoc d t u (c - (s : AddCircle d)))

private theorem periodicCorrelation_neg
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ) (s : ℝ) :
    periodicCorrelation d t u (-s) = conj (periodicCorrelation d t u s) := by
  rw [periodicCorrelation_eq_circle, periodicCorrelation_eq_circle]
  let U := AddCircle.liftIoc d t u
  let F : AddCircle d → ℂ := fun c => conj (conj (U c) * U (c - (s : AddCircle d)))
  calc
    _ = ∫ c : AddCircle d, F (c + (s : AddCircle d)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun c => by
        simp [F, U, AddCircle.coe_neg, sub_neg_eq_add, mul_comm]
    _ = ∫ c : AddCircle d, F c :=
      integral_add_right_eq_self (μ := (volume : Measure (AddCircle d))) F (s : AddCircle d)
    _ = _ := integral_conj

private theorem correlation_difference_slice
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    (∫ x, conj (u x) *
      (periodicExtension d t u (x - s) - zeroExtension d t u (x - s))
        ∂windowMeasure d t) = periodicCorrelation d t u s - zeroCorrelation d t u s := by
  have hp := l2_complex_correlation_integrable hu (periodic_shift_memLp d t u hu s)
  have hz := l2_complex_correlation_integrable hu (zero_shift_memLp d t u hu s)
  simp_rw [mul_sub]
  rw [zeroCorrelation_eq_window]
  exact integral_sub hp hz

private theorem differenceCorrelation_slice
    (d t ε : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    (∫ x, differenceCorrelation d t ε u (x, s) ∂windowMeasure d t) =
      (cutoffKernel ε s : ℂ) *
        (periodicCorrelation d t u s - zeroCorrelation d t u s) := by
  simp only [differenceCorrelation, mul_assoc]
  rw [integral_const_mul, correlation_difference_slice d t u hu s]

private theorem cutoffKernel_of_mem_tail {ε s : ℝ} (hε : 0 < ε) (hs : s ∈ Ioi ε) :
    cutoffKernel ε s = density s := by
  have hs' : ε < s := hs
  have hs0 : 0 < s := hε.trans hs'
  simp only [cutoffKernel, abs_of_pos hs0, if_pos hs']

private theorem signed_cutoff_integral_eq_twice_positive
    {ε : ℝ} (hε : 0 < ε) (R : ℝ → ℝ) (hR : ∀ s, R (-s) = R s)
    (hInt : Integrable (fun s => cutoffKernel ε s * R s) volume) :
    (∫ s : ℝ, cutoffKernel ε s * R s) = 2 * ∫ s in Ioi ε, density s * R s := by
  let H : ℝ → ℝ := (Ioi ε).indicator (fun s => density s * R s)
  have hH : H = (Ioi ε).indicator (fun s => cutoffKernel ε s * R s) := by
    funext s
    by_cases hs : s ∈ Ioi ε
    · simp only [H, Set.indicator_of_mem hs, cutoffKernel_of_mem_tail hε hs]
    · simp only [H, Set.indicator_of_notMem hs]
  have hHi : Integrable H volume := by rw [hH]; exact hInt.indicator measurableSet_Ioi
  have hHpoint (s : ℝ) : H s = (Ioi ε).indicator density s * R s := by
    by_cases hs : s ∈ Ioi ε <;> simp [H, hs]
  have hsplit : (fun s => cutoffKernel ε s * R s) = fun s => H s + H (-s) := by
    funext s
    rw [hHpoint, hHpoint, hR]
    have hkernel := congrFun (cutoffKernel_eq_tail_plus_reflection hε) s
    rw [hkernel]
    ring
  rw [hsplit, integral_add hHi hHi.comp_neg, integral_neg_eq_self H volume]
  rw [show (∫ s, H s) = ∫ s in Ioi ε, density s * R s from
    integral_indicator measurableSet_Ioi]
  ring

private theorem zeroTranslationEnergy_aestronglyMeasurable
    (d t : ℝ) (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t)) :
    AEStronglyMeasurable (zeroTranslationEnergy d t u) volume := by
  have hz := zero_extension_memLp d t u hu
  have hq : QuasiMeasurePreserving (fun p : ℝ × ℝ => p.2 - p.1)
      (volume.prod volume) volume := by
    apply QuasiMeasurePreserving.prod_of_right (by fun_prop)
    exact Filter.Eventually.of_forall fun s =>
      (measurePreserving_sub_right (volume : Measure ℝ) s).quasiMeasurePreserving
  have hshift := hz.aestronglyMeasurable.comp_quasiMeasurePreserving hq
  have hjoint := (hz.aestronglyMeasurable.comp_snd.sub hshift).norm.pow 2
  change AEStronglyMeasurable (fun s => ∫ x : ℝ,
    Complex.normSq (zeroExtension d t u x - zeroExtension d t u (x - s))) volume
  simpa only [Complex.normSq_eq_norm_sq, Function.comp_def,
    Pi.sub_apply, Pi.pow_apply] using hjoint.integral_prod_right'

private theorem periodicTranslationEnergy_aestronglyMeasurable
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) :
    AEStronglyMeasurable (periodicTranslationEnergy d t u) volume := by
  have hjoint := (hu.aestronglyMeasurable.comp_snd.sub
    (periodic_shift_joint_aestronglyMeasurable d t u hu)).norm.pow 2
  change AEStronglyMeasurable (fun s => ∫ x,
    Complex.normSq (u x - periodicExtension d t u (x - s)) ∂windowMeasure d t) volume
  simpa only [Complex.normSq_eq_norm_sq, Function.comp_def,
    Pi.sub_apply, Pi.pow_apply] using hjoint.integral_prod_right'

private theorem zeroTranslationEnergy_nonneg_le
    (d t : ℝ) (u : ℝ → ℂ) (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    0 ≤ zeroTranslationEnergy d t u s ∧
      zeroTranslationEnergy d t u s ≤ 4 * windowEnergy d t u := by
  have hz := zero_extension_memLp d t u hu
  have hzs := hz.comp_measurePreserving (measurePreserving_sub_right volume s)
  refine ⟨integral_nonneg fun x => Complex.normSq_nonneg _, ?_⟩
  have h := l2_normSq_difference_bound hz hzs
  change zeroTranslationEnergy d t u s ≤
    2 * ((∫ x : ℝ, ‖zeroExtension d t u x‖ ^ 2) +
      ∫ x : ℝ, ‖zeroExtension d t u (x - s)‖ ^ 2) at h
  rw [zero_extension_energy_eq, zero_shift_energy_eq] at h
  nlinarith

private theorem periodicTranslationEnergy_nonneg_le
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) (s : ℝ) :
    0 ≤ periodicTranslationEnergy d t u s ∧
      periodicTranslationEnergy d t u s ≤ 4 * windowEnergy d t u := by
  refine ⟨integral_nonneg fun x => Complex.normSq_nonneg _, ?_⟩
  have h := l2_normSq_difference_bound hu (periodic_shift_memLp d t u hu s)
  change periodicTranslationEnergy d t u s ≤
    2 * (windowEnergy d t u + ∫ x,
      ‖periodicExtension d t u (x - s)‖ ^ 2 ∂windowMeasure d t) at h
  rw [periodic_shift_energy_eq] at h
  nlinarith

private theorem cutoff_energy_integrable_of_bound
    {ε : ℝ} (hε : 0 < ε) (E : ℝ → ℝ) (C : ℝ)
    (hEm : AEStronglyMeasurable E volume) (hE : ∀ s, 0 ≤ E s ∧ E s ≤ C) :
    IntegrableOn (fun s => density s * E s) (Ioi ε) := by
  have hk := actual_density_tail_integrable hε
  apply (hk.mul_const C).mono' (hk.1.mul hEm.restrict)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  have hks := actual_density_nonneg (hε.trans hs)
  change ‖density s * E s‖ ≤ density s * C
  rw [Real.norm_of_nonneg (mul_nonneg hks (hE s).1)]
  exact mul_le_mul_of_nonneg_left (hE s).2 hks

private theorem zeroCutoffEnergy_integrable
    (d t ε : ℝ) (hε : 0 < ε) (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) :
    IntegrableOn (fun s => density s * zeroTranslationEnergy d t u s) (Ioi ε) :=
  cutoff_energy_integrable_of_bound hε _ _
    (zeroTranslationEnergy_aestronglyMeasurable d t u hu)
    (zeroTranslationEnergy_nonneg_le d t u hu)

private theorem periodicCutoffEnergy_integrable
    (d t ε : ℝ) [Fact (0 < d)] (hε : 0 < ε) (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) :
    IntegrableOn (fun s => density s * periodicTranslationEnergy d t u s) (Ioi ε) :=
  cutoff_energy_integrable_of_bound hε _ _
    (periodicTranslationEnergy_aestronglyMeasurable d t u hu)
    (periodicTranslationEnergy_nonneg_le d t u hu)

/-- Complete fixed-epsilon actual consumer candidate. All integrability claims
are conclusions; hu and epsilon>0 are the only analytic hypotheses. -/
private theorem actual_common_cutoff_integrable_and_identity
    (d t ε : ℝ) [Fact (0 < d)] (hε : 0 < ε) (u : ℝ → ℂ)
    (hu : MemLp u 2 (windowMeasure d t)) :
    IntegrableOn (fun s => density s * zeroTranslationEnergy d t u s) (Ioi ε) ∧
    IntegrableOn (fun s => density s * periodicTranslationEnergy d t u s) (Ioi ε) ∧
    Integrable (fun p : ℝ × ℝ =>
      conj (u p.1) * (imageKernel d ε p.1 p.2 : ℂ) * u p.2)
      ((windowMeasure d t).prod (windowMeasure d t)) ∧
    zeroCutoffEnergy d t ε u = periodicCutoffEnergy d t ε u +
      (∫ p : ℝ × ℝ,
        conj (u p.1) * (imageKernel d ε p.1 p.2 : ℂ) * u p.2
          ∂((windowMeasure d t).prod (windowMeasure d t))).re := by
  have hE0 := zeroCutoffEnergy_integrable d t ε hε u hu
  have hEP := periodicCutoffEnergy_integrable d t ε hε u hu
  have hF := (differenceCorrelation_integrable_and_bound d t ε hε u hu).1
  obtain ⟨hB, hFB⟩ := lattice_image_integrable_and_identity d t ε u hF
  let R : ℝ → ℝ := fun s =>
    (periodicCorrelation d t u s - zeroCorrelation d t u s).re
  have hRneg (s : ℝ) : R (-s) = R s := by
    simp only [R, periodicCorrelation_neg, zeroCorrelation_neg, map_sub, Complex.sub_re, Complex.conj_re]
  have hSlice : Integrable
      (fun s => ∫ x, differenceCorrelation d t ε u (x, s) ∂windowMeasure d t) volume :=
    hF.integral_prod_right
  have hSliceRe (s : ℝ) :
      (∫ x, differenceCorrelation d t ε u (x, s) ∂windowMeasure d t).re =
        cutoffKernel ε s * R s := by
    rw [differenceCorrelation_slice d t ε u hu s]
    simp only [R, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hRint : Integrable (fun s => cutoffKernel ε s * R s) volume := by
    convert hSlice.re using 1
    funext s
    exact (hSliceRe s).symm
  have hBreal :
      (∫ p : ℝ × ℝ,
        conj (u p.1) * (imageKernel d ε p.1 p.2 : ℂ) * u p.2
          ∂((windowMeasure d t).prod (windowMeasure d t))).re =
        2 * ∫ s in Ioi ε, density s * R s := by
    calc
      _ = (∫ p, differenceCorrelation d t ε u p
          ∂((windowMeasure d t).prod volume)).re := congrArg Complex.re hFB.symm
      _ = (∫ s, ∫ x, differenceCorrelation d t ε u (x, s)
          ∂windowMeasure d t).re := congrArg Complex.re
            (integral_prod_symm (differenceCorrelation d t ε u) hF)
      _ = ∫ s, (∫ x, differenceCorrelation d t ε u (x, s)
          ∂windowMeasure d t).re := (integral_re hSlice).symm
      _ = ∫ s : ℝ, cutoffKernel ε s * R s := by simp_rw [hSliceRe]
      _ = _ := signed_cutoff_integral_eq_twice_positive hε R hRneg hRint
  have hEnergyDifference :
      zeroCutoffEnergy d t ε u - periodicCutoffEnergy d t ε u =
        2 * ∫ s in Ioi ε, density s * R s := by
    unfold zeroCutoffEnergy periodicCutoffEnergy
    rw [← integral_sub hE0 hEP]
    calc
      _ = ∫ s in Ioi ε, 2 * (density s * R s) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun s => by
          change density s * zeroTranslationEnergy d t u s -
            density s * periodicTranslationEnergy d t u s = 2 * (density s * R s)
          rw [zeroTranslationEnergy_expansion d t u hu s,
            periodicTranslationEnergy_expansion d t u hu s]
          simp only [R, Complex.sub_re]
          ring
      _ = _ := integral_const_mul 2 _
  refine ⟨hE0, hEP, hB, ?_⟩
  linarith [hBreal, hEnergyDifference]

/-- Exact original symmetric window; the open and half-open measures coincide. -/
example (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioo (-a) a))) :
    letI : Fact (0 < 2 * a) := ⟨by linarith⟩
    zeroCutoffEnergy (2 * a) (-a) ε u = periodicCutoffEnergy (2 * a) (-a) ε u +
      (∫ p : ℝ × ℝ, conj (u p.1) * (imageKernel (2 * a) ε p.1 p.2 : ℂ) * u p.2
        ∂((volume.restrict (Ioo (-a) a)).prod (volume.restrict (Ioo (-a) a)))).re := by
  letI : Fact (0 < 2 * a) := ⟨by linarith⟩
  have hend : -a + 2 * a = a := by ring
  have hμ : windowMeasure (2 * a) (-a) = volume.restrict (Ioo (-a) a) := by
    simp only [windowMeasure, hend, restrict_Ioo_eq_restrict_Ioc]
  have hu' : MemLp u 2 (windowMeasure (2 * a) (-a)) := by rw [hμ]; exact hu
  have h := (actual_common_cutoff_integrable_and_identity (2 * a) (-a) ε hε u hu').2.2.2
  simpa only [hμ] using h

end ActualGammaCommonCutoffDraft20261017

/-
Transient, uncompiled continuation for the actual Gamma domain passage.
The finite-cutoff identity, cutoff integrability, and actual boundary-pair
limit are explicit unpaid inputs here. This file proves no unconditional
Gamma realization and proposes no tracked declaration or admission claim.
Its purpose is to consume those inputs without subtracting infinite energies.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate

namespace ActualGammaDomainPassageDraft

private abbrev density :=
  D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity

private def intervalMeasure (d t : ℝ) : Measure ℝ :=
  volume.restrict (Ioc t (t + d))

private def zeroExtension (d t : ℝ) (u : ℝ → ℂ) : ℝ → ℂ :=
  (Ioc t (t + d)).indicator u

private def periodicExtension (d t : ℝ) [Fact (0 < d)]
    (u : ℝ → ℂ) (x : ℝ) : ℂ :=
  AddCircle.liftIoc d t u (x : AddCircle d)

private def zeroEnergyDensity (d t : ℝ) (u : ℝ → ℂ) (s : ℝ) : ℝ :=
  density s * ∫ x : ℝ, Complex.normSq
    (zeroExtension d t u x - zeroExtension d t u (x - s))

private def periodicEnergyDensity (d t : ℝ) [Fact (0 < d)]
    (u : ℝ → ℂ) (s : ℝ) : ℝ :=
  density s * ∫ x : ℝ, Complex.normSq
    (u x - periodicExtension d t u (x - s)) ∂intervalMeasure d t

private def cutoffKernel (ε s : ℝ) : ℝ :=
  if ε < |s| then density |s| else 0

private def cutoffBoundaryPair (d t ε : ℝ) (u : ℝ → ℂ) : ℝ :=
  (∫ p : ℝ × ℝ, conj (u p.1) *
    ((∑' m : ℤ, if m = 0 then 0 else
      cutoffKernel ε (p.1 - p.2 + m • d)) : ℂ) * u p.2
    ∂(intervalMeasure d t).prod (intervalMeasure d t)).re

private def cutoff (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private theorem cutoff_pos (n : ℕ) : 0 < cutoff n := by
  unfold cutoff
  positivity

private theorem cutoff_tendsto : Tendsto cutoff atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

private theorem density_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ density s := by
  change 0 ≤ Real.exp (-s / 2) / (1 - Real.exp (-2 * s))
  exact div_nonneg (Real.exp_pos _).le
    (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))

-- Only finite quantities are added or subtracted in the cutoff equalities.
-- AECover then derives integrability of the formerly unknown full energy.
private theorem actual_nonnegative_energy_domain_passage
    (d t : ℝ) [Fact (0 < d)] (u : ℝ → ℂ)
    (hcut0 : ∀ ε : ℝ, 0 < ε →
      IntegrableOn (zeroEnergyDensity d t u) (Ioi ε))
    (hcutP : ∀ ε : ℝ, 0 < ε →
      IntegrableOn (periodicEnergyDensity d t u) (Ioi ε))
    (hfinite : ∀ ε : ℝ, 0 < ε →
      (∫ s in Ioi ε, zeroEnergyDensity d t u s) =
        (∫ s in Ioi ε, periodicEnergyDensity d t u s) +
          cutoffBoundaryPair d t ε u)
    (hboundary : Tendsto (fun n => cutoffBoundaryPair d t (cutoff n) u)
      atTop (𝓝 (cutoffBoundaryPair d t 0 u))) :
    (IntegrableOn (zeroEnergyDensity d t u) (Ioi 0) ↔
      IntegrableOn (periodicEnergyDensity d t u) (Ioi 0)) ∧
    (IntegrableOn (periodicEnergyDensity d t u) (Ioi 0) →
      (∫ s in Ioi 0, zeroEnergyDensity d t u s) =
        (∫ s in Ioi 0, periodicEnergyDensity d t u s) +
          cutoffBoundaryPair d t 0 u) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F := zeroEnergyDensity d t u
  let G := periodicEnergyDensity d t u
  let b := cutoffBoundaryPair d t 0 u
  have hc : AECover μ atTop (fun n : ℕ => Ioi (cutoff n)) :=
    aecover_Ioi_of_Ioi cutoff_tendsto
  have hrestrict (n : ℕ) : μ.restrict (Ioi (cutoff n)) =
      volume.restrict (Ioi (cutoff n)) := by
    exact Measure.restrict_restrict_of_subset
      (fun _ hs => (cutoff_pos n).trans hs)
  have hFcut (n : ℕ) : IntegrableOn F (Ioi (cutoff n)) μ := by
    change Integrable F (μ.restrict (Ioi (cutoff n)))
    rw [hrestrict]
    exact hcut0 _ (cutoff_pos n)
  have hGcut (n : ℕ) : IntegrableOn G (Ioi (cutoff n)) μ := by
    change Integrable G (μ.restrict (Ioi (cutoff n)))
    rw [hrestrict]
    exact hcutP _ (cutoff_pos n)
  have hFnonneg : ∀ᵐ s ∂μ, 0 ≤ F s := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (density_nonneg hs)
      (integral_nonneg fun x => Complex.normSq_nonneg _)
  have hGnonneg : ∀ᵐ s ∂μ, 0 ≤ G s := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (density_nonneg hs)
      (integral_nonneg fun x => Complex.normSq_nonneg _)
  have hid (n : ℕ) : (∫ s in Ioi (cutoff n), F s ∂μ) =
      (∫ s in Ioi (cutoff n), G s ∂μ) +
        cutoffBoundaryPair d t (cutoff n) u := by
    simp only [hrestrict]
    exact hfinite _ (cutoff_pos n)
  have hforward (hG : Integrable G μ) :
      Integrable F μ ∧ (∫ s, F s ∂μ) = (∫ s, G s ∂μ) + b := by
    have hlim : Tendsto (fun n => ∫ s in Ioi (cutoff n), F s ∂μ)
        atTop (𝓝 ((∫ s, G s ∂μ) + b)) := by
      simpa only [hid] using
        (hc.integral_tendsto_of_countably_generated hG).add hboundary
    have hF : Integrable F μ :=
      hc.integrable_of_integral_tendsto_of_nonneg_ae
        ((∫ s, G s ∂μ) + b) hFcut hFnonneg hlim
    exact ⟨hF, hc.integral_eq_of_tendsto _ hF hlim⟩
  have hbackward (hF : Integrable F μ) : Integrable G μ := by
    have hid' (n : ℕ) : (∫ s in Ioi (cutoff n), F s ∂μ) -
        cutoffBoundaryPair d t (cutoff n) u =
          (∫ s in Ioi (cutoff n), G s ∂μ) := by
      rw [hid]
      ring
    have hlim : Tendsto (fun n => ∫ s in Ioi (cutoff n), G s ∂μ)
        atTop (𝓝 ((∫ s, F s ∂μ) - b)) := by
      simpa only [hid'] using
        (hc.integral_tendsto_of_countably_generated hF).sub hboundary
    exact hc.integrable_of_integral_tendsto_of_nonneg_ae
      ((∫ s, F s ∂μ) - b) hGcut hGnonneg hlim
  exact ⟨⟨hbackward, fun hG => (hforward hG).1⟩,
    fun hG => (hforward hG).2⟩

end ActualGammaDomainPassageDraft

/- UNCOMPILED FINAL CONSUMER FRAGMENT, r2713 explicit conditional cast bridge. Append in one Lean file after:
(1) root-corrected stage3 + far stages4-v2/5-v2/6/7;
(2) ActualGammaCommonCutoff.integrated.v2-api-fix.transient.draft.lean;
(3) ActualGammaDomainPassage.actual-energies.transient.draft.lean, with its
single anonymous example renamed PRIVATE actual_nonnegative_energy_domain_passage
ONLY IN THE NEW ASSEMBLY. Original frozen sources must remain unchanged.
All three namespaces' private aliases must be in this same compilation unit.
No canonical/Describe/Reg addition or formal acceptance claim. -/

namespace ActualGammaDomainPassageDraft

open Filter
open scoped Topology ComplexConjugate

/-- Exact consumption of the actual fixed-cutoff proof, full lattice
boundary limit, and nonnegative-energy AECover passage. No full zero-cutoff
energy is assumed finite. The result is a domain equivalence, and on that
domain it identifies the two finite actual energies and their boundary pair. -/
private theorem actual_centered_gamma_full_domain_equivalence
    (a : ℝ) (ha : 0 < a) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    letI : Fact (0 < 2 * a) := ⟨by linarith⟩
    (IntegrableOn (zeroEnergyDensity (2 * a) (-a) u) (Ioi 0) ↔
      IntegrableOn (periodicEnergyDensity (2 * a) (-a) u) (Ioi 0)) ∧
    (IntegrableOn (periodicEnergyDensity (2 * a) (-a) u) (Ioi 0) →
      (∫ s in Ioi 0, zeroEnergyDensity (2 * a) (-a) u s) =
        (∫ s in Ioi 0, periodicEnergyDensity (2 * a) (-a) u s) +
          cutoffBoundaryPair (2 * a) (-a) 0 u) := by
  letI : Fact (0 < 2 * a) := ⟨by linarith⟩
  have hend : -a + 2 * a = a := by ring
  have hWindow :
      ActualGammaCommonCutoffDraft20261017.windowMeasure (2 * a) (-a) =
        volume.restrict (Ioc (-a) a) := by
    simp only [ActualGammaCommonCutoffDraft20261017.windowMeasure, hend]
  have huCommon : MemLp u 2
      (ActualGammaCommonCutoffDraft20261017.windowMeasure (2 * a) (-a)) := by
    rw [hWindow]
    exact hu
  have hCommon (ε : ℝ) (hε : 0 < ε) :=
    ActualGammaCommonCutoffDraft20261017.actual_common_cutoff_integrable_and_identity
      (2 * a) (-a) ε hε u huCommon
  have hcut0 : ∀ ε : ℝ, 0 < ε →
      IntegrableOn (zeroEnergyDensity (2 * a) (-a) u) (Ioi ε) := by
    intro ε hε
    change IntegrableOn
      (fun s => ActualGammaCommonCutoffDraft20261017.density s *
        ActualGammaCommonCutoffDraft20261017.zeroTranslationEnergy (2 * a) (-a) u s)
      (Ioi ε)
    exact (hCommon ε hε).1
  have hcutP : ∀ ε : ℝ, 0 < ε →
      IntegrableOn (periodicEnergyDensity (2 * a) (-a) u) (Ioi ε) := by
    intro ε hε
    change IntegrableOn
      (fun s => ActualGammaCommonCutoffDraft20261017.density s *
        ActualGammaCommonCutoffDraft20261017.periodicTranslationEnergy (2 * a) (-a) u s)
      (Ioi ε)
    exact (hCommon ε hε).2.1
  -- Explicit real-tsum/complex-tsum bridge: the expected complex type
  -- propagates through the boundary sum, so this is not a defeq change.
  have hKernel (ε : ℝ) (p : ℝ × ℝ) :
      (∑' m : ℤ, if m = 0 then (0 : ℂ) else
        (cutoffKernel ε (p.1 - p.2 + m • (2 * a)) : ℂ)) =
      (ActualGammaCommonCutoffDraft20261017.imageKernel
        (2 * a) ε p.1 p.2 : ℂ) := by
    unfold ActualGammaCommonCutoffDraft20261017.imageKernel
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro m
    by_cases hm : m = 0 <;>
      simp [hm, cutoffKernel, ActualGammaCommonCutoffDraft20261017.cutoffKernel]
  have hBoundary_common (ε : ℝ) :
      cutoffBoundaryPair (2 * a) (-a) ε u =
        (∫ p : ℝ × ℝ, conj (u p.1) *
          (ActualGammaCommonCutoffDraft20261017.imageKernel
            (2 * a) ε p.1 p.2 : ℂ) * u p.2
          ∂(ActualGammaCommonCutoffDraft20261017.windowMeasure (2 * a) (-a)).prod
            (ActualGammaCommonCutoffDraft20261017.windowMeasure (2 * a) (-a))).re := by
    simp only [cutoffBoundaryPair, hKernel, intervalMeasure,
      ActualGammaCommonCutoffDraft20261017.windowMeasure]
  have hfinite : ∀ ε : ℝ, 0 < ε →
      (∫ s in Ioi ε, zeroEnergyDensity (2 * a) (-a) u s) =
        (∫ s in Ioi ε, periodicEnergyDensity (2 * a) (-a) u s) +
          cutoffBoundaryPair (2 * a) (-a) ε u := by
    intro ε hε
    rw [hBoundary_common]
    change ActualGammaCommonCutoffDraft20261017.zeroCutoffEnergy (2 * a) (-a) ε u =
      ActualGammaCommonCutoffDraft20261017.periodicCutoffEnergy (2 * a) (-a) ε u +
        (∫ p : ℝ × ℝ, conj (u p.1) *
          (ActualGammaCommonCutoffDraft20261017.imageKernel (2 * a) ε p.1 p.2 : ℂ) *
          u p.2 ∂(ActualGammaCommonCutoffDraft20261017.windowMeasure (2 * a) (-a)).prod
            (ActualGammaCommonCutoffDraft20261017.windowMeasure (2 * a) (-a))).re
    exact (hCommon ε hε).2.2.2
  have hBoundary_eq (ε : ℝ) : cutoffBoundaryPair (2 * a) (-a) ε u =
      ActualGammaCornerTransportDraft20261017.actualIocBoundaryPair a ε u := by
    have hSum (p : ℝ × ℝ) :
        (∑' m : ℤ, if m = 0 then (0 : ℂ) else
          (cutoffKernel ε (p.1 - p.2 + m • (2 * a)) : ℂ)) =
        ∑' m : ℤ, if m = 0 then (0 : ℂ) else
          if ε < |p.1 - p.2 + m • (2 * a)| then
            (ActualGammaCornerTransportDraft20261017.actualDensity
              |p.1 - p.2 + m • (2 * a)| : ℂ) else 0 := by
      apply tsum_congr
      intro m
      by_cases hm : m = 0
      · simp only [hm, if_true]
      · simp only [if_neg hm, cutoffKernel, density,
          ActualGammaCornerTransportDraft20261017.actualDensity]
        split_ifs <;> rfl
    simp only [cutoffBoundaryPair, hSum, intervalMeasure,
      ActualGammaCornerTransportDraft20261017.actualIocBoundaryPair, hend]
  have hboundary : Tendsto
      (fun n : ℕ => cutoffBoundaryPair (2 * a) (-a) (cutoff n) u)
      atTop (𝓝 (cutoffBoundaryPair (2 * a) (-a) 0 u)) := by
    simpa only [hBoundary_eq, cutoff] using
      ActualGammaCornerTransportDraft20261017.actualIocBoundaryPair_nat_tendsto a ha hu
  exact actual_nonnegative_energy_domain_passage (2 * a) (-a) u
    hcut0 hcutP hfinite hboundary

end ActualGammaDomainPassageDraft


/-
TRANSIENT APPLICATION CANDIDATE, NOT COMPILED. No kernel acceptance claimed.
Mathlib pin: db584cd6d46c92f209a44c0f1c829460d327499d.

This file records a proposed exact application of Fourier Parseval and
nonnegative Tonelli. It is not a proposed canonical module/Describe/Reg.
Only this persistent research source is written; no worktree is changed.

The generic endpoint below retains the symbol as an ENNReal lintegral.
The accompanying API/normalization plan explains the last actual-Gamma
specialization using the ALREADY PROVED original private Levy identity
and original private one-frequency integrability theorem, not a new
symbol premise or a new proof of the same mathematical result.
-/


noncomputable section

open MeasureTheory Set AddCircle
open scoped ENNReal ComplexConjugate

namespace ActualGammaPeriodicSpectralEnergyDraft20261017

variable {d : ℝ} [hd : Fact (0 < d)]

private abbrev circleHaar : Measure (AddCircle d) :=
  AddCircle.haarAddCircle

private def circleShift (f : AddCircle d → ℂ) (s : ℝ) : AddCircle d → ℂ :=
  fun x => f (x - (s : AddCircle d))

private def phaseGap (n : ℤ) (s : ℝ) : ℝ :=
  ‖(1 : ℂ) - (@fourier d n) (-(s : AddCircle d))‖ ^ 2

private def angularFrequency (n : ℤ) : ℝ :=
  2 * Real.pi * (n : ℝ) / d

private def circleGapMass (f : AddCircle d → ℂ) (s : ℝ) : ℝ :=
  ∫ x : AddCircle d, ‖f x - circleShift f s x‖ ^ 2 ∂circleHaar

/-- These are the coefficients for the UNNORMALIZED Lebesgue L2 carrier.
Mathlib's fourierCoeff itself uses the probability Haar measure. -/
private def physicalCoeff (f : AddCircle d → ℂ) (n : ℤ) : ℂ :=
  (Real.sqrt d : ℂ) * fourierCoeff f n

private theorem normSq_physicalCoeff (f : AddCircle d → ℂ) (n : ℤ) :
    ‖physicalCoeff f n‖ ^ 2 = d * ‖fourierCoeff f n‖ ^ 2 := by
  simp only [physicalCoeff, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg d), mul_pow,
    Real.sq_sqrt hd.out.le]

private theorem physicalCoeff_liftIoc_eq (t : ℝ) (u : ℝ → ℂ) (n : ℤ) :
    physicalCoeff (AddCircle.liftIoc d t u) n =
      (Real.sqrt d : ℂ) *
        fourierCoeffOn (lt_add_of_pos_right t hd.out) u n := by
  rw [physicalCoeff, fourierCoeff_liftIoc_eq]

omit hd in
/-- Exact angular, rather than cyclic, frequency for the source shift. -/
private theorem fourier_phase_eq_exp (n : ℤ) (s : ℝ) :
    (@fourier d n) (-(s : AddCircle d)) =
      Complex.exp (((-(angularFrequency (d := d) n * s) : ℝ) : ℂ) * Complex.I) := by
  rw [← AddCircle.coe_neg, fourier_coe_apply]
  congr 1
  simp only [angularFrequency, Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_intCast]
  ring

omit hd in
private theorem phaseGap_eq_two_one_sub_cos (n : ℤ) (s : ℝ) :
    phaseGap (d := d) n s =
      2 * (1 - Real.cos (angularFrequency (d := d) n * s)) := by
  have hnorm : Complex.normSq ((@fourier d n) (-(s : AddCircle d))) = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    simp only [fourier_apply, Circle.norm_coe, one_pow]
  have hre : ((@fourier d n) (-(s : AddCircle d))).re =
      Real.cos (angularFrequency (d := d) n * s) := by
    rw [fourier_phase_eq_exp, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  rw [phaseGap, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_one, hnorm]
  simp only [one_mul, Complex.conj_re]
  rw [hre]
  ring

omit hd in
/-- fourier_add adds INDICES; here the character is evaluated at a sum
of spatial points, so use toCircle_add and zsmul_add. -/
private theorem fourier_spatial_add (n : ℤ) (x y : AddCircle d) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

omit hd in
private theorem fourier_neg_index_at_point (n : ℤ) (x : AddCircle d) :
    fourier (-n) x = fourier n (-x) := by
  simp only [fourier_apply, neg_zsmul, zsmul_neg]

/-- Source translation U_s f(x)=f(x-s) has multiplier exp(-i omega_n s).
Haar invariance proves this even before an L1/L2 hypothesis is imposed. -/
private theorem fourierCoeff_circleShift (f : AddCircle d → ℂ) (s : ℝ) (n : ℤ) :
    fourierCoeff (circleShift f s) n =
      fourier n (-(s : AddCircle d)) * fourierCoeff f n := by
  simp only [fourierCoeff, smul_eq_mul, circleShift]
  calc
    (∫ x : AddCircle d, fourier (-n) x * f (x - (s : AddCircle d))
        ∂circleHaar) =
        ∫ x : AddCircle d, fourier (-n) (x + (s : AddCircle d)) * f x
          ∂circleHaar := by
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self (μ := circleHaar)
          (fun x : AddCircle d => fourier (-n) x * f (x - (s : AddCircle d)))
          (s : AddCircle d)).symm
    _ = ∫ x : AddCircle d,
        fourier (-n) (s : AddCircle d) * (fourier (-n) x * f x)
          ∂circleHaar := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [fourier_spatial_add]
        ring
    _ = fourier n (-(s : AddCircle d)) *
        ∫ x : AddCircle d, fourier (-n) x * f x ∂circleHaar := by
      rw [integral_const_mul, fourier_neg_index_at_point]

private theorem circleShift_memLp (f : AddCircle d → ℂ)
    (hf : MemLp f 2 circleHaar) (s : ℝ) :
    MemLp (circleShift f s) 2 circleHaar := by
  exact hf.comp_measurePreserving
    (measurePreserving_sub_right circleHaar (s : AddCircle d))

private theorem fourierCoeff_sub_circleShift (f : AddCircle d → ℂ)
    (hf : MemLp f 2 circleHaar) (s : ℝ) (n : ℤ) :
    fourierCoeff (fun x => f x - circleShift f s x) n =
      (1 - fourier n (-(s : AddCircle d))) * fourierCoeff f n := by
  have hf1 : Integrable f circleHaar := MemLp.integrable (by norm_num) hf
  have hs1 : Integrable (circleShift f s) circleHaar :=
    MemLp.integrable (by norm_num) (circleShift_memLp f hf s)
  calc
    _ = fourierCoeff f n - fourierCoeff (circleShift f s) n := by
      simp only [fourierCoeff, smul_eq_mul, mul_sub]
      exact integral_sub (hf1.fourier_smul (-n)) (hs1.fourier_smul (-n))
    _ = _ := by rw [fourierCoeff_circleShift]; ring

/-- Parseval is only used for one fixed translation. Its L2 energy is
finite automatically; no integrated Gamma energy has been assumed finite. -/
private theorem hasSum_phaseGap_coeff (f : AddCircle d → ℂ)
    (hf : MemLp f 2 circleHaar) (s : ℝ) :
    HasSum (fun n : ℤ => phaseGap (d := d) n s * ‖fourierCoeff f n‖ ^ 2)
      (circleGapMass f s) := by
  let g : AddCircle d → ℂ := fun x => f x - circleShift f s x
  have hg : MemLp g 2 circleHaar := hf.sub (circleShift_memLp f hf s)
  let gLp : Lp ℂ 2 circleHaar := MemLp.toLp g hg
  have hcoef : fourierCoeff gLp = fourierCoeff g :=
    fourierCoeff_congr_ae hg.coeFn_toLp
  have hmass : (∫ x : AddCircle d, ‖gLp x‖ ^ 2 ∂circleHaar) =
      circleGapMass f s := by
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx]
  have h := hasSum_sq_fourierCoeff gLp
  rw [hcoef, hmass] at h
  simpa only [g, fourierCoeff_sub_circleShift f hf s,
    norm_mul, mul_pow, phaseGap] using h

/-- Exact fixed-shift Parseval on the actual unnormalized carrier,
already expressed in ENNReal for the subsequent extended integral. -/
private theorem physicalGapMass_eq_tsum (f : AddCircle d → ℂ)
    (hf : MemLp f 2 circleHaar) (s : ℝ) :
    ENNReal.ofReal (d * circleGapMass f s) =
      ∑' n : ℤ, ENNReal.ofReal (phaseGap (d := d) n s) *
        ENNReal.ofReal (‖physicalCoeff f n‖ ^ 2) := by
  have h := (hasSum_phaseGap_coeff f hf s).mul_left d
  calc
    _ = ENNReal.ofReal (∑' n : ℤ,
        d * (phaseGap (d := d) n s * ‖fourierCoeff f n‖ ^ 2)) :=
      congrArg ENNReal.ofReal h.tsum_eq.symm
    _ = ∑' n : ℤ,
        ENNReal.ofReal (d * (phaseGap (d := d) n s * ‖fourierCoeff f n‖ ^ 2)) :=
      ENNReal.ofReal_tsum_of_nonneg
        (fun n => mul_nonneg hd.out.le
          (mul_nonneg (sq_nonneg _) (sq_nonneg _))) h.summable
    _ = _ := by
      apply tsum_congr
      intro n
      rw [normSq_physicalCoeff]
      have hp : 0 ≤ phaseGap (d := d) n s := sq_nonneg _
      rw [← ENNReal.ofReal_mul hp]
      congr 1
      ring

omit hd in
private theorem measurable_phaseGap (n : ℤ) : Measurable (phaseGap (d := d) n) := by
  have h : Continuous (fun s : ℝ =>
      (1 : ℂ) - (@fourier d n) (-(s : AddCircle d))) :=
    continuous_const.sub
      ((fourier n).continuous.comp (AddCircle.continuous_mk' d).neg)
  exact (h.norm.pow 2).measurable

/-- Complete nonnegative extended spectral equality. Neither side is
assumed finite, and there is no Bochner integral over the shift variable.
The kernel k is arbitrary measurable; ofReal handles its nonnegative part.
For actual Gamma, k is positive on Ioi 0. -/
private theorem extended_circle_energy_eq_tsum
    (k : ℝ → ℝ) (hk : Measurable k) (f : AddCircle d → ℂ)
    (hf : MemLp f 2 circleHaar) :
    (∫⁻ s : ℝ in Ioi 0,
      ENNReal.ofReal (k s) * ENNReal.ofReal (d * circleGapMass f s)) =
      ∑' n : ℤ,
        (∫⁻ s : ℝ in Ioi 0,
          ENNReal.ofReal (k s) * ENNReal.ofReal (phaseGap (d := d) n s)) *
        ENNReal.ofReal (‖physicalCoeff f n‖ ^ 2) := by
  have hmeas (n : ℤ) : Measurable (fun s : ℝ =>
      ENNReal.ofReal (k s) * ENNReal.ofReal (phaseGap (d := d) n s)) :=
    (ENNReal.measurable_ofReal.comp hk).mul
      (ENNReal.measurable_ofReal.comp (measurable_phaseGap n))
  calc
    _ = ∫⁻ s : ℝ in Ioi 0, ∑' n : ℤ,
        (ENNReal.ofReal (k s) * ENNReal.ofReal (phaseGap (d := d) n s)) *
          ENNReal.ofReal (‖physicalCoeff f n‖ ^ 2) := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall fun s => by
        dsimp only
        rw [physicalGapMass_eq_tsum f hf s, ← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro n
        exact (mul_assoc _ _ _).symm
    _ = ∑' n : ℤ, ∫⁻ s : ℝ in Ioi 0,
        (ENNReal.ofReal (k s) * ENNReal.ofReal (phaseGap (d := d) n s)) *
          ENNReal.ofReal (‖physicalCoeff f n‖ ^ 2) :=
      lintegral_tsum fun n => ((hmeas n).mul_const _).aemeasurable
    _ = _ := by
      apply tsum_congr
      intro n
      exact lintegral_mul_const'' _ (hmeas n).aemeasurable

private def windowGapMass (t : ℝ) (u : ℝ → ℂ) (s : ℝ) : ℝ :=
  ∫ x : ℝ in Ioc t (t + d),
    ‖u x - AddCircle.liftIoc d t u ((x - s : ℝ) : AddCircle d)‖ ^ 2

/-- Transport to the source Ioc carrier; endpoint choices affect no L2 class.
This identity uses the standard circle volume of mass d, then Haar mass 1. -/
private theorem windowGapMass_eq_physicalCircleGap
    (t : ℝ) (u : ℝ → ℂ) (s : ℝ) :
    windowGapMass (d := d) t u s =
      d * circleGapMass (AddCircle.liftIoc d t u) s := by
  calc
    _ = ∫ c : AddCircle d,
        ‖AddCircle.liftIoc d t u c -
          AddCircle.liftIoc d t u (c - (s : AddCircle d))‖ ^ 2 := by
      rw [← AddCircle.integral_preimage d t]
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
      rw [AddCircle.liftIoc_coe_apply (p := d) (a := t) (f := u) hx]
      simp only [AddCircle.coe_sub]
    _ = _ := by
      rw [AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure,
        ENNReal.toReal_ofReal hd.out.le]
      rfl

/-- Transient exact application endpoint on the actual interval carrier.
The Fourier coefficient is sqrt(d) times Mathlib's probability-Haar coefficient.
The actual Gamma specialization replaces the displayed frequency lintegral
by ofReal(w(2*pi*n/d)), using the existing original Levy proof. -/
private theorem extended_window_energy_eq_tsum
    (k : ℝ → ℝ) (hk : Measurable k) (t : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc t (t + d)))) :
    (∫⁻ s : ℝ in Ioi 0,
      ENNReal.ofReal (k s) * ENNReal.ofReal (windowGapMass (d := d) t u s)) =
      ∑' n : ℤ,
        (∫⁻ s : ℝ in Ioi 0,
          ENNReal.ofReal (k s) * ENNReal.ofReal (phaseGap (d := d) n s)) *
        ENNReal.ofReal (‖physicalCoeff (AddCircle.liftIoc d t u) n‖ ^ 2) := by
  simp_rw [windowGapMass_eq_physicalCircleGap]
  exact extended_circle_energy_eq_tsum k hk _ hu.memLp_liftIoc.haarAddCircle


/-
TRANSIENT, UNCOMPILED APPEND FRAGMENT. No kernel acceptance claimed.

Append inside ActualGammaPeriodicSpectralEnergyDraft20261017, before
its final end, in ActualGammaPeriodicSpectralEnergy.transient.draft.lean.
Add the original ArchimedeanJumpDecomposition import at the file top.

Integration prerequisite: the ORIGINAL owner declarations
  jump_density_nonnegative
  levy_kernel_integrableOn
  levy_integral_eq_digamma_increment
are private in the pin. Publish the originals with proofs unchanged,
or place their exact application source-locally in the original module.
This fragment deliberately uses the intended original API names and
does not forge public aliases, use mangled private names, duplicate the
symbol proof, or assume the actual symbol identity as a hypothesis.
-/

private abbrev gammaDensity : ℝ → ℝ :=
  D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity

private def gammaIncrement (z : ℝ) : ℝ :=
  (Complex.digamma ((1 / 4 : ℂ) + Complex.I * ((z / 2 : ℝ) : ℂ))).re -
    (Complex.digamma (1 / 4)).re

private theorem measurable_gammaDensity : Measurable gammaDensity := by
  unfold gammaDensity
    D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity
  fun_prop

/-- One frequency is integrable by the ORIGINAL proved Levy theorem.
No finiteness of the sum over all frequencies is needed or asserted. -/
private theorem actual_gamma_spectralWeight (n : ℤ) :
    (∫⁻ s : ℝ in Ioi 0,
      ENNReal.ofReal (gammaDensity s) * ENNReal.ofReal (phaseGap (d := d) n s)) =
      ENNReal.ofReal (gammaIncrement (angularFrequency (d := d) n)) := by
  let z : ℝ := angularFrequency (d := d) n
  have hInt : IntegrableOn
      (fun s : ℝ => 2 * gammaDensity s * (1 - Real.cos (z * s))) (Ioi 0) :=
    D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.levy_kernel_integrableOn z
  have hnn : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      0 ≤ 2 * gammaDensity s * (1 - Real.cos (z * s)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (mul_nonneg (by norm_num)
      (D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.jump_density_nonnegative hs))
      (sub_nonneg.mpr (Real.cos_le_one _))
  calc
    _ = ∫⁻ s : ℝ in Ioi 0,
        ENNReal.ofReal (2 * gammaDensity s * (1 - Real.cos (z * s))) := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      rw [phaseGap_eq_two_one_sub_cos,
        ← ENNReal.ofReal_mul
          (D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.jump_density_nonnegative hs)]
      congr 1
      dsimp only [z]
      ring
    _ = ENNReal.ofReal
        (∫ s : ℝ in Ioi 0, 2 * gammaDensity s * (1 - Real.cos (z * s))) :=
      (ofReal_integral_eq_lintegral_ofReal hInt hnn).symm
    _ = ENNReal.ofReal (gammaIncrement (angularFrequency (d := d) n)) :=
      congrArg ENNReal.ofReal
        (D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.levy_integral_eq_digamma_increment z)

/-- Actual Gamma periodic spectral energy as an ENNReal equality on ALL
of the original interval L2 carrier. In particular neither side is a
prior finite form-domain premise. Set d=2a,t=-a for equation (2). -/
private theorem actual_gamma_periodic_energy_eq_tsum
    (t : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc t (t + d)))) :
    (∫⁻ s : ℝ in Ioi 0,
      ENNReal.ofReal (gammaDensity s) *
        ENNReal.ofReal (windowGapMass (d := d) t u s)) =
      ∑' n : ℤ,
        ENNReal.ofReal (gammaIncrement (angularFrequency (d := d) n)) *
          ENNReal.ofReal (‖physicalCoeff (AddCircle.liftIoc d t u) n‖ ^ 2) := by
  rw [extended_window_energy_eq_tsum gammaDensity measurable_gammaDensity t u hu]
  apply tsum_congr
  intro n
  rw [actual_gamma_spectralWeight]

end ActualGammaPeriodicSpectralEnergyDraft20261017


/- UNCOMPILED TRANSIENT EXACT APPLICATION.
Append after the validated full-domain unit and periodic spectral unit, keeping
all private aliases in one Lean compilation unit. This endpoint retains the
actual frequency integrals until the original digamma API can be consumed.
No new canonical declaration, admission claim or finite-energy premise.
-/

namespace ActualGammaDomainPassageDraft

open MeasureTheory Set
open scoped ENNReal

private theorem actual_gamma_zero_domain_iff_periodic_frequency_sum_finite
    (a : ℝ) (ha : 0 < a) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    letI : Fact (0 < 2 * a) := ⟨by linarith⟩
    IntegrableOn (zeroEnergyDensity (2 * a) (-a) u) (Ioi 0) ↔
      (∑' n : ℤ,
        (∫⁻ s : ℝ in Ioi 0, ENNReal.ofReal (density s) *
          ENNReal.ofReal
            (ActualGammaPeriodicSpectralEnergyDraft20261017.phaseGap
              (d := 2 * a) n s)) *
        ENNReal.ofReal
          (‖ActualGammaPeriodicSpectralEnergyDraft20261017.physicalCoeff
            (AddCircle.liftIoc (2 * a) (-a) u) n‖ ^ 2)) < ∞ := by
  letI : Fact (0 < 2 * a) := ⟨by linarith⟩
  have hend : -a + 2 * a = a := by ring
  have huCommon : MemLp u 2
      (ActualGammaCommonCutoffDraft20261017.windowMeasure (2 * a) (-a)) := by
    simpa only [ActualGammaCommonCutoffDraft20261017.windowMeasure, hend] using hu
  have hdensity : Measurable density := by
    unfold density
      D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity
    fun_prop
  have hmeas : AEStronglyMeasurable
      (periodicEnergyDensity (2 * a) (-a) u) (volume.restrict (Ioi (0 : ℝ))) := by
    have h := hdensity.aestronglyMeasurable.mul
      (ActualGammaCommonCutoffDraft20261017.periodicTranslationEnergy_aestronglyMeasurable
        (2 * a) (-a) u huCommon)
    exact h.restrict
  have hnonneg : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      0 ≤ periodicEnergyDensity (2 * a) (-a) u s := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (density_nonneg hs)
      (integral_nonneg fun x => Complex.normSq_nonneg _)
  have hMass (s : ℝ) :
      ActualGammaPeriodicSpectralEnergyDraft20261017.windowGapMass
        (d := 2 * a) (-a) u s =
      ActualGammaCommonCutoffDraft20261017.periodicTranslationEnergy
        (2 * a) (-a) u s := by
    simp only [ActualGammaPeriodicSpectralEnergyDraft20261017.windowGapMass,
      ActualGammaCommonCutoffDraft20261017.periodicTranslationEnergy,
      ActualGammaCommonCutoffDraft20261017.periodicExtension,
      ActualGammaCommonCutoffDraft20261017.windowMeasure,
      Complex.normSq_eq_norm_sq]
  have hEnergy :=
    ActualGammaPeriodicSpectralEnergyDraft20261017.extended_window_energy_eq_tsum
      density hdensity (-a) u huCommon
  have hLinear :
      (∫⁻ s : ℝ in Ioi 0,
        ENNReal.ofReal (periodicEnergyDensity (2 * a) (-a) u s)) =
      ∫⁻ s : ℝ in Ioi 0,
        ENNReal.ofReal (density s) *
          ENNReal.ofReal
            (ActualGammaPeriodicSpectralEnergyDraft20261017.windowGapMass
              (d := 2 * a) (-a) u s) := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    rw [hMass]
    exact ENNReal.ofReal_mul (density_nonneg hs)
  rw [(actual_centered_gamma_full_domain_equivalence a ha u hu).1]
  rw [← hEnergy, ← hLinear]
  exact ⟨fun h => (hasFiniteIntegral_iff_ofReal hnonneg).mp h.2,
    fun h => ⟨hmeas, (hasFiniteIntegral_iff_ofReal hnonneg).mpr h⟩⟩

end ActualGammaDomainPassageDraft


/- UNCOMPILED TRANSIENT SOURCE-LOCAL EXACT APPLICATION.
Append after the source-local original Gamma owner body, the accepted periodic
spectral unit, and the frequency-finiteness consumer. This is the actual digamma
specialization of that consumer; no prior finite-energy premise is introduced.
The original owner must not be imported in addition to its source-local body.
-/

namespace ActualGammaDomainPassageDraft

open MeasureTheory Set
open scoped ENNReal

private theorem actual_gamma_zero_domain_iff_digamma_weighted_sum_finite
    (a : ℝ) (ha : 0 < a) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    letI : Fact (0 < 2 * a) := ⟨by linarith⟩
    IntegrableOn (zeroEnergyDensity (2 * a) (-a) u) (Ioi 0) ↔
      (∑' n : ℤ,
        ENNReal.ofReal
          (ActualGammaPeriodicSpectralEnergyDraft20261017.gammaIncrement
            (ActualGammaPeriodicSpectralEnergyDraft20261017.angularFrequency
              (d := 2 * a) n)) *
        ENNReal.ofReal
          (‖ActualGammaPeriodicSpectralEnergyDraft20261017.physicalCoeff
            (AddCircle.liftIoc (2 * a) (-a) u) n‖ ^ 2)) < ∞ := by
  letI : Fact (0 < 2 * a) := ⟨by linarith⟩
  have hweight (n : ℤ) :
      (∫⁻ s : ℝ in Ioi 0,
        ENNReal.ofReal (density s) *
          ENNReal.ofReal
            (ActualGammaPeriodicSpectralEnergyDraft20261017.phaseGap
              (d := 2 * a) n s)) =
        ENNReal.ofReal
          (ActualGammaPeriodicSpectralEnergyDraft20261017.gammaIncrement
            (ActualGammaPeriodicSpectralEnergyDraft20261017.angularFrequency
              (d := 2 * a) n)) := by
    simpa only [density,
      ActualGammaPeriodicSpectralEnergyDraft20261017.gammaDensity] using
      ActualGammaPeriodicSpectralEnergyDraft20261017.actual_gamma_spectralWeight
        (d := 2 * a) n
  simpa only [hweight] using
    actual_gamma_zero_domain_iff_periodic_frequency_sum_finite a ha u hu

end ActualGammaDomainPassageDraft

/-
SOURCE-LOCAL CANDIDATE V2, NOT COMPILED, 2026-10-18.

V1 was included in the parent's real v4.33 build; this v2 fixes its reported
elaboration errors from build/core-v433-v1-build.log. V1 is retained unchanged.
No v2 compilation or kernel acceptance is claimed.

Append this fragment to the exact immutable owner unit
  ActualGammaDigammaDomain.actual-energy-v1.immutable-source.lean
  SHA256 8d88a4df48d546aa7e3c8fbcc069ddf85654515a6fbe8c3753099103f9f3badf
after hoisting the following extra imports to its import block:
  import Mathlib.Analysis.Calculus.ContDiff.RCLike
  import Mathlib.Analysis.SpecialFunctions.SmoothTransition
  import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
  import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

This fragment deliberately reuses the owner's source-private
  actualDensity, gammaCk, gammaCk_pos, actual_density_pos,
  actual_density_le_gammaCk_div, actual_density_measurable,
  ActualGammaCommonCutoffDraft20261017.actual_density_tail_integrable.
Do not import mangled private names from a separately compiled owner module.

No kernel or elaboration acceptance is claimed. The accompanying frontier
document records validation status and the remaining integration boundary.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace ActualGammaCornerTransportDraft20261017

/-! The actual smooth cutoff, rather than an assumed cutoff supplier. -/

private def actualCutoffEta (a ε x : ℝ) : ℝ :=
  Real.smoothTransition ((x + a) / ε - 1) *
    Real.smoothTransition ((a - x) / ε - 1)

private def actualCutoffMask (a ε x : ℝ) : ℝ :=
  if x ∈ Ioo (-a) a then 1 - actualCutoffEta a ε x else 0

private theorem actualCutoffEta_contDiff (a ε : ℝ) :
    ContDiff ℝ ∞ (actualCutoffEta a ε) := by
  unfold actualCutoffEta
  fun_prop

private theorem actualCutoffEta_range (a ε x : ℝ) :
    0 ≤ actualCutoffEta a ε x ∧ actualCutoffEta a ε x ≤ 1 := by
  have h₁ := Real.smoothTransition.nonneg ((x + a) / ε - 1)
  have h₂ := Real.smoothTransition.nonneg ((a - x) / ε - 1)
  have h₃ := Real.smoothTransition.le_one ((x + a) / ε - 1)
  have h₄ := Real.smoothTransition.le_one ((a - x) / ε - 1)
  refine ⟨mul_nonneg h₁ h₂, ?_⟩
  exact (mul_le_mul_of_nonneg_right h₃ h₂).trans (by simpa using h₄)

private theorem actualCutoffMask_measurable (a ε : ℝ) :
    Measurable (actualCutoffMask a ε) := by
  have hη := (actualCutoffEta_contDiff a ε).continuous.measurable
  exact Measurable.ite measurableSet_Ioo (measurable_const.sub hη) measurable_const

private theorem actualCutoffMask_range (a ε x : ℝ) :
    0 ≤ actualCutoffMask a ε x ∧ actualCutoffMask a ε x ≤ 1 := by
  have hη := actualCutoffEta_range a ε x
  by_cases hx : x ∈ Ioo (-a) a
  · simp only [actualCutoffMask, if_pos hx]
    constructor <;> linarith
  · simp only [actualCutoffMask, if_neg hx]
    norm_num

private theorem actualCutoffMask_vanish {a ε x : ℝ} (hε : 0 < ε)
    (hleft : 2 * ε ≤ a + x) (hright : 2 * ε ≤ a - x) :
    actualCutoffMask a ε x = 0 := by
  have hx : x ∈ Ioo (-a) a := by constructor <;> linarith
  have hl : 1 ≤ (x + a) / ε - 1 := by
    have h : 2 ≤ (x + a) / ε := (le_div_iff₀ hε).2 (by linarith)
    linarith
  have hr : 1 ≤ (a - x) / ε - 1 := by
    have h : 2 ≤ (a - x) / ε := (le_div_iff₀ hε).2 hright
    linarith
  simp only [actualCutoffMask, if_pos hx, actualCutoffEta,
    Real.smoothTransition.one_of_one_le hl,
    Real.smoothTransition.one_of_one_le hr, one_mul, sub_self]

private theorem smoothTransition_has_global_abs_bound :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ x y : ℝ,
      |Real.smoothTransition x - Real.smoothTransition y| ≤ H * |x - y| := by
  obtain ⟨K, hK⟩ :=
    (Real.smoothTransition.contDiff (n := 1)).contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_Icc (0 : ℝ) 1) isCompact_Icc
  refine ⟨(K : ℝ), K.coe_nonneg, ?_⟩
  intro x y
  let px := projIcc (0 : ℝ) 1 zero_le_one x
  let py := projIcc (0 : ℝ) 1 zero_le_one y
  have hproj : |(px : ℝ) - (py : ℝ)| ≤ |x - y| := by
    simpa only [px, py, NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq] using
      (LipschitzWith.projIcc (a := (0 : ℝ)) (b := 1) zero_le_one).dist_le_mul x y
  have hcompact : |Real.smoothTransition (px : ℝ) -
      Real.smoothTransition (py : ℝ)| ≤ (K : ℝ) * |(px : ℝ) - (py : ℝ)| := by
    simpa only [Real.dist_eq] using
      hK.dist_le_mul (px : ℝ) px.property (py : ℝ) py.property
  calc
    |Real.smoothTransition x - Real.smoothTransition y| =
        |Real.smoothTransition (px : ℝ) - Real.smoothTransition (py : ℝ)| := by
      simp only [px, py, Real.smoothTransition.projIcc]
    _ ≤ (K : ℝ) * |(px : ℝ) - (py : ℝ)| := hcompact
    _ ≤ (K : ℝ) * |x - y| := mul_le_mul_of_nonneg_left hproj K.coe_nonneg

private theorem cutoff_product_abs_bound {A B C D : ℝ}
    (hB₀ : 0 ≤ B) (hB₁ : B ≤ 1) (hC₀ : 0 ≤ C) (hC₁ : C ≤ 1) :
    |A * B - C * D| ≤ |A - C| + |B - D| := by
  calc
    |A * B - C * D| = |(A - C) * B + C * (B - D)| := by congr 1 <;> ring
    _ ≤ |(A - C) * B| + |C * (B - D)| := abs_add_le _ _
    _ = |A - C| * B + C * |B - D| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hB₀, abs_of_nonneg hC₀]
    _ ≤ |A - C| * 1 + 1 * |B - D| :=
      add_le_add (mul_le_mul_of_nonneg_left hB₁ (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hC₁ (abs_nonneg _))
    _ = |A - C| + |B - D| := by ring

private theorem actualCutoffEta_abs_bound {H : ℝ}
    (hθ : ∀ x y : ℝ, |Real.smoothTransition x - Real.smoothTransition y| ≤
      H * |x - y|) {a ε : ℝ} (hε : 0 < ε) (x y : ℝ) :
    |actualCutoffEta a ε x - actualCutoffEta a ε y| ≤
      (2 * H / ε) * |x - y| := by
  have hplus : |((x + a) / ε - 1) - ((y + a) / ε - 1)| = |x - y| / ε := by
    rw [show ((x + a) / ε - 1) - ((y + a) / ε - 1) = (x - y) / ε by ring]
    rw [abs_div, abs_of_pos hε]
  have hminus : |((a - x) / ε - 1) - ((a - y) / ε - 1)| = |x - y| / ε := by
    rw [show ((a - x) / ε - 1) - ((a - y) / ε - 1) = (y - x) / ε by ring]
    rw [abs_div, abs_of_pos hε, abs_sub_comm y x]
  have hp := hθ ((x + a) / ε - 1) ((y + a) / ε - 1)
  have hm := hθ ((a - x) / ε - 1) ((a - y) / ε - 1)
  rw [hplus] at hp
  rw [hminus] at hm
  calc
    |actualCutoffEta a ε x - actualCutoffEta a ε y| ≤
        |Real.smoothTransition ((x + a) / ε - 1) -
          Real.smoothTransition ((y + a) / ε - 1)| +
        |Real.smoothTransition ((a - x) / ε - 1) -
          Real.smoothTransition ((a - y) / ε - 1)| :=
      cutoff_product_abs_bound (Real.smoothTransition.nonneg _)
        (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
        (Real.smoothTransition.le_one _)
    _ ≤ H * (|x - y| / ε) + H * (|x - y| / ε) := add_le_add hp hm
    _ = (2 * H / ε) * |x - y| := by ring

private theorem actualCutoffMask_abs_bound {H : ℝ}
    (hθ : ∀ x y : ℝ, |Real.smoothTransition x - Real.smoothTransition y| ≤
      H * |x - y|) {a ε x y : ℝ} (hε : 0 < ε)
    (hx : x ∈ Ioo (-a) a) (hy : y ∈ Ioo (-a) a) :
    |actualCutoffMask a ε x - actualCutoffMask a ε y| ≤
      (2 * H / ε) * |x - y| := by
  simp only [actualCutoffMask, if_pos hx, if_pos hy]
  rw [show (1 - actualCutoffEta a ε x) - (1 - actualCutoffEta a ε y) =
    -(actualCutoffEta a ε x - actualCutoffEta a ε y) by ring, abs_neg]
  exact actualCutoffEta_abs_bound hθ hε x y

private def cutoffDistance (a y : ℝ) : ℝ := min (a - y) (a + y)

private theorem cutoffDistance_pos {a y : ℝ} (hy : y ∈ Ioo (-a) a) :
    0 < cutoffDistance a y := by
  exact lt_min (sub_pos.mpr hy.2) (by linarith [hy.1])

private theorem actualCutoffMask_eventually_zero (a x : ℝ) :
    ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0, actualCutoffMask a ε x = 0 := by
  by_cases hx : x ∈ Ioo (-a) a
  · have hd := cutoffDistance_pos hx
    have hsmall : ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0, ε < cutoffDistance a x / 2 :=
      (eventually_lt_nhds (half_pos hd)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hs
    apply actualCutoffMask_vanish hε
    · have hm := min_le_right (a - x) (a + x)
      change ε < min (a - x) (a + x) / 2 at hs
      linarith
    · have hm := min_le_left (a - x) (a + x)
      change ε < min (a - x) (a + x) / 2 at hs
      linarith
  · exact Eventually.of_forall fun ε => by simp only [actualCutoffMask, if_neg hx]

private theorem actualCutoffMask_tendsto_zero (a x : ℝ) :
    Tendsto (fun ε => actualCutoffMask a ε x) (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  change ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0, (0 : ℝ) = actualCutoffMask a ε x
  filter_upwards [actualCutoffMask_eventually_zero a x] with ε hε
  exact hε.symm

/-! The inner mask interface is fully instantiated by the actual eta below. -/

private structure GammaCutoffMaskData (a L : ℝ) where
  mask : ℝ → ℝ → ℝ
  nonneg_L : 0 ≤ L
  measurable : ∀ ε, Measurable (mask ε)
  range : ∀ ε x, 0 ≤ mask ε x ∧ mask ε x ≤ 1
  vanish : ∀ {ε x}, 0 < ε → 2 * ε ≤ a + x → 2 * ε ≤ a - x → mask ε x = 0
  local_abs_bound : ∀ {ε x y}, 0 < ε → x ∈ Ioo (-a) a → y ∈ Ioo (-a) a →
    |mask ε x - mask ε y| ≤ (L / ε) * |x - y|
  pointwise_zero : ∀ x,
    Tendsto (fun ε => mask ε x) (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0)

private def actualCutoffMaskData {H : ℝ} (hH : 0 ≤ H)
    (hθ : ∀ x y : ℝ, |Real.smoothTransition x - Real.smoothTransition y| ≤
      H * |x - y|) (a : ℝ) : GammaCutoffMaskData a (2 * H) where
  mask := actualCutoffMask a
  nonneg_L := mul_nonneg (by norm_num) hH
  measurable := actualCutoffMask_measurable a
  range := actualCutoffMask_range a
  vanish := actualCutoffMask_vanish
  local_abs_bound := actualCutoffMask_abs_bound hθ
  pointwise_zero := actualCutoffMask_tendsto_zero a

private def cutoffRadialGap (b : ℝ → ℝ) (y r : ℝ) : ℝ :=
  actualDensity r * ((b (y + r) - b y) ^ 2 + (b (y - r) - b y) ^ 2)

private def cutoffFullGap (b : ℝ → ℝ) (y x : ℝ) : ℝ :=
  actualDensity |x - y| * (b x - b y) ^ 2

private def cutoffEnvelope (δ L r : ℝ) : ℝ :=
  if r ≤ δ / 2 then (32 * gammaCk * L ^ 2 / δ ^ 2) * r else 2 * actualDensity r

private def actualExteriorPotential (a y : ℝ) : ℝ :=
  (∫ r in Ioi (a - y), actualDensity r) +
    ∫ r in Ioi (a + y), actualDensity r

private def cutoffConstant (L : ℝ) : ℝ :=
  4 * gammaCk * L ^ 2 + 2 * gammaCk * Real.log 2

private theorem actualDensity_tail_integrable_for_cutoff {r : ℝ} (hr : 0 < r) :
    IntegrableOn actualDensity (Ioi r) := by
  exact ActualGammaCommonCutoffDraft20261017.actual_density_tail_integrable hr

private theorem cutoffRadialGap_measurable {b : ℝ → ℝ} (hb : Measurable b) (y : ℝ) :
    Measurable (cutoffRadialGap b y) := by
  unfold cutoffRadialGap
  exact actual_density_measurable.mul
    ((((hb.comp (measurable_const.add measurable_id)).sub measurable_const).pow_const 2).add
      (((hb.comp (measurable_const.sub measurable_id)).sub measurable_const).pow_const 2))

private theorem cutoffRadialGap_nonneg (b : ℝ → ℝ) (y : ℝ) {r : ℝ} (hr : 0 < r) :
    0 ≤ cutoffRadialGap b y r :=
  mul_nonneg (actual_density_pos hr).le (add_nonneg (sq_nonneg _) (sq_nonneg _))

private theorem GammaCutoffMaskData.radial_le_tail {a L : ℝ}
    (M : GammaCutoffMaskData a L) (ε y : ℝ) {r : ℝ} (hr : 0 < r) :
    cutoffRadialGap (M.mask ε) y r ≤ 2 * actualDensity r := by
  have hp₀ := M.range ε (y + r)
  have hm₀ := M.range ε (y - r)
  have hy₀ := M.range ε y
  have hp : (M.mask ε (y + r) - M.mask ε y) ^ 2 ≤ 1 := by
    have h := sq_le_sq' (by linarith : -(1 : ℝ) ≤ M.mask ε (y + r) - M.mask ε y)
      (by linarith : M.mask ε (y + r) - M.mask ε y ≤ 1)
    simpa only [one_pow] using h
  have hm : (M.mask ε (y - r) - M.mask ε y) ^ 2 ≤ 1 := by
    have h := sq_le_sq' (by linarith : -(1 : ℝ) ≤ M.mask ε (y - r) - M.mask ε y)
      (by linarith : M.mask ε (y - r) - M.mask ε y ≤ 1)
    simpa only [one_pow] using h
  unfold cutoffRadialGap
  calc
    _ ≤ actualDensity r * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (actual_density_pos hr).le
    _ = 2 * actualDensity r := mul_comm _ _

private theorem GammaCutoffMaskData.radial_le_linear {a L ε y r : ℝ}
    (M : GammaCutoffMaskData a L) (hy : y ∈ Ioo (-a) a) (hε : 0 < ε)
    (hr : 0 < r) (hnear : r ≤ cutoffDistance a y / 2) :
    cutoffRadialGap (M.mask ε) y r ≤
      (32 * gammaCk * L ^ 2 / (cutoffDistance a y) ^ 2) * r := by
  let δ := cutoffDistance a y
  have hd : 0 < δ := cutoffDistance_pos hy
  have hL : 0 ≤ L := M.nonneg_L
  have hCk : 0 < gammaCk := gammaCk_pos
  have hdright : δ ≤ a - y := min_le_left _ _
  have hdleft : δ ≤ a + y := min_le_right _ _
  change r ≤ δ / 2 at hnear
  have hyp : y + r ∈ Ioo (-a) a := by constructor <;> linarith
  have hym : y - r ∈ Ioo (-a) a := by constructor <;> linarith
  by_cases hsmall : ε < δ / 4
  · have hyzero : M.mask ε y = 0 := M.vanish hε (by linarith) (by linarith)
    have hpzero : M.mask ε (y + r) = 0 := M.vanish hε (by linarith) (by linarith)
    have hmzero : M.mask ε (y - r) = 0 := M.vanish hε (by linarith) (by linarith)
    have hzero : cutoffRadialGap (M.mask ε) y r = 0 := by
      simp [cutoffRadialGap, hyzero, hpzero, hmzero]
    rw [hzero]
    positivity
  · have hlarge : δ ≤ 4 * ε := by linarith
    have hratio : L / ε ≤ 4 * L / δ := by
      apply (div_le_div_iff₀ hε hd).2
      nlinarith [mul_nonneg M.nonneg_L (sub_nonneg.mpr hlarge)]
    have hp := M.local_abs_bound hε hyp hy
    have hm := M.local_abs_bound hε hym hy
    rw [show (y + r) - y = r by ring, abs_of_pos hr] at hp
    rw [show (y - r) - y = -r by ring, abs_neg, abs_of_pos hr] at hm
    have hbound : (L / ε) * r ≤ 4 * L * r / δ := by
      calc
        (L / ε) * r ≤ (4 * L / δ) * r := mul_le_mul_of_nonneg_right hratio hr.le
        _ = 4 * L * r / δ := by ring
    have hB : 0 ≤ 4 * L * r / δ := by positivity
    have hp₂ : (M.mask ε (y + r) - M.mask ε y) ^ 2 ≤ (4 * L * r / δ) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) hB).2 (hp.trans hbound)
    have hm₂ : (M.mask ε (y - r) - M.mask ε y) ^ 2 ≤ (4 * L * r / δ) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) hB).2 (hm.trans hbound)
    calc
      cutoffRadialGap (M.mask ε) y r ≤
          (gammaCk / r) * ((M.mask ε (y + r) - M.mask ε y) ^ 2 +
            (M.mask ε (y - r) - M.mask ε y) ^ 2) :=
        mul_le_mul_of_nonneg_right (actual_density_le_gammaCk_div hr)
          (add_nonneg (sq_nonneg _) (sq_nonneg _))
      _ ≤ (gammaCk / r) * (2 * (4 * L * r / δ) ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (div_nonneg gammaCk_pos.le hr.le)
      _ = (32 * gammaCk * L ^ 2 / (cutoffDistance a y) ^ 2) * r := by
        change (gammaCk / r) * (2 * (4 * L * r / δ) ^ 2) =
          (32 * gammaCk * L ^ 2 / δ ^ 2) * r
        field_simp [ne_of_gt hr, ne_of_gt hd]
        <;> ring

private theorem GammaCutoffMaskData.radial_le_envelope {a L ε y r : ℝ}
    (M : GammaCutoffMaskData a L) (hy : y ∈ Ioo (-a) a) (hε : 0 < ε)
    (hr : 0 < r) :
    cutoffRadialGap (M.mask ε) y r ≤ cutoffEnvelope (cutoffDistance a y) L r := by
  by_cases hnear : r ≤ cutoffDistance a y / 2
  · simpa only [cutoffEnvelope, if_pos hnear] using M.radial_le_linear hy hε hr hnear
  · simpa only [cutoffEnvelope, if_neg hnear] using M.radial_le_tail ε y hr

private theorem cutoffEnvelope_integrable {δ L : ℝ} (hd : 0 < δ) :
    IntegrableOn (cutoffEnvelope δ L) (Ioi 0) := by
  have hR : 0 < δ / 2 := half_pos hd
  have hline : IntervalIntegrable (fun r : ℝ => (32 * gammaCk * L ^ 2 / δ ^ 2) * r)
      volume 0 (δ / 2) := (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hnear : IntegrableOn (cutoffEnvelope δ L) (Ioc 0 (δ / 2)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).1 hline).congr_fun
      (fun r hr => by simp only [cutoffEnvelope, if_pos hr.2]) measurableSet_Ioc
  have htail_raw : IntegrableOn (fun r => 2 * actualDensity r) (Ioi (δ / 2)) :=
    (actualDensity_tail_integrable_for_cutoff hR).const_mul 2
  have htail : IntegrableOn (cutoffEnvelope δ L) (Ioi (δ / 2)) := by
    apply IntegrableOn.congr_fun htail_raw _ measurableSet_Ioi
    intro r hr
    have hr' : δ / 2 < r := hr
    simp only [cutoffEnvelope, if_neg (not_le.mpr hr')]
  simpa only [Ioc_union_Ioi_eq_Ioi hR.le] using hnear.union htail

private theorem cutoffEnvelope_integral {δ L : ℝ} (hd : 0 < δ) :
    (∫ r in Ioi 0, cutoffEnvelope δ L r) =
      4 * gammaCk * L ^ 2 + 2 * ∫ r in Ioi (δ / 2), actualDensity r := by
  have hR : 0 < δ / 2 := half_pos hd
  have henv := cutoffEnvelope_integrable (L := L) hd
  have htail : IntegrableOn (cutoffEnvelope δ L) (Ioi (δ / 2)) :=
    henv.mono_set (Ioi_subset_Ioi hR.le)
  have hnear : IntervalIntegrable (cutoffEnvelope δ L) volume 0 (δ / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).2
      (henv.mono_set Ioc_subset_Ioi_self)
  have hsplit := intervalIntegral.integral_interval_add_Ioi' hnear htail
  calc
    (∫ r in Ioi 0, cutoffEnvelope δ L r) =
        (∫ r in (0 : ℝ)..(δ / 2), cutoffEnvelope δ L r) +
          ∫ r in Ioi (δ / 2), cutoffEnvelope δ L r := hsplit.symm
    _ = (∫ r in (0 : ℝ)..(δ / 2), (32 * gammaCk * L ^ 2 / δ ^ 2) * r) +
        2 * ∫ r in Ioi (δ / 2), actualDensity r := by
      congr 1
      · rw [intervalIntegral.integral_of_le hR.le, intervalIntegral.integral_of_le hR.le]
        exact setIntegral_congr_fun measurableSet_Ioc fun r hr => by
          simp only [cutoffEnvelope, if_pos hr.2]
      · rw [← integral_const_mul]
        exact setIntegral_congr_fun measurableSet_Ioi fun r hr => by
          have hr' : δ / 2 < r := hr
          simp only [cutoffEnvelope, if_neg (not_le.mpr hr')]
    _ = 4 * gammaCk * L ^ 2 + 2 * ∫ r in Ioi (δ / 2), actualDensity r := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      congr 1
      field_simp [ne_of_gt hd]
      <;> ring

private theorem actualDensity_half_tail_le {δ : ℝ} (hd : 0 < δ) :
    (∫ r in Ioi (δ / 2), actualDensity r) ≤
      gammaCk * Real.log 2 + ∫ r in Ioi δ, actualDensity r := by
  have hR : 0 < δ / 2 := half_pos hd
  have hRd : δ / 2 ≤ δ := by linarith
  have hρR := actualDensity_tail_integrable_for_cutoff hR
  have hρd := actualDensity_tail_integrable_for_cutoff hd
  have hρint : IntervalIntegrable actualDensity volume (δ / 2) δ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hRd).2
      (hρR.mono_set Ioc_subset_Ioi_self)
  have hinv_cont : ContinuousOn (fun r : ℝ => gammaCk / r) (Icc (δ / 2) δ) :=
    continuousOn_const.div continuousOn_id fun r hr => ne_of_gt (hR.trans_le hr.1)
  have hinv_int : IntervalIntegrable (fun r : ℝ => gammaCk / r) volume (δ / 2) δ :=
    hinv_cont.intervalIntegrable_of_Icc (μ := volume) hRd
  have hle : (∫ r in (δ / 2)..δ, actualDensity r) ≤
      ∫ r in (δ / 2)..δ, gammaCk / r := by
    apply intervalIntegral.integral_mono_on hRd hρint hinv_int
    intro r hr
    exact actual_density_le_gammaCk_div (hR.trans_le hr.1)
  have hinv : (∫ r in (δ / 2)..δ, gammaCk / r) = gammaCk * Real.log 2 := by
    change (∫ r in (δ / 2)..δ, gammaCk * r⁻¹) = gammaCk * Real.log 2
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hR hd]
    have hquot : δ / (δ / 2) = 2 := by
      field_simp [ne_of_gt hd]
      <;> ring
    rw [hquot]
  rw [hinv] at hle
  have hsplit := intervalIntegral.integral_interval_add_Ioi hρR hρd
  linarith

private theorem actualDensity_tail_nonneg {δ : ℝ} (hd : 0 < δ) :
    0 ≤ ∫ r in Ioi δ, actualDensity r :=
  setIntegral_nonneg measurableSet_Ioi fun r hr => (actual_density_pos (hd.trans hr)).le

private theorem actualDensity_distance_tail_le_potential {a y : ℝ}
    (hy : y ∈ Ioo (-a) a) :
    (∫ r in Ioi (cutoffDistance a y), actualDensity r) ≤ actualExteriorPotential a y := by
  have hl : 0 < a + y := by linarith [hy.1]
  have hr : 0 < a - y := sub_pos.mpr hy.2
  rcases le_total (a - y) (a + y) with h | h
  · simp only [cutoffDistance, min_eq_left h, actualExteriorPotential]
    linarith [actualDensity_tail_nonneg hl]
  · simp only [cutoffDistance, min_eq_right h, actualExteriorPotential]
    linarith [actualDensity_tail_nonneg hr]

private theorem GammaCutoffMaskData.radial_integrable_and_le {a L ε y : ℝ}
    (M : GammaCutoffMaskData a L) (hy : y ∈ Ioo (-a) a) (hε : 0 < ε) :
    IntegrableOn (cutoffRadialGap (M.mask ε) y) (Ioi 0) ∧
      (∫ r in Ioi 0, cutoffRadialGap (M.mask ε) y r) ≤
        cutoffConstant L + 2 * actualExteriorPotential a y := by
  have hd := cutoffDistance_pos hy
  have henv := cutoffEnvelope_integrable (L := L) hd
  have hdom : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      ‖cutoffRadialGap (M.mask ε) y r‖ ≤ cutoffEnvelope (cutoffDistance a y) L r := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    rw [Real.norm_of_nonneg (cutoffRadialGap_nonneg _ y hr)]
    exact M.radial_le_envelope hy hε hr
  have hgap := henv.mono' (cutoffRadialGap_measurable (M.measurable ε) y).aestronglyMeasurable hdom
  refine ⟨hgap, ?_⟩
  have hle : (∫ r in Ioi 0, cutoffRadialGap (M.mask ε) y r) ≤
      ∫ r in Ioi 0, cutoffEnvelope (cutoffDistance a y) L r := by
    apply integral_mono_ae hgap henv
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact M.radial_le_envelope hy hε hr
  rw [cutoffEnvelope_integral hd] at hle
  have hhalf := actualDensity_half_tail_le hd
  have hpot := actualDensity_distance_tail_le_potential hy
  unfold cutoffConstant
  linarith

private theorem GammaCutoffMaskData.radial_tendsto_zero {a L y : ℝ}
    (M : GammaCutoffMaskData a L) (hy : y ∈ Ioo (-a) a) :
    Tendsto (fun ε => ∫ r in Ioi 0, cutoffRadialGap (M.mask ε) y r)
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0) := by
  have hd := cutoffDistance_pos hy
  have henv := cutoffEnvelope_integrable (L := L) hd
  have hmeas : ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0,
      AEStronglyMeasurable (cutoffRadialGap (M.mask ε) y) (volume.restrict (Ioi 0)) :=
    Eventually.of_forall fun ε => (cutoffRadialGap_measurable (M.measurable ε) y).aestronglyMeasurable
  have hdom : ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0,
      ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
        ‖cutoffRadialGap (M.mask ε) y r‖ ≤ cutoffEnvelope (cutoffDistance a y) L r := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    rw [Real.norm_of_nonneg (cutoffRadialGap_nonneg _ y hr)]
    exact M.radial_le_envelope hy hε hr
  have hlim : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun ε => cutoffRadialGap (M.mask ε) y r)
        (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro r
    have hp := ((M.pointwise_zero (y + r)).sub (M.pointwise_zero y)).pow 2
    have hm := ((M.pointwise_zero (y - r)).sub (M.pointwise_zero y)).pow 2
    have hρ : Tendsto (fun _ε : ℝ => actualDensity r)
        (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (actualDensity r)) := tendsto_const_nhds
    simpa [cutoffRadialGap] using hρ.mul (hp.add hm)
  have h := tendsto_integral_filter_of_dominated_convergence
    (cutoffEnvelope (cutoffDistance a y) L) hmeas hdom henv hlim
  simpa only [integral_zero] using h

/-! Bridge back to the requested full real-line carrier. -/

private theorem cutoffFullGap_integrable_and_radial {b : ℝ → ℝ} (hb : Measurable b)
    (y : ℝ) (hradial : IntegrableOn (cutoffRadialGap b y) (Ioi 0)) :
    Integrable (cutoffFullGap b y) ∧
      (∫ x, cutoffFullGap b y x) = ∫ r in Ioi 0, cutoffRadialGap b y r := by
  let F : ℝ → ℝ := fun r => actualDensity |r| * (b (y + r) - b y) ^ 2
  have hFm : Measurable F :=
    (actual_density_measurable.comp measurable_abs).mul
      (((hb.comp (measurable_const.add measurable_id)).sub measurable_const).pow_const 2)
  have hpositive : IntegrableOn F (Ioi (0 : ℝ)) := by
    apply hradial.mono' hFm.aestronglyMeasurable
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hr' : 0 < r := hr
    have hρ := (actual_density_pos hr').le
    have hF : F r = actualDensity r * (b (y + r) - b y) ^ 2 := by
      simp only [F, abs_of_pos hr']
    rw [hF, Real.norm_of_nonneg (mul_nonneg hρ (sq_nonneg _))]
    unfold cutoffRadialGap
    nlinarith [mul_nonneg hρ (sq_nonneg (b (y - r) - b y))]
  have hnegative : IntegrableOn (fun r => F (-r)) (Ioi (0 : ℝ)) := by
    apply hradial.mono' (hFm.comp measurable_neg).aestronglyMeasurable
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    change ‖F (-r)‖ ≤ cutoffRadialGap b y r
    have hr' : 0 < r := hr
    have hρ := (actual_density_pos hr').le
    have hF : F (-r) = actualDensity r * (b (y - r) - b y) ^ 2 := by
      simp only [F, abs_neg, abs_of_pos hr', ← sub_eq_add_neg]
    rw [hF, Real.norm_of_nonneg (mul_nonneg hρ (sq_nonneg _))]
    unfold cutoffRadialGap
    nlinarith [mul_nonneg hρ (sq_nonneg (b (y + r) - b y))]
  have hleft : IntegrableOn F (Iic (0 : ℝ)) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, neg_preimage, neg_Iic, neg_zero]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).2 hnegative
  have hF : Integrable F := by
    simpa only [Iic_union_Ioi, IntegrableOn, Measure.restrict_univ] using hleft.union hpositive
  have hfull_meas : Measurable (cutoffFullGap b y) :=
    (actual_density_measurable.comp ((measurable_id.sub measurable_const).abs)).mul
      ((hb.sub measurable_const).pow_const 2)
  have hshift : (fun r => cutoffFullGap b y (r + y)) = F := by
    funext r
    simp only [cutoffFullGap, F]
    rw [add_sub_cancel_right, add_comm r y]
  have hfull : Integrable (cutoffFullGap b y) := by
    apply ((measurePreserving_add_right (volume : Measure ℝ) y).integrable_comp
      hfull_meas.aestronglyMeasurable).mp
    change Integrable (fun r => cutoffFullGap b y (r + y))
    rw [hshift]
    exact hF
  refine ⟨hfull, ?_⟩
  calc
    (∫ x, cutoffFullGap b y x) = ∫ r, F r := by
      rw [← integral_add_right_eq_self (cutoffFullGap b y) y, hshift]
    _ = (∫ r in Iic (0 : ℝ), F r) + ∫ r in Ioi (0 : ℝ), F r :=
      (intervalIntegral.integral_Iic_add_Ioi hleft hpositive).symm
    _ = (∫ r in Ioi (0 : ℝ), F (-r)) + ∫ r in Ioi (0 : ℝ), F r := by
      rw [integral_comp_neg_Ioi, neg_zero]
    _ = ∫ r in Ioi (0 : ℝ), F (-r) + F r := (integral_add hnegative hpositive).symm
    _ = ∫ r in Ioi (0 : ℝ), cutoffRadialGap b y r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hr' : 0 < r := hr
      simp only [F, cutoffRadialGap, abs_neg, abs_of_pos hr', ← sub_eq_add_neg]
      ring

/-! Closed actual consumer: all mask hypotheses above are discharged here. -/

theorem actual_smooth_cutoff_commutator_candidate :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      (∀ a ε : ℝ, ContDiff ℝ ∞ (actualCutoffEta a ε)) ∧
      ∀ a y : ℝ, y ∈ Ioo (-a) a →
        ((∀ ε : ℝ, 0 < ε →
            IntegrableOn (cutoffRadialGap (actualCutoffMask a ε) y) (Ioi 0) ∧
              (∫ r in Ioi 0, cutoffRadialGap (actualCutoffMask a ε) y r) ≤
                C0 + 2 * actualExteriorPotential a y) ∧
          Tendsto (fun ε => ∫ r in Ioi 0, cutoffRadialGap (actualCutoffMask a ε) y r)
            (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0)) ∧
        ((∀ ε : ℝ, 0 < ε →
            Integrable (cutoffFullGap (actualCutoffMask a ε) y) ∧
              (∫ x, cutoffFullGap (actualCutoffMask a ε) y x) ≤
                C0 + 2 * actualExteriorPotential a y) ∧
          Tendsto (fun ε => ∫ x, cutoffFullGap (actualCutoffMask a ε) y x)
            (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0)) := by
  obtain ⟨H, hH, hθ⟩ := smoothTransition_has_global_abs_bound
  let L := 2 * H
  have hC : 0 ≤ cutoffConstant L := by
    unfold cutoffConstant
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) gammaCk_pos.le) (sq_nonneg L))
      (mul_nonneg (mul_nonneg (by norm_num) gammaCk_pos.le)
        (Real.log_nonneg (by norm_num)))
  refine ⟨cutoffConstant L, hC, actualCutoffEta_contDiff, ?_⟩
  intro a y hy
  let M : GammaCutoffMaskData a L := actualCutoffMaskData hH hθ a
  refine ⟨⟨fun ε hε => M.radial_integrable_and_le hy hε,
    M.radial_tendsto_zero hy⟩, ?_⟩
  refine ⟨?_, ?_⟩
  · intro ε hε
    have hr := M.radial_integrable_and_le hy hε
    have hf := cutoffFullGap_integrable_and_radial (actualCutoffMask_measurable a ε) y hr.1
    refine ⟨hf.1, ?_⟩
    rw [hf.2]
    exact hr.2
  · have hr := M.radial_tendsto_zero hy
    apply hr.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hi := (M.radial_integrable_and_le hy hε).1
    exact (cutoffFullGap_integrable_and_radial
      (actualCutoffMask_measurable a ε) y hi).2.symm

end ActualGammaCornerTransportDraft20261017

/-
SOURCE-LOCAL CORE HELPER CANDIDATE, NOT COMPILED.

This prepares the exterior-potential budget on the original positive-shift
energy, without requiring a preliminary two-dimensional change of variables.
It is intended for the actual smooth-cutoff core proof, not as an independent
canonical generic-energy module. The actual consumer takes
  nu = (volume.restrict (Ioi 0)).withDensity (fun s => ofReal (rho s)).
All quantities here are ENNReal; the estimate precedes any finiteness premise.
Measurable representatives suffice for the L2 quotient consumer; transport
from arbitrary AE representatives is a remaining integration obligation.

Append after the actual Gamma source unit. Extra imports, if not already
present, belong at the top: MeasureTheory.Integral.Prod,
MeasureTheory.Integral.Lebesgue.Map, MeasureTheory.Measure.WithDensity.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal Classical

namespace ActualGammaCompactCoreDraft20261018

private def directionalEnergy (nu : Measure ℝ) (F : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ s : ℝ, ∫⁻ x : ℝ, ‖F x - F (x - s)‖ₑ ^ 2 ∂volume ∂nu

private def exteriorExitPair (Omega : Set ℝ) (x s : ℝ) : ℝ≥0∞ :=
  (if x - s ∈ Omega then 0 else 1) +
    (if x + s ∈ Omega then 0 else 1)

private def exteriorPotential (nu : Measure ℝ) (Omega : Set ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ s : ℝ, exteriorExitPair Omega x s ∂nu

private theorem exit_pair_pointwise_le (Omega : Set ℝ) (F : ℝ → ℂ)
    (hzero : ∀ x ∉ Omega, F x = 0) (x s : ℝ) :
    (if x - s ∈ Omega then 0 else ‖F x‖ₑ ^ 2) +
      (if x ∈ Omega then 0 else ‖F (x - s)‖ₑ ^ 2) ≤
        ‖F x - F (x - s)‖ₑ ^ 2 := by
  by_cases hx : x ∈ Omega
  · by_cases hy : x - s ∈ Omega
    · simp only [if_pos hx, if_pos hy, zero_add, zero_le]
    · simp [hx, hy, hzero (x - s) hy]
  · by_cases hy : x - s ∈ Omega
    · simp [hx, hy, hzero x hx]
    · simp [hx, hy, hzero x hx, hzero (x - s) hy]

private theorem exit_pair_lintegral_le (Omega : Set ℝ)
    (hOmega : MeasurableSet Omega) (F : ℝ → ℂ) (hF : Measurable F)
    (hzero : ∀ x ∉ Omega, F x = 0) (s : ℝ) :
    (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2 * exteriorExitPair Omega x s) ≤
      ∫⁻ x : ℝ, ‖F x - F (x - s)‖ₑ ^ 2 := by
  have hminus : Measurable (fun x : ℝ =>
      if x - s ∈ Omega then (0 : ℝ≥0∞) else ‖F x‖ₑ ^ 2) :=
    Measurable.ite (hOmega.preimage (measurable_id.sub_const s))
      measurable_const (hF.enorm.pow_const 2)
  have hright : Measurable (fun x : ℝ =>
      if x ∈ Omega then (0 : ℝ≥0∞) else ‖F (x - s)‖ₑ ^ 2) :=
    Measurable.ite hOmega measurable_const
      ((hF.comp (measurable_id.sub_const s)).enorm.pow_const 2)
  have hshift :
      (∫⁻ x : ℝ, if x ∈ Omega then (0 : ℝ≥0∞) else ‖F (x - s)‖ₑ ^ 2) =
        ∫⁻ x : ℝ, if x + s ∈ Omega then (0 : ℝ≥0∞) else ‖F x‖ₑ ^ 2 := by
    simpa only [Function.comp_def, add_sub_cancel_right] using
      ((measurePreserving_add_right (volume : Measure ℝ) s).lintegral_comp hright).symm
  have hbound := lintegral_mono (μ := (volume : Measure ℝ))
    (fun x : ℝ => exit_pair_pointwise_le Omega F hzero x s)
  rw [lintegral_add_left hminus, hshift] at hbound
  calc
    _ = (∫⁻ x : ℝ, if x - s ∈ Omega then (0 : ℝ≥0∞) else ‖F x‖ₑ ^ 2) +
        ∫⁻ x : ℝ, if x + s ∈ Omega then (0 : ℝ≥0∞) else ‖F x‖ₑ ^ 2 := by
      rw [← lintegral_add_left hminus]
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        unfold exteriorExitPair
        by_cases hm : x - s ∈ Omega <;> by_cases hp : x + s ∈ Omega <;>
          simp [hm, hp, mul_add]
    _ ≤ _ := hbound

private theorem exterior_mass_le_directionalEnergy
    (nu : Measure ℝ) [SFinite nu] (Omega : Set ℝ)
    (hOmega : MeasurableSet Omega) (F : ℝ → ℂ) (hF : Measurable F)
    (hzero : ∀ x ∉ Omega, F x = 0) :
    (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2 * exteriorPotential nu Omega x) ≤
      directionalEnergy nu F := by
  have hpair : Measurable (fun p : ℝ × ℝ => exteriorExitPair Omega p.1 p.2) := by
    unfold exteriorExitPair
    exact (Measurable.ite (hOmega.preimage (measurable_fst.sub measurable_snd))
      (measurable_const : Measurable (fun _ : ℝ × ℝ => (0 : ℝ≥0∞)))
      measurable_const).add
      (Measurable.ite (hOmega.preimage (measurable_fst.add measurable_snd))
        measurable_const measurable_const)
  have hproduct : Measurable (fun p : ℝ × ℝ =>
      ‖F p.1‖ₑ ^ 2 * exteriorExitPair Omega p.1 p.2) :=
    ((hF.comp measurable_fst).enorm.pow_const 2).mul hpair
  calc
    _ = ∫⁻ x : ℝ, ∫⁻ s : ℝ,
        ‖F x‖ₑ ^ 2 * exteriorExitPair Omega x s ∂nu := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        unfold exteriorPotential
        exact (lintegral_const_mul' _ _ (by finiteness)).symm
    _ = ∫⁻ s : ℝ, ∫⁻ x : ℝ,
        ‖F x‖ₑ ^ 2 * exteriorExitPair Omega x s ∂volume ∂nu :=
      lintegral_lintegral_swap hproduct.aemeasurable
    _ ≤ _ := lintegral_mono fun s =>
      exit_pair_lintegral_le Omega hOmega F hF hzero s

/- The next cutoff consumer uses two product-difference estimates, averaged,
   so that its two shifted commutators combine into the actual radial K. -/

private theorem complex_norm_add_sq_le (z w : ℂ) :
    ‖z + w‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  have ht := norm_add_le z w
  have hz := norm_nonneg z
  have hw := norm_nonneg w
  have hzw := norm_nonneg (z + w)
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

private theorem cutoff_product_gap_sq_le (a b : ℝ) (z w : ℂ) :
    ‖(a : ℂ) * z - (b : ℂ) * w‖ ^ 2 ≤
      (a ^ 2 + b ^ 2) * ‖z - w‖ ^ 2 +
        (‖z‖ ^ 2 + ‖w‖ ^ 2) * (a - b) ^ 2 := by
  have hleft : (a : ℂ) * z - (b : ℂ) * w =
      (a : ℂ) * (z - w) + ((a - b : ℝ) : ℂ) * w := by push_cast; ring
  have hright : (a : ℂ) * z - (b : ℂ) * w =
      (b : ℂ) * (z - w) + ((a - b : ℝ) : ℂ) * z := by push_cast; ring
  have h₁ := complex_norm_add_sq_le ((a : ℂ) * (z - w)) (((a - b : ℝ) : ℂ) * w)
  have h₂ := complex_norm_add_sq_le ((b : ℂ) * (z - w)) (((a - b : ℝ) : ℂ) * z)
  rw [← hleft] at h₁
  rw [← hright] at h₂
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] at h₁ h₂
  nlinarith

end ActualGammaCompactCoreDraft20261018

/-
UNCOMPILED SOURCE-LOCAL ACTUAL CORE CONSUMER HELPERS.

Append after ActualGammaCoreExteriorBudget.root-v1.uncompiled.fragment.lean.
The actual Gamma consumer uses its positive jump measure and the actual
smooth mask from ActualGammaCutoffCommutator.actual-mask.candidate-20261018.
This source is not a new generic canonical module or a kernel acceptance.
It proves the finite outer majorant directly from mass and the exterior
budget, and handles the first (energy-density) term in the cutoff product
estimate by DCT. The remaining second term uses the actual radial K bound.
-/

namespace ActualGammaCompactCoreDraft20261018

open MeasureTheory Set Filter
open scoped ENNReal Topology

private theorem cutoff_outer_majorant_finite
    (nu : Measure ℝ) [SFinite nu] (Omega : Set ℝ)
    (hOmega : MeasurableSet Omega) (F : ℝ → ℂ) (hF : Measurable F)
    (hzero : ∀ x ∉ Omega, F x = 0)
    (hmass : (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2) < (⊤ : ℝ≥0∞))
    (henergy : directionalEnergy nu F < (⊤ : ℝ≥0∞)) (C : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal C * ‖F x‖ₑ ^ 2 +
      2 * (‖F x‖ₑ ^ 2 * exteriorPotential nu Omega x)) < (⊤ : ℝ≥0∞) := by
  have hpotential :
      (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2 * exteriorPotential nu Omega x) < (⊤ : ℝ≥0∞) :=
    lt_of_le_of_lt
      (exterior_mass_le_directionalEnergy nu Omega hOmega F hF hzero) henergy
  have hM : Measurable (fun x : ℝ => ENNReal.ofReal C * ‖F x‖ₑ ^ 2) := by fun_prop
  rw [lintegral_add_left hM,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ (by norm_num)]
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmass,
      ENNReal.mul_lt_top (by norm_num) hpotential⟩

private def cutoffFirstDensity (b : ℝ → ℝ) (F : ℝ → ℂ)
    (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((b p.2 ^ 2 + b (p.2 - p.1) ^ 2) *
    ‖F p.2 - F (p.2 - p.1)‖ ^ 2)

private def cutoffFirstEnergy (nu : Measure ℝ) (b : ℝ → ℝ)
    (F : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ p : ℝ × ℝ, cutoffFirstDensity b F p ∂nu.prod volume

private theorem cutoffFirstDensity_measurable
    (b : ℝ → ℝ) (hb : Measurable b) (F : ℝ → ℂ) (hF : Measurable F) :
    Measurable (cutoffFirstDensity b F) := by
  unfold cutoffFirstDensity
  fun_prop

private theorem cutoffFirstDensity_le_two_gap
    (b : ℝ → ℝ) (hb : ∀ x, 0 ≤ b x ∧ b x ≤ 1)
    (F : ℝ → ℂ) (p : ℝ × ℝ) :
    cutoffFirstDensity b F p ≤
      2 * ENNReal.ofReal (‖F p.2 - F (p.2 - p.1)‖ ^ 2) := by
  have hx := hb p.2
  have hy := hb (p.2 - p.1)
  have hcoef : b p.2 ^ 2 + b (p.2 - p.1) ^ 2 ≤ 2 := by
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2),
      mul_nonneg hy.1 (sub_nonneg.mpr hy.2)]
  have hpoint := mul_le_mul_of_nonneg_right hcoef
    (sq_nonneg ‖F p.2 - F (p.2 - p.1)‖)
  calc
    _ ≤ ENNReal.ofReal (2 * ‖F p.2 - F (p.2 - p.1)‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal hpoint
    _ = _ := by simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]

private theorem cutoffFirstEnergy_tendsto_zero
    (nu : Measure ℝ) [SFinite nu] (F : ℝ → ℂ) (hF : Measurable F)
    (henergy : directionalEnergy nu F < (⊤ : ℝ≥0∞)) (b : ℝ → ℝ → ℝ)
    (hb : ∀ ε, Measurable (b ε))
    (hbound : ∀ ε > 0, ∀ x, 0 ≤ b ε x ∧ b ε x ≤ 1)
    (hzero : ∀ x, Tendsto (fun ε => b ε x) (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0)) :
    Tendsto (fun ε => cutoffFirstEnergy nu (b ε) F)
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0) := by
  let gap : ℝ × ℝ → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (‖F p.2 - F (p.2 - p.1)‖ ^ 2)
  have hgap : Measurable gap := by dsimp only [gap]; fun_prop
  have hgapIntegral : (∫⁻ p : ℝ × ℝ, gap p ∂nu.prod volume) =
      directionalEnergy nu F := by
    rw [lintegral_prod _ hgap.aemeasurable]
    unfold directionalEnergy
    apply lintegral_congr_ae
    exact Eventually.of_forall fun s => by
      apply lintegral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only [gap]
        rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
  have hfinite : (∫⁻ p : ℝ × ℝ, 2 * gap p ∂nu.prod volume) ≠ (⊤ : ℝ≥0∞) := by
    rw [lintegral_const_mul' _ _ (by norm_num), hgapIntegral]
    exact (ENNReal.mul_lt_top (by norm_num) henergy).ne
  have hmeas : ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0,
      Measurable (cutoffFirstDensity (b ε) F) :=
    Eventually.of_forall fun ε => cutoffFirstDensity_measurable _ (hb ε) _ hF
  have hdom : ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0,
      ∀ᵐ p ∂nu.prod volume, cutoffFirstDensity (b ε) F p ≤ 2 * gap p := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Eventually.of_forall fun p => cutoffFirstDensity_le_two_gap _ (hbound ε hε) F p
  have hlim : ∀ᵐ p ∂nu.prod volume,
      Tendsto (fun ε => cutoffFirstDensity (b ε) F p)
        (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) := by
    exact Eventually.of_forall fun p => by
      have hreal : Tendsto (fun ε =>
          (b ε p.2 ^ 2 + b ε (p.2 - p.1) ^ 2) *
            ‖F p.2 - F (p.2 - p.1)‖ ^ 2)
          (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ)) := by
        simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, zero_mul] using
          (((hzero p.2).pow 2).add ((hzero (p.2 - p.1)).pow 2)).mul_const
            (‖F p.2 - F (p.2 - p.1)‖ ^ 2)
      simpa only [cutoffFirstDensity, ENNReal.ofReal_zero, Function.comp_def] using
        (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
  simpa only [cutoffFirstEnergy, lintegral_zero] using
    tendsto_lintegral_filter_of_dominated_convergence
      (μ := nu.prod volume) (fun p => 2 * gap p) hmeas hdom hfinite hlim

end ActualGammaCompactCoreDraft20261018

/-
UNCOMPILED SOURCE-LOCAL CUTOFF ENERGY CANDIDATE, 2026-10-18.

Append after ActualGammaCoreExteriorBudget.root-v2.uncompiled.fragment.lean
and ActualGammaCoreOuterDCT.root-v1.uncompiled.fragment.lean in their same
source-local unit. Reuses cutoff_product_gap_sq_le without reproving it.
Private names below are actual core-use helpers, not canonical wrappers.

The source was prepared D-only with no build or WT edit. API evidence was
read from Mathlib db584cd6d46c92f209a44c0f1c829460d327499d. Dev has moved to
Lean v4.35 / Mathlib 56a005855, so compatible elaboration and kernel checking
remain required. No acceptance is claimed for these proof terms.

For fixed positive-shift parameter s (indeed the algebra holds for any s),
the shifted-F commutator term is translated only by x=y+s in Lebesgue measure.
The two terms become |F(y)|^2 times the sum of forward/backward mask gaps.
Tonelli then exchanges the scale and space integrals. No 2D kernel change of
variables, finiteness assumption, subtraction of infinities, or assumption
that b is bounded is used. The actual positive Gamma scale measure may be
substituted for the arbitrary SFinite nu at the final core consumer.
-/

namespace ActualGammaCompactCoreDraft20261018

open MeasureTheory Set Filter
open scoped ENNReal Topology

private def radialMaskEnergy (nu : Measure ℝ) (b : ℝ → ℝ) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ s : ℝ, ENNReal.ofReal
    ((b (y + s) - b y) ^ 2 + (b (y - s) - b y) ^ 2) ∂nu

private theorem radialMaskEnergy_measurable
    (nu : Measure ℝ) [SFinite nu] (b : ℝ → ℝ) (hb : Measurable b) :
    Measurable (radialMaskEnergy nu b) := by
  have hpair : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal
      ((b (p.1 + p.2) - b p.1) ^ 2 + (b (p.1 - p.2) - b p.1) ^ 2)) := by
    fun_prop
  exact hpair.lintegral_prod_right'

/-- At a fixed scale, only the term containing F(x-s) is translated. -/
private theorem cutoff_commutator_lintegral_eq_radial
    (b : ℝ → ℝ) (hb : Measurable b) (F : ℝ → ℂ) (hF : Measurable F) (s : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal
      ((‖F x‖ ^ 2 + ‖F (x - s)‖ ^ 2) * (b x - b (x - s)) ^ 2)) =
      ∫⁻ y : ℝ, ‖F y‖ₑ ^ 2 * ENNReal.ofReal
        ((b (y + s) - b y) ^ 2 + (b (y - s) - b y) ^ 2) := by
  have hnorm (z : ℂ) : ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := by
    rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
  have hsplit (x : ℝ) : ENNReal.ofReal
      ((‖F x‖ ^ 2 + ‖F (x - s)‖ ^ 2) * (b x - b (x - s)) ^ 2) =
        ‖F x‖ₑ ^ 2 * ENNReal.ofReal ((b x - b (x - s)) ^ 2) +
          ‖F (x - s)‖ₑ ^ 2 * ENNReal.ofReal ((b x - b (x - s)) ^ 2) := by
    rw [ENNReal.ofReal_mul (add_nonneg (sq_nonneg ‖F x‖) (sq_nonneg ‖F (x - s)‖)),
      ENNReal.ofReal_add (sq_nonneg ‖F x‖) (sq_nonneg ‖F (x - s)‖)]
    simp only [hnorm, add_mul]
  have hminus : Measurable (fun x : ℝ =>
      ‖F x‖ₑ ^ 2 * ENNReal.ofReal ((b x - b (x - s)) ^ 2)) := by fun_prop
  have hshifted : Measurable (fun x : ℝ =>
      ‖F (x - s)‖ₑ ^ 2 * ENNReal.ofReal ((b x - b (x - s)) ^ 2)) := by fun_prop
  have hplus : Measurable (fun y : ℝ =>
      ‖F y‖ₑ ^ 2 * ENNReal.ofReal ((b (y + s) - b y) ^ 2)) := by fun_prop
  have hshift :
      (∫⁻ x : ℝ, ‖F (x - s)‖ₑ ^ 2 * ENNReal.ofReal ((b x - b (x - s)) ^ 2)) =
        ∫⁻ y : ℝ, ‖F y‖ₑ ^ 2 * ENNReal.ofReal ((b (y + s) - b y) ^ 2) := by
    simpa only [Function.comp_def, add_sub_cancel_right] using
      ((measurePreserving_add_right (volume : Measure ℝ) s).lintegral_comp hshifted).symm
  calc
    _ = ∫⁻ x : ℝ,
        ‖F x‖ₑ ^ 2 * ENNReal.ofReal ((b x - b (x - s)) ^ 2) +
          ‖F (x - s)‖ₑ ^ 2 * ENNReal.ofReal ((b x - b (x - s)) ^ 2) :=
      lintegral_congr_ae (Eventually.of_forall hsplit)
    _ = (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2 * ENNReal.ofReal ((b x - b (x - s)) ^ 2)) +
        ∫⁻ x : ℝ, ‖F (x - s)‖ₑ ^ 2 * ENNReal.ofReal ((b x - b (x - s)) ^ 2) :=
      lintegral_add_left hminus _
    _ = (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2 * ENNReal.ofReal ((b x - b (x - s)) ^ 2)) +
        ∫⁻ y : ℝ, ‖F y‖ₑ ^ 2 * ENNReal.ofReal ((b (y + s) - b y) ^ 2) := by
      rw [hshift]
    _ = (∫⁻ y : ℝ, ‖F y‖ₑ ^ 2 * ENNReal.ofReal ((b (y + s) - b y) ^ 2)) +
        ∫⁻ y : ℝ, ‖F y‖ₑ ^ 2 * ENNReal.ofReal ((b y - b (y - s)) ^ 2) := add_comm _ _
    _ = ∫⁻ y : ℝ,
        ‖F y‖ₑ ^ 2 * ENNReal.ofReal ((b (y + s) - b y) ^ 2) +
          ‖F y‖ₑ ^ 2 * ENNReal.ofReal ((b y - b (y - s)) ^ 2) :=
      (lintegral_add_left hplus _).symm
    _ = _ := by
      apply lintegral_congr_ae
      exact Eventually.of_forall fun y => by
        dsimp only
        have hsq : (b y - b (y - s)) ^ 2 = (b (y - s) - b y) ^ 2 := by ring
        rw [hsq, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), mul_add]

/-- The positive-scale cutoff estimate with the exact radial commutator.
Its coefficient is one: the averaged product-gap inequality was already
proved by the exterior-budget helper and is only consumed here. -/
private theorem directionalEnergy_cutoff_le
    (nu : Measure ℝ) [SFinite nu] (b : ℝ → ℝ) (hb : Measurable b)
    (F : ℝ → ℂ) (hF : Measurable F) :
    directionalEnergy nu (fun x => (b x : ℂ) * F x) ≤
      cutoffFirstEnergy nu b F +
        ∫⁻ y : ℝ, ‖F y‖ₑ ^ 2 * radialMaskEnergy nu b y := by
  let G : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ‖(b p.2 : ℂ) * F p.2 - (b (p.2 - p.1) : ℂ) * F (p.2 - p.1)‖ₑ ^ 2
  let J : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal
    ((‖F p.2‖ ^ 2 + ‖F (p.2 - p.1)‖ ^ 2) * (b p.2 - b (p.2 - p.1)) ^ 2)
  have hG : Measurable G := by dsimp only [G]; fun_prop
  have hJ : Measurable J := by dsimp only [J]; fun_prop
  have hR : Measurable (fun p : ℝ × ℝ =>
      ‖F p.2‖ₑ ^ 2 * ENNReal.ofReal
        ((b (p.2 + p.1) - b p.2) ^ 2 + (b (p.2 - p.1) - b p.2) ^ 2)) := by
    fun_prop
  have hpoint (p : ℝ × ℝ) : G p ≤ cutoffFirstDensity b F p + J p := by
    have h := ENNReal.ofReal_le_ofReal
      (cutoff_product_gap_sq_le (b p.2) (b (p.2 - p.1)) (F p.2) (F (p.2 - p.1)))
    rw [ENNReal.ofReal_add
      (mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))
      (mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)),
      ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm] at h
    exact h
  have hJradial : (∫⁻ p : ℝ × ℝ, J p ∂nu.prod volume) =
      ∫⁻ y : ℝ, ‖F y‖ₑ ^ 2 * radialMaskEnergy nu b y := by
    calc
      _ = ∫⁻ s : ℝ, ∫⁻ x : ℝ, J (s, x) ∂volume ∂nu :=
        lintegral_prod J hJ.aemeasurable
      _ = ∫⁻ s : ℝ, ∫⁻ y : ℝ, ‖F y‖ₑ ^ 2 * ENNReal.ofReal
          ((b (y + s) - b y) ^ 2 + (b (y - s) - b y) ^ 2) ∂volume ∂nu := by
        apply lintegral_congr_ae
        exact Eventually.of_forall fun s => cutoff_commutator_lintegral_eq_radial b hb F hF s
      _ = ∫⁻ y : ℝ, ∫⁻ s : ℝ, ‖F y‖ₑ ^ 2 * ENNReal.ofReal
          ((b (y + s) - b y) ^ 2 + (b (y - s) - b y) ^ 2) ∂nu ∂volume :=
        lintegral_lintegral_swap hR.aemeasurable
      _ = _ := by
        apply lintegral_congr_ae
        exact Eventually.of_forall fun y => by
          unfold radialMaskEnergy
          exact lintegral_const_mul' _ _ (by finiteness)
  calc
    _ = ∫⁻ p : ℝ × ℝ, G p ∂nu.prod volume :=
      (lintegral_prod G hG.aemeasurable).symm
    _ ≤ ∫⁻ p : ℝ × ℝ, cutoffFirstDensity b F p + J p ∂nu.prod volume :=
      lintegral_mono hpoint
    _ = cutoffFirstEnergy nu b F + ∫⁻ p : ℝ × ℝ, J p ∂nu.prod volume :=
      lintegral_add_left (cutoffFirstDensity_measurable b hb F hF) _
    _ = _ := by rw [hJradial]

end ActualGammaCompactCoreDraft20261018

/-
D-ONLY SOURCE-LOCAL APPLICATION CANDIDATE, NOT COMPILED.

Append after BOTH
  ActualGammaCutoffCommutator.actual-mask.v2.candidate-20261018.lean
  the corrected root exterior-budget fragment (v2 or later)
in the same source-local actual Gamma owner assembly. Reuse existing private
names; do not import a compiled owner in addition to its source body.

This is an application/binding, not a new canonical theorem or module.
It binds the positive-shift exit potential exactly to the actual real-valued
Gamma tail potential, including the Ici/Ioi endpoint conversion. It then
applies the positive-shift exterior budget to the weighted DCT majorant.

API basis: the v4.33.0 / mathlib db584cd6d46c92f209a44c0f1c829460d327499d
source cache used by the accepted owner. No claim of v4.35 compilation.
The existing root imports (Prod, Lebesgue.Map, WithDensity) suffice in
addition to those of the cutoff candidate. No compiler is invoked here.
-/

noncomputable section

open MeasureTheory Set
open scoped Classical ENNReal

namespace ActualGammaCompactCoreDraft20261018

open ActualGammaCornerTransportDraft20261017

private abbrev actualGammaExitMeasure : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun s => ENNReal.ofReal (actualDensity s))

private theorem actual_gamma_tail_lintegral_eq_ofReal {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ r in Ioi δ, ENNReal.ofReal (actualDensity r)) =
      ENNReal.ofReal (∫ r in Ioi δ, actualDensity r) := by
  have hρ := actualDensity_tail_integrable_for_cutoff hδ
  have hnn : ∀ᵐ r ∂volume.restrict (Ioi δ), 0 ≤ actualDensity r := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact (actual_density_pos (hδ.trans hr)).le
  exact (ofReal_integral_eq_lintegral_ofReal hρ hnn).symm

private theorem actual_gamma_exteriorPotential_eq_ofReal {a y : ℝ}
    (hy : y ∈ Ioo (-a) a) :
    exteriorPotential actualGammaExitMeasure (Ioo (-a) a) y =
      ENNReal.ofReal (actualExteriorPotential a y) := by
  have hleft : 0 < a + y := by linarith [hy.1]
  have hright : 0 < a - y := sub_pos.mpr hy.2
  have hρ : Measurable (fun r => ENNReal.ofReal (actualDensity r)) :=
    actual_density_measurable.ennreal_ofReal
  have hpair : Measurable (exteriorExitPair (Ioo (-a) a) y) := by
    unfold exteriorExitPair
    have h0 : Measurable (fun _ : ℝ => (0 : ℝ≥0∞)) := measurable_const
    have h1 : Measurable (fun _ : ℝ => (1 : ℝ≥0∞)) := measurable_const
    exact (Measurable.ite (measurableSet_Ioo.preimage (measurable_const.sub measurable_id))
      h0 h1).add
      (Measurable.ite (measurableSet_Ioo.preimage (measurable_const.add measurable_id))
        h0 h1)
  have hpoint : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      ENNReal.ofReal (actualDensity r) * exteriorExitPair (Ioo (-a) a) y r =
        (Ici (a + y)).indicator (fun r => ENNReal.ofReal (actualDensity r)) r +
          (Ici (a - y)).indicator (fun r => ENNReal.ofReal (actualDensity r)) r := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    change (0 : ℝ) < r at hr
    have hm : y - r ∈ Ioo (-a) a ↔ r < a + y := by
      constructor
      · intro h
        linarith [h.1]
      · intro h
        constructor <;> linarith [hy.2]
    have hp : y + r ∈ Ioo (-a) a ↔ r < a - y := by
      constructor
      · intro h
        linarith [h.2]
      · intro h
        constructor <;> linarith [hy.1]
    simp only [exteriorExitPair, hm, hp, Set.indicator, mem_Ici, ← not_lt]
    by_cases hm' : r < a + y <;> by_cases hp' : r < a - y <;>
      simp [hm', hp', mul_add]
  have hleft_subset : Ici (a + y) ⊆ Ioi (0 : ℝ) :=
    fun r hr => hleft.trans_le hr
  have hright_subset : Ici (a - y) ⊆ Ioi (0 : ℝ) :=
    fun r hr => hright.trans_le hr
  calc
    exteriorPotential actualGammaExitMeasure (Ioo (-a) a) y =
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (actualDensity r) *
          exteriorExitPair (Ioo (-a) a) y r := by
      unfold exteriorPotential actualGammaExitMeasure
      exact lintegral_withDensity_eq_lintegral_mul _ hρ hpair
    _ = ∫⁻ r in Ioi (0 : ℝ),
        (Ici (a + y)).indicator (fun r => ENNReal.ofReal (actualDensity r)) r +
          (Ici (a - y)).indicator (fun r => ENNReal.ofReal (actualDensity r)) r :=
      lintegral_congr_ae hpoint
    _ = (∫⁻ r in Ici (a + y), ENNReal.ofReal (actualDensity r)) +
        ∫⁻ r in Ici (a - y), ENNReal.ofReal (actualDensity r) := by
      rw [lintegral_add_left (hρ.indicator measurableSet_Ici),
        lintegral_indicator measurableSet_Ici, lintegral_indicator measurableSet_Ici,
        Measure.restrict_restrict_of_subset hleft_subset,
        Measure.restrict_restrict_of_subset hright_subset]
    _ = (∫⁻ r in Ioi (a + y), ENNReal.ofReal (actualDensity r)) +
        ∫⁻ r in Ioi (a - y), ENNReal.ofReal (actualDensity r) := by
      rw [← restrict_Ioi_eq_restrict_Ici (μ := (volume : Measure ℝ)) (a := a + y),
        ← restrict_Ioi_eq_restrict_Ici (μ := (volume : Measure ℝ)) (a := a - y)]
    _ = ENNReal.ofReal (∫ r in Ioi (a + y), actualDensity r) +
        ENNReal.ofReal (∫ r in Ioi (a - y), actualDensity r) := by
      rw [actual_gamma_tail_lintegral_eq_ofReal hleft,
        actual_gamma_tail_lintegral_eq_ofReal hright]
    _ = ENNReal.ofReal (actualExteriorPotential a y) := by
      rw [actualExteriorPotential,
        ENNReal.ofReal_add (actualDensity_tail_nonneg hright) (actualDensity_tail_nonneg hleft)]
      exact add_comm _ _

private theorem actual_gamma_exterior_budget (a : ℝ) (F : ℝ → ℂ)
    (hF : Measurable F) (hzero : ∀ x ∉ Ioo (-a) a, F x = 0) :
    (∫⁻ y in Ioo (-a) a, ‖F y‖ₑ ^ 2 * ENNReal.ofReal (actualExteriorPotential a y)) ≤
      directionalEnergy actualGammaExitMeasure F := by
  calc
    _ = ∫⁻ y in Ioo (-a) a,
        ‖F y‖ₑ ^ 2 * exteriorPotential actualGammaExitMeasure (Ioo (-a) a) y := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with y hy
      rw [actual_gamma_exteriorPotential_eq_ofReal hy]
    _ ≤ ∫⁻ y : ℝ,
        ‖F y‖ₑ ^ 2 * exteriorPotential actualGammaExitMeasure (Ioo (-a) a) y :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ ≤ directionalEnergy actualGammaExitMeasure F :=
      exterior_mass_le_directionalEnergy actualGammaExitMeasure (Ioo (-a) a)
        measurableSet_Ioo F hF hzero

private theorem actual_gamma_exteriorPotential_measurable (a : ℝ) :
    Measurable (exteriorPotential actualGammaExitMeasure (Ioo (-a) a)) := by
  have hpair : Measurable (fun p : ℝ × ℝ => exteriorExitPair (Ioo (-a) a) p.1 p.2) := by
    unfold exteriorExitPair
    have h0 : Measurable (fun _ : ℝ × ℝ => (0 : ℝ≥0∞)) := measurable_const
    have h1 : Measurable (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) := measurable_const
    exact (Measurable.ite (measurableSet_Ioo.preimage (measurable_fst.sub measurable_snd))
      h0 h1).add
      (Measurable.ite (measurableSet_Ioo.preimage (measurable_fst.add measurable_snd))
        h0 h1)
  exact hpair.lintegral_prod_right'

/- The actual exterior budget supplies this DCT majorant directly. The
   measurability proof uses the ENNReal potential before converting finite
   tails to real numbers; it does not assume V to be measurable. -/
private theorem actual_gamma_exterior_weight_integrable (a : ℝ) (F : ℝ → ℂ)
    (hF : Measurable F) (hF₂ : MemLp F 2)
    (hzero : ∀ x ∉ Ioo (-a) a, F x = 0)
    (hEnergy : directionalEnergy actualGammaExitMeasure F < (⊤ : ℝ≥0∞)) :
    IntegrableOn (fun y => (1 + actualExteriorPotential a y) * ‖F y‖ ^ 2)
      (Ioo (-a) a) := by
  let W : ℝ → ℝ≥0∞ := fun y =>
    ‖F y‖ₑ ^ 2 * exteriorPotential actualGammaExitMeasure (Ioo (-a) a) y
  have hWm : Measurable W :=
    (hF.enorm.pow_const 2).mul (actual_gamma_exteriorPotential_measurable a)
  have hbudget := actual_gamma_exterior_budget a F hF hzero
  have hWfinite : (∫⁻ y in Ioo (-a) a, W y) < (⊤ : ℝ≥0∞) := by
    have heq : (∫⁻ y in Ioo (-a) a, W y) =
        ∫⁻ y in Ioo (-a) a, ‖F y‖ₑ ^ 2 * ENNReal.ofReal (actualExteriorPotential a y) := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with y hy
      dsimp only [W]
      rw [actual_gamma_exteriorPotential_eq_ofReal hy]
    rw [heq]
    exact hbudget.trans_lt hEnergy
  have hWi : IntegrableOn (fun y => (W y).toReal) (Ioo (-a) a) :=
    integrable_toReal_of_lintegral_ne_top hWm.aemeasurable.restrict hWfinite.ne
  have hprod : IntegrableOn (fun y => ‖F y‖ ^ 2 * actualExteriorPotential a y)
      (Ioo (-a) a) := by
    apply IntegrableOn.congr_fun hWi _ measurableSet_Ioo
    intro y hy
    have hleft : 0 < a + y := by linarith [hy.1]
    have hright : 0 < a - y := sub_pos.mpr hy.2
    have hV : 0 ≤ actualExteriorPotential a y :=
      add_nonneg (actualDensity_tail_nonneg hright) (actualDensity_tail_nonneg hleft)
    dsimp only [W]
    rw [actual_gamma_exteriorPotential_eq_ofReal hy]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm,
      ENNReal.toReal_ofReal hV]
  have hmass : Integrable (fun y => ‖F y‖ ^ 2) :=
    hF₂.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  apply IntegrableOn.congr_fun (hmass.integrableOn.add hprod) _ measurableSet_Ioo
  intro y _hy
  simp only [Pi.add_apply]
  ring

end ActualGammaCompactCoreDraft20261018

/-
D-ONLY SOURCE-LOCAL ACTUAL RADIAL COMMUTATOR / OUTER DCT CANDIDATE.
NOT COMPILED. No Lean/kernel or latest-dev acceptance is claimed.

Append after the existing actual owner body and all of:
  ActualGammaCutoffCommutator.actual-mask.v2.candidate-20261018.lean
  ActualGammaCoreExteriorBudget.root-v2.uncompiled.fragment.lean
  ActualGammaCoreOuterDCT.root-v1.uncompiled.fragment.lean
  ActualGammaExteriorTailBinding.actual-consumer.v2.candidate-20261018.lean
  ActualGammaCorePositiveScaleCutoff.signed-v1.uncompiled.fragment.lean
Order the latter fragments so each definition precedes its consumers.
This is same-source append content, not a second imported owner/module.

The final theorem proves J_epsilon -> 0 for the actual positive Gamma
measure and actual mask. Its inputs are a measurable complex F, L2 finite
mass, zero support outside Ioo(-a,a), and finite directionalEnergy.
No real-potential measurability or trace/smoothness premise is added.
This closes the radial commutator's outer-DCT step, not the full compact
core, quotient representative transport, or RH.

Mathlib API inspection used the compatible v4.33/db584 source cache only.
No compiler, worktree mutation, or resource-gate bypass was used.
-/

noncomputable section

namespace ActualGammaCompactCoreDraft20261018

open MeasureTheory Set Filter
open ActualGammaCornerTransportDraft20261017
open scoped ENNReal Topology

/-- The actual scale measure folds the actual rho into the real radial gap.
This conversion requires exactly the already-proved radial integrability. -/
private theorem actual_gamma_radialMaskEnergy_eq_ofReal
    (b : ℝ → ℝ) (hb : Measurable b) (y : ℝ)
    (hi : IntegrableOn (cutoffRadialGap b y) (Ioi (0 : ℝ))) :
    radialMaskEnergy actualGammaExitMeasure b y =
      ENNReal.ofReal (∫ r in Ioi (0 : ℝ), cutoffRadialGap b y r) := by
  have hρ : Measurable (fun r => ENNReal.ofReal (actualDensity r)) :=
    actual_density_measurable.ennreal_ofReal
  have hpair : Measurable (fun r : ℝ => ENNReal.ofReal
      ((b (y + r) - b y) ^ 2 + (b (y - r) - b y) ^ 2)) := by
    fun_prop
  have hnn : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ cutoffRadialGap b y r := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact cutoffRadialGap_nonneg b y hr
  calc
    radialMaskEnergy actualGammaExitMeasure b y =
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (actualDensity r) *
          ENNReal.ofReal ((b (y + r) - b y) ^ 2 + (b (y - r) - b y) ^ 2) := by
      unfold radialMaskEnergy actualGammaExitMeasure
      exact lintegral_withDensity_eq_lintegral_mul _ hρ hpair
    _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (cutoffRadialGap b y r) := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      rw [cutoffRadialGap, ENNReal.ofReal_mul (actual_density_pos hr).le]
    _ = ENNReal.ofReal (∫ r in Ioi (0 : ℝ), cutoffRadialGap b y r) :=
      (ofReal_integral_eq_lintegral_ofReal hi hnn).symm

/-- Bind both parts of the actual real cutoff estimate to the ENNReal
radialMaskEnergy used by the positive-scale product-gap consumer. -/
private theorem actual_gamma_radialMaskEnergy_bound_and_tendsto :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a y : ℝ, y ∈ Ioo (-a) a →
      (∀ ε : ℝ, 0 < ε →
        radialMaskEnergy actualGammaExitMeasure (actualCutoffMask a ε) y ≤
          ENNReal.ofReal C +
            2 * exteriorPotential actualGammaExitMeasure (Ioo (-a) a) y) ∧
      Tendsto (fun ε =>
        radialMaskEnergy actualGammaExitMeasure (actualCutoffMask a ε) y)
        (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0) := by
  obtain ⟨C, hC, _hsmooth, hcut⟩ := actual_smooth_cutoff_commutator_candidate
  refine ⟨C, hC, ?_⟩
  intro a y hy
  have hleft : 0 < a + y := by linarith [hy.1]
  have hright : 0 < a - y := sub_pos.mpr hy.2
  have hV : 0 ≤ actualExteriorPotential a y := by
    unfold actualExteriorPotential
    exact add_nonneg (actualDensity_tail_nonneg hright)
      (actualDensity_tail_nonneg hleft)
  have hradial := (hcut a y hy).1
  refine ⟨?_, ?_⟩
  · intro ε hε
    have hi := (hradial.1 ε hε).1
    calc
      radialMaskEnergy actualGammaExitMeasure (actualCutoffMask a ε) y =
          ENNReal.ofReal (∫ r in Ioi (0 : ℝ),
            cutoffRadialGap (actualCutoffMask a ε) y r) :=
        actual_gamma_radialMaskEnergy_eq_ofReal _ (actualCutoffMask_measurable a ε) y hi
      _ ≤ ENNReal.ofReal (C + 2 * actualExteriorPotential a y) :=
        ENNReal.ofReal_le_ofReal (hradial.1 ε hε).2
      _ = ENNReal.ofReal C + (2 : ℝ≥0∞) *
          exteriorPotential actualGammaExitMeasure (Ioo (-a) a) y := by
        rw [ENNReal.ofReal_add hC (mul_nonneg (by norm_num) hV),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          actual_gamma_exteriorPotential_eq_ofReal hy]
        norm_num
  · have hoff : Tendsto (fun ε => ENNReal.ofReal
        (∫ r in Ioi (0 : ℝ), cutoffRadialGap (actualCutoffMask a ε) y r))
        (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) := by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using
        (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hradial.2
    apply hoff.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (actual_gamma_radialMaskEnergy_eq_ofReal _
      (actualCutoffMask_measurable a ε) y (hradial.1 ε hε).1).symm

/-- The actual radial commutator's outer integral tends to zero.
The finite majorant is supplied by L2 mass plus the exterior energy budget,
and the fixed-y limit comes from the actual smooth mask theorem. -/
private theorem actual_gamma_cutoff_radial_outer_tendsto_zero
    (a : ℝ) (F : ℝ → ℂ) (hF : Measurable F) (hF₂ : MemLp F 2)
    (hzero : ∀ x ∉ Ioo (-a) a, F x = 0)
    (henergy : directionalEnergy actualGammaExitMeasure F < (⊤ : ℝ≥0∞)) :
    Tendsto (fun ε => ∫⁻ y : ℝ, ‖F y‖ₑ ^ 2 *
      radialMaskEnergy actualGammaExitMeasure (actualCutoffMask a ε) y)
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0) := by
  obtain ⟨C, _hC, hcut⟩ := actual_gamma_radialMaskEnergy_bound_and_tendsto
  let G : ℝ → ℝ → ℝ≥0∞ := fun ε y => ‖F y‖ₑ ^ 2 *
    radialMaskEnergy actualGammaExitMeasure (actualCutoffMask a ε) y
  let D : ℝ → ℝ≥0∞ := fun y =>
    ENNReal.ofReal C * ‖F y‖ₑ ^ 2 +
      2 * (‖F y‖ₑ ^ 2 * exteriorPotential actualGammaExitMeasure (Ioo (-a) a) y)
  have hmassR : Integrable (fun y => ‖F y‖ ^ 2) :=
    hF₂.integrable_norm_pow (p := 2) (by norm_num)
  have hmass_eq : (∫⁻ y : ℝ, ‖F y‖ₑ ^ 2) =
      ENNReal.ofReal (∫ y : ℝ, ‖F y‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hmassR
      (Eventually.of_forall fun y => sq_nonneg ‖F y‖)]
    apply lintegral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only
      rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
  have hmass : (∫⁻ y : ℝ, ‖F y‖ₑ ^ 2) < (⊤ : ℝ≥0∞) := by
    rw [hmass_eq]
    exact ENNReal.ofReal_lt_top
  have hfinite : (∫⁻ y : ℝ, D y) ≠ (⊤ : ℝ≥0∞) :=
    (cutoff_outer_majorant_finite actualGammaExitMeasure (Ioo (-a) a)
      measurableSet_Ioo F hF hzero hmass henergy C).ne
  have hmeas : ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0, Measurable (G ε) :=
    Eventually.of_forall fun ε =>
      (hF.enorm.pow_const 2).mul
        (radialMaskEnergy_measurable actualGammaExitMeasure _
          (actualCutoffMask_measurable a ε))
  have hdom : ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0,
      ∀ᵐ y ∂volume, G ε y ≤ D y := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Eventually.of_forall fun y => by
      by_cases hy : y ∈ Ioo (-a) a
      · calc
          G ε y ≤ ‖F y‖ₑ ^ 2 * (ENNReal.ofReal C +
              2 * exteriorPotential actualGammaExitMeasure (Ioo (-a) a) y) :=
            mul_le_mul' le_rfl ((hcut a y hy).1 ε hε)
          _ = D y := by
            dsimp only [D]
            rw [mul_add]
            ac_rfl
      · simp [G, D, hzero y hy]
  have hlim : ∀ᵐ y ∂volume,
      Tendsto (fun ε => G ε y) (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) := by
    exact Eventually.of_forall fun y => by
      by_cases hy : y ∈ Ioo (-a) a
      · simpa only [G, mul_zero] using
          (ENNReal.Tendsto.const_mul (a := ‖F y‖ₑ ^ 2) (hcut a y hy).2
            (Or.inr (by finiteness : ‖F y‖ₑ ^ 2 ≠ (⊤ : ℝ≥0∞))))
      · simpa [G, hzero y hy] using
          (tendsto_const_nhds : Tendsto (fun _ε : ℝ => (0 : ℝ≥0∞))
            (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0))
  simpa only [G, lintegral_zero] using
    tendsto_lintegral_filter_of_dominated_convergence
      (μ := (volume : Measure ℝ)) (f := fun _ => (0 : ℝ≥0∞))
      D hmeas hdom hfinite hlim

end ActualGammaCompactCoreDraft20261018

/-
UNCOMPILED ACTUAL GAMMA CUTOFF ERROR-ENERGY ENDPOINT.
Append after the two outer-DCT fragments and the positive-scale estimate.
It supplies the boundary-cutoff step of the core proof; mollification,
smooth compact approximation and quotient transport remain separate steps.
-/
namespace ActualGammaCompactCoreDraft20261018

open MeasureTheory Set Filter
open ActualGammaCornerTransportDraft20261017
open scoped ENNReal Topology

private theorem actual_gamma_cutoff_error_energy_tendsto_zero
    (a : ℝ) (F : ℝ → ℂ) (hF : Measurable F) (hF₂ : MemLp F 2)
    (hzero : ∀ x ∉ Ioo (-a) a, F x = 0)
    (henergy : directionalEnergy actualGammaExitMeasure F < (⊤ : ℝ≥0∞)) :
    Tendsto (fun ε => directionalEnergy actualGammaExitMeasure
      (fun x => (actualCutoffMask a ε x : ℂ) * F x))
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) := by
  have hfirst := cutoffFirstEnergy_tendsto_zero actualGammaExitMeasure F hF henergy
    (actualCutoffMask a) (actualCutoffMask_measurable a)
    (fun ε _hε x => actualCutoffMask_range a ε x)
    (actualCutoffMask_tendsto_zero a)
  have hsecond := actual_gamma_cutoff_radial_outer_tendsto_zero
    a F hF hF₂ hzero henergy
  have hsum : Tendsto (fun ε => cutoffFirstEnergy actualGammaExitMeasure
      (actualCutoffMask a ε) F + ∫⁻ y : ℝ, ‖F y‖ₑ ^ 2 *
        radialMaskEnergy actualGammaExitMeasure (actualCutoffMask a ε) y)
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [zero_add] using hfirst.add hsecond
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun ε => directionalEnergy_cutoff_le
      actualGammaExitMeasure (actualCutoffMask a ε)
      (actualCutoffMask_measurable a ε) F hF)

end ActualGammaCompactCoreDraft20261018

/-
UNCOMPILED SAME-SOURCE AE TRANSPORT FOR THE ACTUAL CORE CONSUMER.
These helpers preserve the entire positive-shift energy, including infinity,
and let the actual cutoff DCT apply to original L2 equivalence classes.
They are not new canonical bind-only declarations. Append after exterior-v2.
-/

namespace ActualGammaCompactCoreDraft20261018

open MeasureTheory Set Filter
open scoped ENNReal Classical

private theorem directionalEnergy_congr_ae (nu : Measure ℝ)
    {F G : ℝ → ℂ} (h : F =ᵐ[volume] G) :
    directionalEnergy nu F = directionalEnergy nu G := by
  unfold directionalEnergy
  apply lintegral_congr_ae
  exact Eventually.of_forall fun s => by
    have hs : (fun x : ℝ => F (x - s)) =ᵐ[volume]
        (fun x : ℝ => G (x - s)) :=
      (measurePreserving_sub_right (volume : Measure ℝ) s).quasiMeasurePreserving.ae_eq h
    apply lintegral_congr_ae
    filter_upwards [h, hs] with x hx hxs
    rw [hx, hxs]

private theorem exists_measurable_zero_supported_energy_representative
    (nu : Measure ℝ) (Omega : Set ℝ) (hOmega : MeasurableSet Omega)
    (F : ℝ → ℂ) (hF : AEMeasurable F)
    (hzero : ∀ᵐ x : ℝ, x ∉ Omega → F x = 0) :
    ∃ G : ℝ → ℂ, Measurable G ∧ (∀ x ∉ Omega, G x = 0) ∧
      F =ᵐ[volume] G ∧
      (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2) = (∫⁻ x : ℝ, ‖G x‖ₑ ^ 2) ∧
      directionalEnergy nu F = directionalEnergy nu G := by
  let G : ℝ → ℂ := Omega.indicator (hF.mk F)
  have hG : Measurable G := hF.measurable_mk.indicator hOmega
  have hGzero : ∀ x ∉ Omega, G x = 0 := by
    intro x hx
    exact indicator_of_notMem hx _
  have hFG : F =ᵐ[volume] G := by
    filter_upwards [hF.ae_eq_mk, hzero] with x hx hz
    by_cases hmem : x ∈ Omega
    · simpa only [G, indicator_of_mem hmem] using hx
    · simp only [G, indicator_of_notMem hmem, hz hmem]
  refine ⟨G, hG, hGzero, hFG, ?_, directionalEnergy_congr_ae nu hFG⟩
  apply lintegral_congr_ae
  filter_upwards [hFG] with x hx
  rw [hx]

end ActualGammaCompactCoreDraft20261018

/-
D-ONLY SOURCE-LOCAL CANDIDATE, NOT COMPILED, 2026-10-18.

Append after ActualGammaCutoffCommutator.actual-mask.v2.candidate-20261018.lean
in the same exact actual-Gamma owner source assembly. Hoist, if not already
present, these imports to the owner's import block:
  import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
  import Mathlib.Topology.Algebra.Support

Reuses source-private actualCutoffEta/Mask, their range/measurability lemmas,
actualCutoffEta_contDiff, and actualCutoffMask_eventually_zero. Do not import
mangled private names from another compiled owner.

Eta is smooth and compactly supported in the interior. For measurable F of
finite L2 mass, the squared L2 mass of mask * F tends to zero. The product
eta * F has compact support, but no continuity or smoothness of that product
is asserted. Mollification remains a separate step.

API basis: the v4.33 source cache. Neither v4.33 nor v4.35 compilation or
kernel acceptance is claimed for this fragment.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Classical ENNReal Topology ContDiff

namespace ActualGammaCornerTransportDraft20261017

private theorem actualCutoffEta_eq_zero_of_le_left {a ε x : ℝ} (hε : 0 < ε)
    (hx : x ≤ -a + ε) : actualCutoffEta a ε x = 0 := by
  have hq : (x + a) / ε ≤ 1 := (div_le_iff₀ hε).2 (by linarith)
  have harg : (x + a) / ε - 1 ≤ 0 := by linarith
  simp only [actualCutoffEta, Real.smoothTransition.zero_of_nonpos harg, zero_mul]

private theorem actualCutoffEta_eq_zero_of_right_le {a ε x : ℝ} (hε : 0 < ε)
    (hx : a - ε ≤ x) : actualCutoffEta a ε x = 0 := by
  have hq : (a - x) / ε ≤ 1 := (div_le_iff₀ hε).2 (by linarith)
  have harg : (a - x) / ε - 1 ≤ 0 := by linarith
  simp only [actualCutoffEta, Real.smoothTransition.zero_of_nonpos harg, mul_zero]

private theorem actualCutoffEta_support_subset_Ioo {a ε : ℝ} (hε : 0 < ε) :
    Function.support (actualCutoffEta a ε) ⊆ Ioo (-a + ε) (a - ε) := by
  intro x hx
  change actualCutoffEta a ε x ≠ 0 at hx
  constructor
  · by_contra h
    exact hx (actualCutoffEta_eq_zero_of_le_left hε (not_lt.mp h))
  · by_contra h
    exact hx (actualCutoffEta_eq_zero_of_right_le hε (not_lt.mp h))

private theorem actualCutoffEta_tsupport_subset_Icc {a ε : ℝ} (hε : 0 < ε) :
    tsupport (actualCutoffEta a ε) ⊆ Icc (-a + ε) (a - ε) := by
  change closure (Function.support (actualCutoffEta a ε)) ⊆ _
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hx' := actualCutoffEta_support_subset_Ioo hε hx
  exact ⟨hx'.1.le, hx'.2.le⟩

private theorem actualCutoffEta_hasCompactSupport {a ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (actualCutoffEta a ε) := by
  change IsCompact (tsupport (actualCutoffEta a ε))
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (actualCutoffEta_tsupport_subset_Icc hε)

private theorem actualCutoffEta_tsupport_subset_interior {a ε : ℝ} (hε : 0 < ε) :
    tsupport (actualCutoffEta a ε) ⊆ Ioo (-a) a := by
  intro x hx
  have hx' := actualCutoffEta_tsupport_subset_Icc hε hx
  constructor <;> linarith [hx'.1, hx'.2]

/- These conclusions need only epsilon > 0, hence apply in particular when
   a > 0 and epsilon < a/2. Smallness additionally ensures eta(0) = 1. -/
private theorem actualCutoffEta_smooth_compact_interior {a ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (actualCutoffEta a ε) ∧
      HasCompactSupport (actualCutoffEta a ε) ∧
      tsupport (actualCutoffEta a ε) ⊆ Icc (-a + ε) (a - ε) ∧
      tsupport (actualCutoffEta a ε) ⊆ Ioo (-a) a :=
  ⟨actualCutoffEta_contDiff a ε, actualCutoffEta_hasCompactSupport hε,
    actualCutoffEta_tsupport_subset_Icc hε, actualCutoffEta_tsupport_subset_interior hε⟩

private theorem actualCutoffEta_at_zero_eq_one {a ε : ℝ} (hε : 0 < ε)
    (hsmall : ε < a / 2) : actualCutoffEta a ε 0 = 1 := by
  have hq : 2 ≤ a / ε := (le_div_iff₀ hε).2 (by linarith)
  have harg : 1 ≤ a / ε - 1 := by linarith
  simp only [actualCutoffEta, zero_add, sub_zero,
    Real.smoothTransition.one_of_one_le harg, one_mul]

/- This is ordinary support, not topological support: the mask need not have
   topological support strictly inside the interval. -/
private theorem actualCutoffMask_support_subset (a ε : ℝ) :
    Function.support (actualCutoffMask a ε) ⊆ Ioo (-a) a := by
  intro x hx
  change actualCutoffMask a ε x ≠ 0 at hx
  by_contra hout
  exact hx (by simp only [actualCutoffMask, if_neg hout])

private theorem actualCutoffEta_mul_eq_sub_mask (a ε : ℝ) (F : ℝ → ℂ)
    (hzero : ∀ x ∉ Ioo (-a) a, F x = 0) (x : ℝ) :
    (actualCutoffEta a ε x : ℂ) * F x =
      F x - (actualCutoffMask a ε x : ℂ) * F x := by
  by_cases hx : x ∈ Ioo (-a) a
  · simp only [actualCutoffMask, if_pos hx]
    push_cast
    ring
  · simp only [actualCutoffMask, if_neg hx, hzero x hx,
      mul_zero, Complex.ofReal_zero, zero_mul, sub_self]

private theorem actualCutoffEta_mul_tsupport_subset_Icc {a ε : ℝ} (hε : 0 < ε)
    (F : ℝ → ℂ) :
    tsupport (fun x => (actualCutoffEta a ε x : ℂ) * F x) ⊆
      Icc (-a + ε) (a - ε) := by
  change closure (Function.support (fun x => (actualCutoffEta a ε x : ℂ) * F x)) ⊆ _
  apply closure_minimal _ isClosed_Icc
  intro x hx
  change (actualCutoffEta a ε x : ℂ) * F x ≠ 0 at hx
  have hη : actualCutoffEta a ε x ≠ 0 := by
    intro h
    exact hx (by rw [h, Complex.ofReal_zero, zero_mul])
  have hx' := actualCutoffEta_support_subset_Ioo hε hη
  exact ⟨hx'.1.le, hx'.2.le⟩

private theorem actualCutoffEta_mul_hasCompactSupport {a ε : ℝ} (hε : 0 < ε)
    (F : ℝ → ℂ) :
    HasCompactSupport (fun x => (actualCutoffEta a ε x : ℂ) * F x) := by
  change IsCompact (tsupport (fun x => (actualCutoffEta a ε x : ℂ) * F x))
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (actualCutoffEta_mul_tsupport_subset_Icc hε F)

private theorem actualCutoffMask_mul_enorm_sq_le (a ε : ℝ) (F : ℝ → ℂ) (x : ℝ) :
    ‖(actualCutoffMask a ε x : ℂ) * F x‖ₑ ^ 2 ≤ ‖F x‖ₑ ^ 2 := by
  have hb := actualCutoffMask_range a ε x
  have hnorm : ‖(actualCutoffMask a ε x : ℂ) * F x‖ ≤ ‖F x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hb.2 (norm_nonneg (F x))
  exact pow_le_pow_left' (enorm_le_iff_norm_le.mpr hnorm) 2

private theorem actualCutoffMask_mul_mass_le (a ε : ℝ) (F : ℝ → ℂ) :
    (∫⁻ x : ℝ, ‖(actualCutoffMask a ε x : ℂ) * F x‖ₑ ^ 2) ≤
      ∫⁻ x : ℝ, ‖F x‖ₑ ^ 2 :=
  lintegral_mono (actualCutoffMask_mul_enorm_sq_le a ε F)

private theorem actualCutoffMask_mul_mass_tendsto_zero (a : ℝ) (F : ℝ → ℂ)
    (hF : Measurable F)
    (hmass : (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2) < (⊤ : ℝ≥0∞)) :
    Tendsto (fun ε => ∫⁻ x : ℝ, ‖(actualCutoffMask a ε x : ℂ) * F x‖ₑ ^ 2)
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0) := by
  have hmeas : ∀ ε : ℝ,
      Measurable (fun x => ‖(actualCutoffMask a ε x : ℂ) * F x‖ₑ ^ 2) := by
    intro ε
    have hb : Measurable (fun x => (actualCutoffMask a ε x : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (actualCutoffMask_measurable a ε)
    exact (hb.mul hF).enorm.pow_const 2
  have hpoint : ∀ x : ℝ,
      Tendsto (fun ε => ‖(actualCutoffMask a ε x : ℂ) * F x‖ₑ ^ 2)
        (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) := by
    intro x
    apply tendsto_const_nhds.congr'
    change ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0,
      (0 : ℝ≥0∞) = ‖(actualCutoffMask a ε x : ℂ) * F x‖ₑ ^ 2
    filter_upwards [actualCutoffMask_eventually_zero a x] with ε hε
    simp only [hε, Complex.ofReal_zero, zero_mul, enorm_zero, zero_pow (by norm_num : 2 ≠ 0)]
  have hdct := tendsto_lintegral_filter_of_dominated_convergence
    (μ := (volume : Measure ℝ)) (l := 𝓝[Ioi (0 : ℝ)] 0)
    (f := fun _ : ℝ => (0 : ℝ≥0∞))
    (fun x : ℝ => ‖F x‖ₑ ^ 2)
    (Eventually.of_forall hmeas)
    (Eventually.of_forall fun ε =>
      Eventually.of_forall (actualCutoffMask_mul_enorm_sq_le a ε F))
    hmass.ne (Eventually.of_forall hpoint)
  simpa only [lintegral_zero] using hdct

private theorem actualCutoffMask_mul_mass_tendsto_zero_of_memLp (a : ℝ) (F : ℝ → ℂ)
    (hF : Measurable F) (hF₂ : MemLp F 2) :
    Tendsto (fun ε => ∫⁻ x : ℝ, ‖(actualCutoffMask a ε x : ℂ) * F x‖ₑ ^ 2)
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0) := by
  apply actualCutoffMask_mul_mass_tendsto_zero a F hF
  have hm := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hF₂
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using hm

private theorem actualCutoffEta_mul_sub_mass_tendsto_zero (a : ℝ) (F : ℝ → ℂ)
    (hF : Measurable F)
    (hmass : (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2) < (⊤ : ℝ≥0∞))
    (hzero : ∀ x ∉ Ioo (-a) a, F x = 0) :
    Tendsto (fun ε =>
        ∫⁻ x : ℝ, ‖(actualCutoffEta a ε x : ℂ) * F x - F x‖ₑ ^ 2)
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0) := by
  apply (actualCutoffMask_mul_mass_tendsto_zero a F hF hmass).congr'
  exact Eventually.of_forall fun ε => by
    apply lintegral_congr_ae
    exact Eventually.of_forall fun x => by
      have hid : (actualCutoffEta a ε x : ℂ) * F x - F x =
          -((actualCutoffMask a ε x : ℂ) * F x) := by
        rw [actualCutoffEta_mul_eq_sub_mask a ε F hzero x]
        abel
      dsimp only
      rw [hid, enorm_neg]

end ActualGammaCornerTransportDraft20261017

/-
UNCOMPILED ACTUAL INTERIOR CUTOFF FORM APPROXIMATION.
The approximants below have compact support in the open interval but retain
only the original function regularity. This does not claim a smooth core;
smoothing these approximants remains a genuine mathematical obligation.
Append after mass/support, cutoff-error energy and AE helper fragments.
-/
namespace ActualGammaCompactCoreDraft20261018

open MeasureTheory Set Filter
open ActualGammaCornerTransportDraft20261017
open scoped ENNReal Topology

private theorem directionalEnergy_neg (nu : Measure ℝ) (F : ℝ → ℂ) :
    directionalEnergy nu (fun x => -F x) = directionalEnergy nu F := by
  unfold directionalEnergy
  apply lintegral_congr_ae
  exact Eventually.of_forall fun s => by
    apply lintegral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [show -F x - -F (x - s) = -(F x - F (x - s)) by abel, enorm_neg]

private theorem actual_gamma_interior_cutoff_form_approximation
    (a : ℝ) (F : ℝ → ℂ) (hF : Measurable F) (hF₂ : MemLp F 2)
    (hzero : ∀ x ∉ Ioo (-a) a, F x = 0)
    (henergy : directionalEnergy actualGammaExitMeasure F < (⊤ : ℝ≥0∞)) :
    (∀ ε > 0, HasCompactSupport (fun x => (actualCutoffEta a ε x : ℂ) * F x) ∧
      tsupport (fun x => (actualCutoffEta a ε x : ℂ) * F x) ⊆ Ioo (-a) a) ∧
    Tendsto (fun ε =>
      (∫⁻ x : ℝ, ‖(actualCutoffEta a ε x : ℂ) * F x - F x‖ₑ ^ 2) +
        directionalEnergy actualGammaExitMeasure
          (fun x => (actualCutoffEta a ε x : ℂ) * F x - F x))
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) := by
  have hmass : (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2) < (⊤ : ℝ≥0∞) := by
    have hm := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hF₂
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using hm
  have hm := actualCutoffEta_mul_sub_mass_tendsto_zero a F hF hmass hzero
  have he := actual_gamma_cutoff_error_energy_tendsto_zero a F hF hF₂ hzero henergy
  have he' : Tendsto (fun ε => directionalEnergy actualGammaExitMeasure
      (fun x => (actualCutoffEta a ε x : ℂ) * F x - F x))
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) := by
    apply he.congr'
    exact Eventually.of_forall fun ε => by
      have hpoint : (fun x => (actualCutoffEta a ε x : ℂ) * F x - F x) =
          (fun x => -((actualCutoffMask a ε x : ℂ) * F x)) := by
        funext x
        rw [actualCutoffEta_mul_eq_sub_mask a ε F hzero x]
        abel
      dsimp only
      rw [hpoint, directionalEnergy_neg]
  refine ⟨?_, ?_⟩
  · intro ε hε
    refine ⟨actualCutoffEta_mul_hasCompactSupport hε F, ?_⟩
    intro x hx
    have hx' := actualCutoffEta_mul_tsupport_subset_Icc hε F hx
    constructor <;> linarith [hx'.1, hx'.2]
  · simpa only [zero_add] using hm.add he'

end ActualGammaCompactCoreDraft20261018

/-
D-ONLY ORIGINAL-Ioc CARRIER / AE REPRESENTATIVE CONSUMER.
NOT COMPILED. No Lean/kernel or latest-dev acceptance is claimed.

Append after the actual owner assembly, tail binding, root AE transport,
and root cutoff-error-energy consumer. The only interval-source definition
used is the existing source-private
  ActualGammaDomainPassageDraft.zeroExtension (2*a) (-a) u.
It is already present in the accepted 4398-line digamma unit and is exactly
the definition consumed by the accepted interval-raw endpoint. No raw
Fourier body, extra zero-extension definition, or duplicate owner is needed.

The Ioc(-a,a] to Ioo(-a,a) boundary change removes only the right singleton
{a}, which is null for volume. No endpoint value or trace is assumed.
The representative preserves original interval mass, full zero-extension
mass, and the actual Gamma directional energy literally, including top.
The final consumer transports the proved cutoff error-energy limit back
to the original Ioc zero extension. This is not the full compact core.

No compiler or WT/canonical-source mutation was used. Mathlib API inspection
used v4.33/db584cd6d46c92f209a44c0f1c829460d327499d only.
-/

noncomputable section

namespace ActualGammaCompactCoreDraft20261018

open MeasureTheory Set Filter
open ActualGammaCornerTransportDraft20261017
open scoped ENNReal Topology

/-- Only the included right endpoint prevents pointwise open-interval support;
volume.ae_ne removes it without any condition on u(a). -/
private theorem actual_ioc_zeroExtension_ae_zero_outside
    (a : ℝ) (u : ℝ → ℂ) :
    ∀ᵐ x : ℝ, x ∉ Ioo (-a) a →
      ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u x = 0 := by
  have hend : -a + 2 * a = a := by ring
  filter_upwards [(volume : Measure ℝ).ae_ne a] with x hxa
  intro hx
  have hnot : x ∉ Ioc (-a) a := by
    intro hxi
    exact hx ⟨hxi.1, lt_of_le_of_ne hxi.2 hxa⟩
  simp only [ActualGammaDomainPassageDraft.zeroExtension, hend,
    indicator_of_notMem hnot]

/-- The zero extension's full ENNReal mass is exactly the original Ioc mass.
No integrability or measurability premise is necessary for this identity. -/
private theorem actual_ioc_zeroExtension_mass_eq (a : ℝ) (u : ℝ → ℂ) :
    (∫⁻ x : ℝ,
      ‖ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u x‖ₑ ^ 2) =
        ∫⁻ x in Ioc (-a) a, ‖u x‖ₑ ^ 2 := by
  have hend : -a + 2 * a = a := by ring
  calc
    _ = ∫⁻ x : ℝ, (Ioc (-a) a).indicator (fun y => ‖u y‖ₑ ^ 2) x := by
      apply lintegral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : x ∈ Ioc (-a) a <;>
          simp [ActualGammaDomainPassageDraft.zeroExtension, hend, hx]
    _ = _ := lintegral_indicator measurableSet_Ioc _

/-- An actual original-carrier L2 vector has a measurable representative with
exact open-interval support, with both masses and actual Gamma energy intact.
No energy-finiteness hypothesis is used in this representative theorem. -/
private theorem actual_ioc_exists_measurable_zero_supported_energy_representative
    (a : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :
    ∃ G : ℝ → ℂ, Measurable G ∧ MemLp G 2 ∧
      (∀ x ∉ Ioo (-a) a, G x = 0) ∧
      ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u =ᵐ[volume] G ∧
      ((∫⁻ x : ℝ,
          ‖ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u x‖ₑ ^ 2) =
        ∫⁻ x : ℝ, ‖G x‖ₑ ^ 2) ∧
      ((∫⁻ x in Ioc (-a) a, ‖u x‖ₑ ^ 2) = ∫⁻ x : ℝ, ‖G x‖ₑ ^ 2) ∧
      directionalEnergy actualGammaExitMeasure
        (ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u) =
          directionalEnergy actualGammaExitMeasure G := by
  have hend : -a + 2 * a = a := by ring
  have hF₂ : MemLp
      (ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u) 2 := by
    simpa only [ActualGammaDomainPassageDraft.zeroExtension, hend] using
      (memLp_indicator_iff_restrict (μ := volume)
        measurableSet_Ioc.nullMeasurableSet).mpr hu
  obtain ⟨G, hG, hGzero, hFG, hmass, henergy⟩ :=
    exists_measurable_zero_supported_energy_representative
      actualGammaExitMeasure (Ioo (-a) a) measurableSet_Ioo
      (ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u)
      hF₂.aestronglyMeasurable.aemeasurable (actual_ioc_zeroExtension_ae_zero_outside a u)
  refine ⟨G, hG, (memLp_congr_ae hFG).mp hF₂, hGzero, hFG, hmass, ?_, henergy⟩
  exact (actual_ioc_zeroExtension_mass_eq a u).symm.trans hmass

/-- Apply the actual cutoff error-energy endpoint to the original Ioc L2
carrier, retaining its original zero extension in the conclusion. -/
private theorem actual_ioc_cutoff_error_energy_tendsto_zero
    (a : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a)))
    (henergy : directionalEnergy actualGammaExitMeasure
      (ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u) < (⊤ : ℝ≥0∞)) :
    Tendsto (fun ε => directionalEnergy actualGammaExitMeasure
      (fun x => (actualCutoffMask a ε x : ℂ) *
        ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u x))
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) := by
  obtain ⟨G, hG, hG₂, hGzero, hFG, _hmass, _hmassIoc, henergyEq⟩ :=
    actual_ioc_exists_measurable_zero_supported_energy_representative a u hu
  have hGenergy : directionalEnergy actualGammaExitMeasure G < (⊤ : ℝ≥0∞) := by
    rw [← henergyEq]
    exact henergy
  have hlim := actual_gamma_cutoff_error_energy_tendsto_zero a G hG hG₂ hGzero hGenergy
  apply hlim.congr'
  exact Eventually.of_forall fun ε => by
    have hcut :
        (fun x => (actualCutoffMask a ε x : ℂ) *
          ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u x) =ᵐ[volume]
            (fun x => (actualCutoffMask a ε x : ℂ) * G x) := by
      filter_upwards [hFG] with x hx
      rw [hx]
    exact (directionalEnergy_congr_ae actualGammaExitMeasure hcut).symm

end ActualGammaCompactCoreDraft20261018

/-
UNCOMPILED ORIGINAL Ioc L2 GAMMA-FORM CUTOFF CONSUMER.
It transports both components of interior cutoff approximation back to the
original Ioc zero extension, with no endpoint/trace or measurability addition.
The approximants are compactly supported inside the open interval;
they are not asserted smooth. Append after original-Ioc AE consumer.
-/
namespace ActualGammaCompactCoreDraft20261018

open MeasureTheory Set Filter
open ActualGammaCornerTransportDraft20261017
open scoped ENNReal Topology

private theorem actual_ioc_interior_cutoff_form_approximation
    (a : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a)))
    (henergy : directionalEnergy actualGammaExitMeasure
      (ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u) < (⊤ : ℝ≥0∞)) :
    let F := ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u
    (∀ ε > 0, HasCompactSupport (fun x => (actualCutoffEta a ε x : ℂ) * F x) ∧
      tsupport (fun x => (actualCutoffEta a ε x : ℂ) * F x) ⊆ Ioo (-a) a) ∧
    Tendsto (fun ε =>
      (∫⁻ x : ℝ, ‖(actualCutoffEta a ε x : ℂ) * F x - F x‖ₑ ^ 2) +
        directionalEnergy actualGammaExitMeasure
          (fun x => (actualCutoffEta a ε x : ℂ) * F x - F x))
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) := by
  dsimp only
  let F := ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u
  obtain ⟨G, hG, hG₂, hGzero, hFG, _hmass, _hmassIoc, henergyEq⟩ :=
    actual_ioc_exists_measurable_zero_supported_energy_representative a u hu
  have hGenergy : directionalEnergy actualGammaExitMeasure G < (⊤ : ℝ≥0∞) := by
    rw [← henergyEq]
    exact henergy
  have hlim := (actual_gamma_interior_cutoff_form_approximation
    a G hG hG₂ hGzero hGenergy).2
  refine ⟨?_, ?_⟩
  · intro ε hε
    refine ⟨actualCutoffEta_mul_hasCompactSupport hε F, ?_⟩
    intro x hx
    have hx' := actualCutoffEta_mul_tsupport_subset_Icc hε F hx
    constructor <;> linarith [hx'.1, hx'.2]
  · apply hlim.congr'
    exact Eventually.of_forall fun ε => by
      have herr : (fun x => (actualCutoffEta a ε x : ℂ) * F x - F x) =ᵐ[volume]
          (fun x => (actualCutoffEta a ε x : ℂ) * G x - G x) := by
        filter_upwards [hFG] with x hx
        dsimp only [F]
        rw [hx]
      have hm : (∫⁻ x : ℝ, ‖(actualCutoffEta a ε x : ℂ) * F x - F x‖ₑ ^ 2) =
          ∫⁻ x : ℝ, ‖(actualCutoffEta a ε x : ℂ) * G x - G x‖ₑ ^ 2 := by
        apply lintegral_congr_ae
        filter_upwards [herr] with x hx
        rw [hx]
      have he := directionalEnergy_congr_ae actualGammaExitMeasure herr
      dsimp only
      exact (congrArg₂ (fun x y : ℝ≥0∞ => x + y) hm he).symm

end ActualGammaCompactCoreDraft20261018

/- ASSEMBLY CONSTITUENT: accepted_raw_wholeline_tail -/


/-
SOURCE-LOCAL CANDIDATE, NOT COMPILED. No kernel acceptance is claimed.

Read-only preparation against Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
No canonical module, wrapper registration, worktree, or build was changed.

The intended consumer is the original Ioc zero extension, whose L1 and L2
properties are already available. None of the lemmas below assumes a smooth
core or finiteness of a full Gamma energy. The real test functions below
are used solely to identify two Fourier representatives almost everywhere.
-/


noncomputable section

open MeasureTheory Set
open scoped FourierTransform SchwartzMap NNReal ENNReal

namespace ActualGammaRawFourierBridgeDraft20261017

private theorem continuous_raw_fourier {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) := by
  exact VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar continuous_inner hf

/-- Fourier--Fubini needs only L1 of the original function and of the
Schwartz test; no L2 property of the raw Fourier integral is assumed. -/
private theorem raw_fourier_test {f : ℝ → ℂ} (hf : Integrable f)
    (ψ : SchwartzMap ℝ ℂ) :
    (∫ ξ : ℝ, ψ ξ • 𝓕 f ξ) = ∫ x : ℝ, 𝓕 ψ x • f x := by
  simpa [SchwartzMap.fourier_coe, Real.fourier_eq, VectorFourier.fourierIntegral,
    Real.inner_apply, smul_eq_mul, mul_comm] using!
    VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (f := f) (g := (ψ : ℝ → ℂ)) (.mul ℂ ℂ) (L := innerₗ ℝ)
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      Real.continuous_fourierChar continuous_inner hf (ψ.integrable (μ := volume))

/-- The ordinary L1 Fourier integral represents the L2 Fourier transform
for an original L1 ∩ L2 function. This is the missing compatibility bridge,
obtained from distribution compatibility and local integral uniqueness. -/
private theorem raw_fourier_ae_eq_L2 {f : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    (𝓕 f : ℝ → ℂ) =ᵐ[volume]
      (𝓕 (hf₂.toLp f) : Lp ℂ 2 volume) := by
  let F : Lp ℂ 2 volume := 𝓕 (hf₂.toLp f)
  apply ae_eq_of_integral_contDiff_smul_eq
    (continuous_raw_fourier hf₁).locallyIntegrable
    ((Lp.memLp F).locallyIntegrable (by norm_num))
  intro g hg hgc
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Complex.ofRealCLM ∘ g) :=
    Complex.ofRealCLM.contDiff.comp hg
  let ψ : SchwartzMap ℝ ℂ := hg₁.toSchwartzMap hg₂
  have hdist := congrArg (fun T : TemperedDistribution ℝ ℂ => T ψ)
    (Lp.fourier_toTemperedDistribution_eq (hf₂.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hdist
  calc
    (∫ ξ : ℝ, g ξ • 𝓕 f ξ) = ∫ ξ : ℝ, ψ ξ • 𝓕 f ξ := by
      simp [ψ, Function.comp_apply]
    _ = ∫ x : ℝ, 𝓕 ψ x • f x := raw_fourier_test hf₁ ψ
    _ = ∫ x : ℝ, 𝓕 ψ x • (hf₂.toLp f) x := by
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ ξ : ℝ, ψ ξ • F ξ := hdist
    _ = ∫ ξ : ℝ, g ξ • F ξ := by
      simp [ψ, Function.comp_apply]

private theorem raw_fourier_memLp {f : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2) : MemLp (𝓕 f) 2 := by
  exact (memLp_congr_ae (raw_fourier_ae_eq_L2 hf₁ hf₂)).mpr (Lp.memLp _)

private theorem raw_fourier_eLpNorm_eq {f : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume := by
  calc
    _ = eLpNorm (𝓕 (hf₂.toLp f) : Lp ℂ 2 volume) 2 volume :=
      eLpNorm_congr_ae (raw_fourier_ae_eq_L2 hf₁ hf₂)
    _ = ‖𝓕 (hf₂.toLp f)‖ₑ := (Lp.enorm_def _).symm
    _ = ‖hf₂.toLp f‖ₑ := (Lp.fourierTransformₗᵢ ℝ ℂ).enorm_map _
    _ = _ := Lp.enorm_toLp hf₂

private theorem squared_mass_eq_eLpNorm (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f volume) :
    (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2) = eLpNorm f 2 volume ^ 2 := by
  simpa using (eLpNorm_nnreal_pow_eq_lintegral
    (f := f) (μ := volume) (p := (2 : ℝ≥0)) (by norm_num) hf).symm

/-- ENNReal Plancherel for the actual ordinary Fourier integral. -/
private theorem raw_fourier_extended_plancherel {f : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    (∫⁻ ξ : ℝ, ‖𝓕 f ξ‖ₑ ^ 2) = ∫⁻ x : ℝ, ‖f x‖ₑ ^ 2 := by
  rw [squared_mass_eq_eLpNorm (𝓕 f)
      ((continuous_raw_fourier hf₁).aestronglyMeasurable),
    squared_mass_eq_eLpNorm f hf₂.aestronglyMeasurable,
    raw_fourier_eLpNorm_eq hf₁ hf₂]

/-- No measurability or finiteness hypothesis on H is necessary: nonzero
real dilation is a measurable embedding. In particular this applies to
the full, potentially infinite, spectral energy. -/
private theorem lintegral_dilate (H : ℝ → ℝ≥0∞) {c : ℝ} (hc : c ≠ 0) :
    (∫⁻ ξ : ℝ, H (c * ξ)) =
      ENNReal.ofReal |c⁻¹| * ∫⁻ t : ℝ, H t := by
  calc
    _ = ∫⁻ t : ℝ, H t ∂Measure.map (c * ·) volume :=
      ((Homeomorph.mulLeft₀ c hc).toMeasurableEquiv.measurableEmbedding.lintegral_map H).symm
    _ = _ := by
      rw [Real.map_volume_mul_left hc, lintegral_smul_measure]
      rfl

private def angularFourier (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  𝓕 f (t / (2 * Real.pi))

/-- The angular convention is the actual Bochner Fourier integral. -/
private theorem angularFourier_eq_integral (f : ℝ → ℂ) (t : ℝ) :
    angularFourier f t =
      ∫ x : ℝ, Complex.exp ((-(t * x) : ℝ) * Complex.I) * f x := by
  unfold angularFourier
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  have h : -2 * Real.pi * x * (t / (2 * Real.pi)) = -(t * x) := by
    field_simp [Real.pi_ne_zero]
    <;> ring
  rw [h, smul_eq_mul]

private theorem angular_extended_plancherel {f : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2) =
      ENNReal.ofReal (1 / (2 * Real.pi)) *
        ∫⁻ t : ℝ, ‖angularFourier f t‖ₑ ^ 2 := by
  have hc : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hpoint (ξ : ℝ) : angularFourier f ((2 * Real.pi) * ξ) = 𝓕 f ξ := by
    unfold angularFourier
    congr 1
    field_simp [Real.pi_ne_zero]
  calc
    _ = ∫⁻ ξ : ℝ, ‖𝓕 f ξ‖ₑ ^ 2 :=
      (raw_fourier_extended_plancherel hf₁ hf₂).symm
    _ = ∫⁻ ξ : ℝ, ‖angularFourier f ((2 * Real.pi) * ξ)‖ₑ ^ 2 := by
      simp_rw [hpoint]
    _ = _ := by
      simpa only [abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * Real.pi)),
        one_div] using
        lintegral_dilate (fun t : ℝ => ‖angularFourier f t‖ₑ ^ 2) hc

/-- Translation is first established for the raw Fourier integral; its
phase sign corresponds to the original displacement f(x-s). -/
private theorem raw_fourier_translation (f : ℝ → ℂ) (s ξ : ℝ) :
    𝓕 (fun x : ℝ => f (x - s)) ξ =
      (Real.fourierChar (-(s * ξ)) : ℂ) * 𝓕 f ξ := by
  simpa [Real.fourier_eq, VectorFourier.fourierIntegral,
    Function.comp_def, sub_eq_add_neg, Real.inner_apply,
    Circle.smul_def, smul_eq_mul, mul_comm] using
    congrFun (VectorFourier.fourierIntegral_comp_add_right
      Real.fourierChar volume (innerₗ ℝ) f (-s)) ξ

private theorem raw_fourier_sub {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    𝓕 (fun x => f x - g x) ξ = 𝓕 f ξ - 𝓕 g ξ := by
  simp only [Real.fourier_eq, smul_sub]
  exact integral_sub ((Real.fourierIntegral_convergent_iff ξ).2 hf)
    ((Real.fourierIntegral_convergent_iff ξ).2 hg)


/-
SOURCE-LOCAL APPEND FRAGMENT, NOT COMPILED. No kernel acceptance claimed.

Append inside ActualGammaRawFourierBridgeDraft20261017, after the existing
raw_fourier_translation and raw_fourier_sub helpers and before its final end.
This fragment consumes the existing raw_fourier_extended_plancherel helper;
it does not reproduce the raw/L2 Fourier compatibility argument.

Only this persistent research fragment is written. No worktree or canonical
source is edited and no compiler is started. Mathlib source pin used for API
alignment: db584cd6d46c92f209a44c0f1c829460d327499d.
-/

private def lineGapMass (f : ℝ → ℂ) (s : ℝ) : ℝ :=
  ∫ x : ℝ, ‖f x - f (x - s)‖ ^ 2

private theorem linePhase_gap_norm_sq (ξ s : ℝ) :
    ‖(1 : ℂ) - (Real.fourierChar (-(s * ξ)) : ℂ)‖ ^ 2 =
      2 * (1 - Real.cos ((2 * Real.pi * ξ) * s)) := by
  have hre : (Real.fourierChar (-(s * ξ)) : ℂ).re =
      Real.cos ((2 * Real.pi * ξ) * s) := by
    rw [Real.fourierChar_apply, Complex.exp_ofReal_mul_I_re]
    have harg : 2 * Real.pi * -(s * ξ) = -((2 * Real.pi * ξ) * s) := by ring
    rw [harg, Real.cos_neg]
  rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_one, Circle.normSq_coe]
  simp only [one_mul, Complex.conj_re]
  rw [hre]
  ring

/-- The original L1∩L2 function's finite per-shift mass equals its raw
Fourier spectral mass, in ENNReal. The function may have infinite full
Gamma jump energy; that quantity is never assumed finite here. -/
private theorem lineGapMass_eq_lintegral {f : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2 volume) (s : ℝ) :
    ENNReal.ofReal (lineGapMass f s) =
      ∫⁻ ξ : ℝ,
        ENNReal.ofReal (2 * (1 - Real.cos ((2 * Real.pi * ξ) * s))) *
          ‖𝓕 f ξ‖ₑ ^ 2 := by
  have hshift₁ : Integrable (fun x : ℝ => f (x - s)) volume := by
    simpa only [Function.comp_def] using
      (measurePreserving_sub_right (volume : Measure ℝ) s).integrable_comp_of_integrable hf₁
  have hshift₂ : MemLp (fun x : ℝ => f (x - s)) 2 volume := by
    simpa only [Function.comp_def] using
      hf₂.comp_measurePreserving (measurePreserving_sub_right (volume : Measure ℝ) s)
  have hgap₁ : Integrable (fun x : ℝ => f x - f (x - s)) volume :=
    hf₁.sub hshift₁
  have hgap₂ : MemLp (fun x : ℝ => f x - f (x - s)) 2 volume :=
    hf₂.sub hshift₂
  have hgap_sq : Integrable (fun x : ℝ => ‖f x - f (x - s)‖ ^ 2) volume :=
    hgap₂.integrable_norm_pow (p := 2) (by norm_num)
  have htransform (ξ : ℝ) :
      𝓕 (fun x : ℝ => f x - f (x - s)) ξ =
        ((1 : ℂ) - (Real.fourierChar (-(s * ξ)) : ℂ)) * 𝓕 f ξ := by
    rw [raw_fourier_sub hf₁ hshift₁ ξ, raw_fourier_translation]
    ring
  have hphase (ξ : ℝ) :
      ‖(1 : ℂ) - (Real.fourierChar (-(s * ξ)) : ℂ)‖ₑ ^ 2 =
        ENNReal.ofReal (2 * (1 - Real.cos ((2 * Real.pi * ξ) * s))) := by
    calc
      _ = ENNReal.ofReal
          (‖(1 : ℂ) - (Real.fourierChar (-(s * ξ)) : ℂ)‖ ^ 2) := by
        rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
      _ = _ := congrArg ENNReal.ofReal (linePhase_gap_norm_sq ξ s)
  calc
    ENNReal.ofReal (lineGapMass f s) =
        ∫⁻ x : ℝ, ENNReal.ofReal (‖f x - f (x - s)‖ ^ 2) := by
      unfold lineGapMass
      exact ofReal_integral_eq_lintegral_ofReal hgap_sq
        (Filter.Eventually.of_forall fun x => sq_nonneg _)
    _ = ∫⁻ x : ℝ, ‖f x - f (x - s)‖ₑ ^ 2 := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]
    _ = ∫⁻ ξ : ℝ, ‖𝓕 (fun x : ℝ => f x - f (x - s)) ξ‖ₑ ^ 2 :=
      (raw_fourier_extended_plancherel hgap₁ hgap₂).symm
    _ = _ := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall fun ξ => by
        dsimp only
        rw [htransform ξ, enorm_mul, mul_pow, hphase ξ]

end ActualGammaRawFourierBridgeDraft20261017


/-
Source-local application fragment; not compiled.
Append after the accepted raw Fourier bridge and the per-shift gap fragment,
with the original ArchimedeanJumpDecomposition body in the same source unit.
The final equality permits infinite total energy. No smooth-core premise is used.
-/

namespace ActualGammaRawFourierBridgeDraft20261017

private abbrev actualDensity : ℝ → ℝ :=
  D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity

private def actualIncrement (z : ℝ) : ℝ :=
  (Complex.digamma ((1 / 4 : ℂ) + Complex.I * ((z / 2 : ℝ) : ℂ))).re -
    (Complex.digamma (1 / 4)).re

private def cyclicGap (ξ s : ℝ) : ℝ :=
  2 * (1 - Real.cos ((2 * Real.pi * ξ) * s))

private theorem extended_line_energy_eq_frequency_integral
    (k : ℝ → ℝ) (hk : Measurable k) {f : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    (∫⁻ s : ℝ in Ioi 0,
      ENNReal.ofReal (k s) * ENNReal.ofReal (lineGapMass f s)) =
      ∫⁻ ξ : ℝ,
        (∫⁻ s : ℝ in Ioi 0,
          ENNReal.ofReal (k s) * ENNReal.ofReal (cyclicGap ξ s)) *
        ‖𝓕 f ξ‖ₑ ^ 2 := by
  have hgap : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (cyclicGap p.2 p.1)) := by
    unfold cyclicGap
    fun_prop
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (k p.1) *
        (ENNReal.ofReal (cyclicGap p.2 p.1) * ‖𝓕 f p.2‖ₑ ^ 2)) :=
    (ENNReal.measurable_ofReal.comp (hk.comp measurable_fst)).mul
      (hgap.mul (((continuous_raw_fourier hf₁).measurable.comp
        measurable_snd).enorm.pow_const 2))
  calc
    _ = ∫⁻ s : ℝ in Ioi 0, ∫⁻ ξ : ℝ,
        ENNReal.ofReal (k s) *
          (ENNReal.ofReal (cyclicGap ξ s) * ‖𝓕 f ξ‖ₑ ^ 2) := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall fun s => by
        dsimp only
        rw [lineGapMass_eq_lintegral hf₁ hf₂ s]
        exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ ξ : ℝ, ∫⁻ s : ℝ in Ioi 0,
        ENNReal.ofReal (k s) *
          (ENNReal.ofReal (cyclicGap ξ s) * ‖𝓕 f ξ‖ₑ ^ 2) :=
      lintegral_lintegral_swap hmeas.aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall fun ξ => by
        simp_rw [← mul_assoc]
        exact lintegral_mul_const' _ _ (by finiteness)

private theorem actual_line_spectralWeight (ξ : ℝ) :
    (∫⁻ s : ℝ in Ioi 0,
      ENNReal.ofReal (actualDensity s) * ENNReal.ofReal (cyclicGap ξ s)) =
      ENNReal.ofReal (actualIncrement (2 * Real.pi * ξ)) := by
  let z : ℝ := 2 * Real.pi * ξ
  have hInt : IntegrableOn
      (fun s : ℝ => 2 * actualDensity s * (1 - Real.cos (z * s))) (Ioi 0) :=
    D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.levy_kernel_integrableOn z
  have hnn : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      0 ≤ 2 * actualDensity s * (1 - Real.cos (z * s)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (mul_nonneg (by norm_num)
      (D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.jump_density_nonnegative hs))
      (sub_nonneg.mpr (Real.cos_le_one _))
  calc
    _ = ∫⁻ s : ℝ in Ioi 0,
        ENNReal.ofReal (2 * actualDensity s * (1 - Real.cos (z * s))) := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      rw [← ENNReal.ofReal_mul
        (D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.jump_density_nonnegative hs)]
      congr 1
      dsimp only [cyclicGap, z]
      ring
    _ = ENNReal.ofReal
        (∫ s : ℝ in Ioi 0, 2 * actualDensity s * (1 - Real.cos (z * s))) :=
      (ofReal_integral_eq_lintegral_ofReal hInt hnn).symm
    _ = _ := congrArg ENNReal.ofReal
      (D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.levy_integral_eq_digamma_increment z)

private theorem actual_gamma_whole_line_energy_eq_angular_integral
    {f : ℝ → ℂ} (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    (∫⁻ s : ℝ in Ioi 0,
      ENNReal.ofReal (actualDensity s) * ENNReal.ofReal (lineGapMass f s)) =
      ENNReal.ofReal (1 / (2 * Real.pi)) *
        ∫⁻ z : ℝ, ENNReal.ofReal (actualIncrement z) *
          ‖angularFourier f z‖ₑ ^ 2 := by
  have hk : Measurable actualDensity := by
    unfold actualDensity
      D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity
    fun_prop
  have hc : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hpoint (ξ : ℝ) : angularFourier f ((2 * Real.pi) * ξ) = 𝓕 f ξ := by
    unfold angularFourier
    congr 1
    field_simp [Real.pi_ne_zero]
  calc
    _ = ∫⁻ ξ : ℝ, ENNReal.ofReal (actualIncrement (2 * Real.pi * ξ)) *
        ‖𝓕 f ξ‖ₑ ^ 2 := by
      rw [extended_line_energy_eq_frequency_integral actualDensity hk hf₁ hf₂]
      simp_rw [actual_line_spectralWeight]
    _ = ∫⁻ ξ : ℝ, ENNReal.ofReal (actualIncrement ((2 * Real.pi) * ξ)) *
        ‖angularFourier f ((2 * Real.pi) * ξ)‖ₑ ^ 2 := by
      simp_rw [hpoint]
    _ = _ := by
      simpa only [abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * Real.pi)),
        one_div] using
        lintegral_dilate (fun z : ℝ => ENNReal.ofReal (actualIncrement z) *
          ‖angularFourier f z‖ₑ ^ 2) hc

end ActualGammaRawFourierBridgeDraft20261017

/- ASSEMBLY CONSTITUENT: uncompiled_spectral_mollification -/
/-
UNCOMPILED SOURCE-LOCAL CORE CANDIDATE, 2026-10-18.

D-only. No compiler, worktree or canonical module was touched. This fragment
consumes ActualGammaWholeLineEnergy.actual-energy-v2.immutable-source.lean,
the core exterior helpers and the actualGammaExitMeasure binding in their
same source unit. It does not reprove the accepted whole-line bridge.

This is the spectral alternative to the translation fragment: do not append
both, since coreL2Mass/coreMollify intentionally have the same local names.
Hoist these imports if absent:
  Mathlib.Analysis.Fourier.Convolution
  Mathlib.Analysis.Calculus.BumpFunction.Convolution
  Mathlib.Analysis.Calculus.ContDiff.Convolution
  Mathlib.MeasureTheory.Function.LpSpace.Indicator
  Mathlib.Analysis.SpecificLimits.Basic

Source API inspection used the persistent Mathlib source cache. The actual
Lean v4.35 / Mathlib 56a005855 check belongs to the parent. All proof terms
below are candidates, not a claim of elaboration or kernel acceptance.

G is merely measurable L2 with compact support and finite actual energy.
Neither smoothness nor continuity of G is assumed. No Jensen supplier or
general L2-convolution approximation theorem is assumed.
-/

noncomputable section

namespace ActualGammaCompactCoreDraft20261018

open MeasureTheory Set Filter
open ActualGammaRawFourierBridgeDraft20261017
open scoped ENNReal Topology FourierTransform Convolution Pointwise

private def coreL2Mass (G : ℝ → ℂ) : ℝ≥0∞ := ∫⁻ x : ℝ, ‖G x‖ₑ ^ 2

private def coreMollify (φ : ContDiffBump (0 : ℝ)) (G : ℝ → ℂ) : ℝ → ℂ :=
  convolution (φ.normed volume) G (ContinuousLinearMap.lsmul ℝ ℝ) volume

private def coreComplexKernel (φ : ContDiffBump (0 : ℝ)) (x : ℝ) : ℂ :=
  (φ.normed volume x : ℂ)

private theorem coreComplexKernel_integrable (φ : ContDiffBump (0 : ℝ)) :
    Integrable (coreComplexKernel φ) :=
  Complex.ofRealCLM.integrable_comp φ.integrable_normed

private theorem coreMollify_eq_complex_convolution
    (φ : ContDiffBump (0 : ℝ)) (G : ℝ → ℂ) :
    coreMollify φ G =
      convolution (coreComplexKernel φ) G (ContinuousLinearMap.mul ℂ ℂ) volume := by
  funext x
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    simp only [coreComplexKernel, ContinuousLinearMap.lsmul_apply,
      ContinuousLinearMap.mul_apply', Complex.real_smul]

private theorem coreMollify_integrable
    (φ : ContDiffBump (0 : ℝ)) (G : ℝ → ℂ) (hG : Integrable G) :
    Integrable (coreMollify φ G) :=
  φ.integrable_normed.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hG

private theorem coreMollify_contDiff
    (φ : ContDiffBump (0 : ℝ)) (G : ℝ → ℂ) (hG2 : MemLp G 2 volume) :
    ContDiff ℝ ∞ (coreMollify φ G) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    φ.contDiff_normed (hG2.locallyIntegrable (by norm_num))

private theorem coreMollify_hasCompactSupport
    (φ : ContDiffBump (0 : ℝ)) (G : ℝ → ℂ) (hGc : HasCompactSupport G) :
    HasCompactSupport (coreMollify φ G) :=
  φ.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hGc

private theorem coreMollify_memLp
    (φ : ContDiffBump (0 : ℝ)) (G : ℝ → ℂ)
    (hG2 : MemLp G 2 volume) (hGc : HasCompactSupport G) :
    MemLp (coreMollify φ G) 2 volume :=
  (coreMollify_contDiff φ G hG2).continuous.memLp_of_hasCompactSupport
    (coreMollify_hasCompactSupport φ G hGc)

/-- L1 is obtained from compact support and local integrability, with no
continuity premise on G. -/
private theorem core_integrable_of_memLp_compact
    (G : ℝ → ℂ) (hG2 : MemLp G 2 volume) (hGc : HasCompactSupport G) :
    Integrable G :=
  (integrableOn_iff_integrable_of_support_subset (subset_tsupport G)).mp
    ((hG2.locallyIntegrable (by norm_num)).integrableOn_isCompact hGc)

/-- The precise support budget after fixing the inward cutoff. -/
private theorem coreMollify_tsupport_subset
    (φ : ContDiffBump (0 : ℝ)) (G : ℝ → ℂ) (l r : ℝ)
    (hGsupport : tsupport G ⊆ Icc l r) :
    tsupport (coreMollify φ G) ⊆ Icc (l - φ.rOut) (r + φ.rOut) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  obtain ⟨u, hu, v, hv, rfl⟩ :=
    support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) hx
  rw [φ.support_normed_eq] at hu
  have huabs : |u| < φ.rOut := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hu
  have hvI := hGsupport (subset_tsupport G hv)
  exact ⟨by linarith [(abs_lt.mp huabs).1, hvI.1],
    by linarith [(abs_lt.mp huabs).2, hvI.2]⟩

private theorem coreMollify_tsupport_inside
    (φ : ContDiffBump (0 : ℝ)) (G : ℝ → ℂ) (a η : ℝ)
    (hmargin : φ.rOut < η) (hGsupport : tsupport G ⊆ Icc (-a + η) (a - η)) :
    tsupport (coreMollify φ G) ⊆ Ioo (-a) a := by
  intro x hx
  have h := coreMollify_tsupport_subset φ G (-a + η) (a - η) hGsupport hx
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The Fourier transform of a unit nonnegative kernel has modulus at most 1. -/
private theorem coreComplexKernel_fourier_norm_le_one
    (φ : ContDiffBump (0 : ℝ)) (ξ : ℝ) : ‖𝓕 (coreComplexKernel φ) ξ‖ ≤ 1 := by
  calc
    _ ≤ ∫ x : ℝ, ‖coreComplexKernel φ x‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar volume (innerₗ ℝ) (coreComplexKernel φ) ξ
    _ = ∫ x : ℝ, φ.normed volume x := by
      congr 1
      funext x
      exact Complex.norm_of_nonneg (φ.nonneg_normed x)
    _ = 1 := φ.integral_normed

private theorem coreComplexKernel_fourier_gap_sq_le_four
    (φ : ContDiffBump (0 : ℝ)) (ξ : ℝ) :
    ‖𝓕 (coreComplexKernel φ) ξ - 1‖ₑ ^ 2 ≤ 4 := by
  have hn : ‖𝓕 (coreComplexKernel φ) ξ - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖𝓕 (coreComplexKernel φ) ξ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 := by
        calc
          _ ≤ 1 + ‖(1 : ℂ)‖ :=
            add_le_add (coreComplexKernel_fourier_norm_le_one φ ξ) (le_refl _)
          _ = 2 := by norm_num
  have he : ‖𝓕 (coreComplexKernel φ) ξ - 1‖ₑ ≤ (2 : ℝ≥0∞) := by
    simpa only [ofReal_norm, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hn
  calc
    _ ≤ (2 : ℝ≥0∞) ^ 2 := pow_le_pow_left' he 2
    _ = 4 := by norm_num

/-- The Fourier multiplier converges to 1 by applying Mathlib's existing
bump approximate-identity theorem only to a continuous Fourier character. -/
private theorem coreComplexKernel_fourier_tendsto_one
    {ι : Type*} {l : Filter ι} (φ : ι → ContDiffBump (0 : ℝ))
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) (ξ : ℝ) :
    Tendsto (fun i => 𝓕 (coreComplexKernel (φ i)) ξ) l (𝓝 1) := by
  let character : ℝ → ℂ := fun x => (Real.fourierChar (x * ξ) : ℂ)
  have hchar : Continuous character := by
    dsimp only [character]
    fun_prop
  have heq (i : ι) :
      ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] character) 0 =
        𝓕 (coreComplexKernel (φ i)) ξ := by
    simp only [convolution_def, Real.fourier_eq, Real.inner_apply]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp [character, coreComplexKernel, Circle.smul_def, smul_eq_mul,
        Complex.real_smul, mul_comm]
  have hconv :=
    ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hφ hchar 0
  have hzero : character 0 = (1 : ℂ) := by
    simp [character, Real.fourierChar_apply]
  rw [hzero] at hconv
  apply Tendsto.congr' (Filter.Eventually.of_forall heq) hconv

/-- A single DCT works for both unweighted L2 mass and actual Gamma energy.
B is the already integrable spectral density of G. -/
private theorem coreFourierMultiplier_lintegral_tendsto_zero
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (φ : ι → ContDiffBump (0 : ℝ))
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (B : ℝ → ℝ≥0∞) (hB : Measurable B)
    (hBfin : (∫⁻ z : ℝ, B z) < (⊤ : ℝ≥0∞)) :
    Tendsto (fun i => ∫⁻ z : ℝ,
      ‖angularFourier (coreComplexKernel (φ i)) z - 1‖ₑ ^ 2 * B z) l (𝓝 0) := by
  have hm (i : ι) : Measurable (fun z : ℝ =>
      ‖angularFourier (coreComplexKernel (φ i)) z - 1‖ₑ ^ 2 * B z) := by
    have hc : Continuous (angularFourier (coreComplexKernel (φ i))) :=
      (continuous_raw_fourier (coreComplexKernel_integrable (φ i))).comp
        (continuous_id.div_const (2 * Real.pi))
    exact ((hc.sub continuous_const).measurable.enorm.pow_const 2).mul hB
  have hbound (i : ι) (z : ℝ) :
      ‖angularFourier (coreComplexKernel (φ i)) z - 1‖ₑ ^ 2 * B z ≤ 4 * B z := by
    gcongr
    exact coreComplexKernel_fourier_gap_sq_le_four (φ i) (z / (2 * Real.pi))
  have hfin : (∫⁻ z : ℝ, 4 * B z) ≠ (⊤ : ℝ≥0∞) := by
    rw [lintegral_const_mul' _ _ (by norm_num)]
    exact (ENNReal.mul_lt_top (by norm_num) hBfin).ne
  have hlim : ∀ᵐ z : ℝ, Tendsto (fun i =>
      ‖angularFourier (coreComplexKernel (φ i)) z - 1‖ₑ ^ 2 * B z) l (𝓝 0) := by
    filter_upwards [ae_lt_top hB hBfin.ne] with z hz
    have ht : Tendsto (fun i =>
        ‖angularFourier (coreComplexKernel (φ i)) z - 1‖ₑ ^ 2) l (𝓝 0) := by
      have htc := (coreComplexKernel_fourier_tendsto_one φ hφ
        (z / (2 * Real.pi))).sub
        (tendsto_const_nhds : Tendsto (fun _ : ι => (1 : ℂ)) l (𝓝 1))
      have htc' : Tendsto (fun i =>
          𝓕 (coreComplexKernel (φ i)) (z / (2 * Real.pi)) - 1) l
          (𝓝 (0 : ℂ)) := by
        simpa only [sub_self] using htc
      have hteRaw : Tendsto (fun i =>
          ‖𝓕 (coreComplexKernel (φ i)) (z / (2 * Real.pi)) - 1‖ₑ) l
          (𝓝 (0 : ℝ≥0∞)) := by
        simpa only [Function.comp_def, enorm_zero] using
          ((continuous_enorm : Continuous (fun w : ℂ => ‖w‖ₑ)).tendsto 0).comp htc'
      have hte : Tendsto (fun i =>
          ‖angularFourier (coreComplexKernel (φ i)) z - 1‖ₑ) l
          (𝓝 (0 : ℝ≥0∞)) := by
        simpa only [angularFourier] using hteRaw
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
        (ENNReal.Tendsto.pow (n := 2) hte)
    simpa only [zero_mul] using
      (ENNReal.Tendsto.mul_const ht (Or.inr hz.ne) :
        Tendsto (fun i =>
          ‖angularFourier (coreComplexKernel (φ i)) z - 1‖ₑ ^ 2 * B z) l
          (𝓝 ((0 : ℝ≥0∞) * B z)))
  simpa only [lintegral_zero] using
    tendsto_lintegral_filter_of_dominated_convergence (fun z => 4 * B z)
      (Eventually.of_forall hm)
      (Eventually.of_forall fun i => Eventually.of_forall (hbound i)) hfin hlim

private theorem coreMollify_angular_fourier_error
    (φ : ContDiffBump (0 : ℝ)) (G : ℝ → ℂ) (hG1 : Integrable G) (z : ℝ) :
    angularFourier (fun x => coreMollify φ G x - G x) z =
      (angularFourier (coreComplexKernel φ) z - 1) * angularFourier G z := by
  unfold angularFourier
  rw [raw_fourier_sub (coreMollify_integrable φ G hG1) hG1,
    coreMollify_eq_complex_convolution,
    Real.fourier_mul_convolution_eq (coreComplexKernel_integrable φ) hG1]
  ring

/-- Measurability of the actual weight follows from its accepted positive
integral representation; no regularity of digamma is reproved. -/
private theorem core_actual_spectral_weight_measurable :
    Measurable (fun z : ℝ => ENNReal.ofReal (actualIncrement z)) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (actualDensity p.2) *
        ENNReal.ofReal (cyclicGap (p.1 / (2 * Real.pi)) p.2)) := by
    unfold actualDensity
      D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity cyclicGap
    fun_prop
  have heq (z : ℝ) : (∫⁻ s : ℝ in Ioi 0,
      ENNReal.ofReal (actualDensity s) *
        ENNReal.ofReal (cyclicGap (z / (2 * Real.pi)) s)) =
      ENNReal.ofReal (actualIncrement z) := by
    rw [actual_line_spectralWeight]
    congr 2
    field_simp [Real.pi_ne_zero]
  simpa only [heq] using
    (hm.lintegral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ))))

/-- Bind the exact directional-energy convention to the already accepted
whole-line angular Fourier identity. -/
private theorem core_actual_energy_eq_angular
    (G : ℝ → ℂ) (hG : Measurable G) (hG1 : Integrable G) (hG2 : MemLp G 2 volume) :
    directionalEnergy actualGammaExitMeasure G =
      ENNReal.ofReal (1 / (2 * Real.pi)) *
        ∫⁻ z : ℝ, ENNReal.ofReal (actualIncrement z) * ‖angularFourier G z‖ₑ ^ 2 := by
  have hscale : Measurable (fun s : ℝ => ∫⁻ x : ℝ, ‖G x - G (x - s)‖ₑ ^ 2) := by
    have hm : Measurable (fun p : ℝ × ℝ => ‖G p.2 - G (p.2 - p.1)‖ₑ ^ 2) := by
      fun_prop
    exact hm.lintegral_prod_right'
  have hρ : Measurable (fun s => ENNReal.ofReal (actualDensity s)) := by
    unfold actualDensity
      D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity
    fun_prop
  have hgap (s : ℝ) : (∫⁻ x : ℝ, ‖G x - G (x - s)‖ₑ ^ 2) =
      ENNReal.ofReal (lineGapMass G s) := by
    have hg2 : MemLp (fun x : ℝ => G x - G (x - s)) 2 volume :=
      hG2.sub (hG2.comp_measurePreserving (measurePreserving_sub_right volume s))
    have hsq := hg2.integrable_norm_pow (p := 2) (by norm_num)
    rw [lineGapMass, ofReal_integral_eq_lintegral_ofReal hsq
      (Eventually.of_forall fun x => sq_nonneg _)]
    apply lintegral_congr_ae
    exact Eventually.of_forall fun x => by
      simpa only [ofReal_norm] using
        (ENNReal.ofReal_pow (norm_nonneg (G x - G (x - s))) 2).symm
  calc
    _ = ∫⁻ s : ℝ in Ioi 0, ENNReal.ofReal (actualDensity s) *
        (∫⁻ x : ℝ, ‖G x - G (x - s)‖ₑ ^ 2) := by
      unfold directionalEnergy actualGammaExitMeasure
      exact lintegral_withDensity_eq_lintegral_mul _ hρ hscale
    _ = ∫⁻ s : ℝ in Ioi 0,
        ENNReal.ofReal (actualDensity s) * ENNReal.ofReal (lineGapMass G s) := by
      apply lintegral_congr_ae
      exact Eventually.of_forall fun s => by dsimp only; rw [hgap]
    _ = _ := actual_gamma_whole_line_energy_eq_angular_integral hG1 hG2

/-- Smooth compact convolution converges in both physical mass and actual
Gamma energy for merely measurable compactly supported L2 data. -/
private theorem coreMollify_mass_and_actual_energy_tendsto_zero
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (φ : ι → ContDiffBump (0 : ℝ))
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (G : ℝ → ℂ) (hG : Measurable G) (hG2 : MemLp G 2 volume)
    (hGc : HasCompactSupport G)
    (hGE : directionalEnergy actualGammaExitMeasure G < (⊤ : ℝ≥0∞)) :
    Tendsto (fun i => coreL2Mass (fun x => coreMollify (φ i) G x - G x) +
      directionalEnergy actualGammaExitMeasure (fun x => coreMollify (φ i) G x - G x))
      l (𝓝 0) := by
  let c : ℝ≥0∞ := ENNReal.ofReal (1 / (2 * Real.pi))
  have hc0 : c ≠ 0 := by dsimp only [c]; positivity
  have hcfin : c ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hG1 : Integrable G := core_integrable_of_memLp_compact G hG2 hGc
  have hGhat : Measurable (angularFourier G) :=
    ((continuous_raw_fourier hG1).comp (continuous_id.div_const (2 * Real.pi))).measurable
  have hmassfin : (∫⁻ z : ℝ, ‖angularFourier G z‖ₑ ^ 2) < (⊤ : ℝ≥0∞) := by
    apply ENNReal.lt_top_of_mul_ne_top_right (a := c)
      (b := ∫⁻ z : ℝ, ‖angularFourier G z‖ₑ ^ 2) _ hc0
    change ENNReal.ofReal (1 / (2 * Real.pi)) *
      (∫⁻ z : ℝ, ‖angularFourier G z‖ₑ ^ 2) ≠ (⊤ : ℝ≥0∞)
    rw [← angular_extended_plancherel hG1 hG2,
      squared_mass_eq_eLpNorm _ hG2.aestronglyMeasurable]
    exact (ENNReal.pow_lt_top hG2.eLpNorm_lt_top).ne
  have henergyfin : (∫⁻ z : ℝ,
      ENNReal.ofReal (actualIncrement z) * ‖angularFourier G z‖ₑ ^ 2) < (⊤ : ℝ≥0∞) := by
    apply ENNReal.lt_top_of_mul_ne_top_right (a := c) _ hc0
    change ENNReal.ofReal (1 / (2 * Real.pi)) *
      (∫⁻ z : ℝ, ENNReal.ofReal (actualIncrement z) * ‖angularFourier G z‖ₑ ^ 2)
        ≠ (⊤ : ℝ≥0∞)
    rw [← core_actual_energy_eq_angular G hG hG1 hG2]
    exact hGE.ne
  have hM := coreFourierMultiplier_lintegral_tendsto_zero φ hφ
    (fun z => ‖angularFourier G z‖ₑ ^ 2) (hGhat.enorm.pow_const 2) hmassfin
  have hE := coreFourierMultiplier_lintegral_tendsto_zero φ hφ
    (fun z => ENNReal.ofReal (actualIncrement z) * ‖angularFourier G z‖ₑ ^ 2)
    (core_actual_spectral_weight_measurable.mul (hGhat.enorm.pow_const 2)) henergyfin
  have hscaled := ENNReal.Tendsto.const_mul (hM.add hE) (Or.inr hcfin)
  have heq (i : ι) : coreL2Mass (fun x => coreMollify (φ i) G x - G x) +
      directionalEnergy actualGammaExitMeasure (fun x => coreMollify (φ i) G x - G x) =
      c * ((∫⁻ z : ℝ,
        ‖angularFourier (coreComplexKernel (φ i)) z - 1‖ₑ ^ 2 *
          ‖angularFourier G z‖ₑ ^ 2) +
        ∫⁻ z : ℝ, ‖angularFourier (coreComplexKernel (φ i)) z - 1‖ₑ ^ 2 *
          (ENNReal.ofReal (actualIncrement z) * ‖angularFourier G z‖ₑ ^ 2)) := by
    have hf1 := (coreMollify_integrable (φ i) G hG1).sub hG1
    have hf2 := (coreMollify_memLp (φ i) G hG2 hGc).sub hG2
    have hfm := (coreMollify_contDiff (φ i) G hG2).continuous.measurable.sub hG
    change (∫⁻ x : ℝ, ‖(coreMollify (φ i) G - G) x‖ₑ ^ 2) +
      directionalEnergy actualGammaExitMeasure (coreMollify (φ i) G - G) = _
    rw [angular_extended_plancherel hf1 hf2,
      core_actual_energy_eq_angular _ hfm hf1 hf2]
    change c * _ + c * _ = c * _
    rw [← mul_add]
    apply congrArg (fun t : ℝ≥0∞ => c * t)
    apply congrArg₂ (fun u v : ℝ≥0∞ => u + v)
    · apply lintegral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp only
        change ‖angularFourier
          (fun x => coreMollify (φ i) G x - G x) z‖ₑ ^ 2 = _
        rw [coreMollify_angular_fourier_error (φ i) G hG1 z, enorm_mul, mul_pow]
    · apply lintegral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp only
        change ENNReal.ofReal (actualIncrement z) *
          ‖angularFourier (fun x => coreMollify (φ i) G x - G x) z‖ₑ ^ 2 = _
        rw [coreMollify_angular_fourier_error (φ i) G hG1 z, enorm_mul, mul_pow]
        ring
  simpa only [heq, zero_add, mul_zero] using hscaled

/-- Shrinking kernels eventually respect any fixed positive inward margin.
Together with the preceding theorem this supplies the smooth compact core
approximation after the cutoff has been fixed. -/
private theorem coreMollify_eventually_tsupport_inside
    {ι : Type*} {l : Filter ι} (φ : ι → ContDiffBump (0 : ℝ))
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (G : ℝ → ℂ) (a η : ℝ) (hη : 0 < η)
    (hGsupport : tsupport G ⊆ Icc (-a + η) (a - η)) :
    ∀ᶠ i in l, tsupport (coreMollify (φ i) G) ⊆ Ioo (-a) a := by
  filter_upwards [hφ.eventually (gt_mem_nhds hη)] with i hi
  exact coreMollify_tsupport_inside (φ i) G a η hi hGsupport

private def coreBumpSequence (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := (1 / ((n : ℝ) + 1)) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hp : 0 < (1 / ((n : ℝ) + 1)) := by positivity
    linarith

private theorem coreBumpSequence_rOut_tendsto_zero :
    Tendsto (fun n : ℕ => (coreBumpSequence n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The usable fixed-cutoff core statement, with an explicit smooth compact
approximant in the original open window and arbitrarily small sum of the
physical L2 mass error and actual Gamma form error. -/
private theorem exists_smooth_actual_gamma_approximation_of_inward_support
    (G : ℝ → ℂ) (hG : Measurable G) (hG2 : MemLp G 2 volume)
    (hGc : HasCompactSupport G)
    (hGE : directionalEnergy actualGammaExitMeasure G < (⊤ : ℝ≥0∞))
    (a η : ℝ) (hη : 0 < η) (hGsupport : tsupport G ⊆ Icc (-a + η) (a - η))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℝ → ℂ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      tsupport H ⊆ Ioo (-a) a ∧
      coreL2Mass (fun x => H x - G x) +
        directionalEnergy actualGammaExitMeasure (fun x => H x - G x) <
          ENNReal.ofReal ε := by
  have hconv := coreMollify_mass_and_actual_energy_tendsto_zero
    coreBumpSequence coreBumpSequence_rOut_tendsto_zero G hG hG2 hGc hGE
  have hs := coreMollify_eventually_tsupport_inside
    coreBumpSequence coreBumpSequence_rOut_tendsto_zero G a η hη hGsupport
  have he : ∀ᶠ n : ℕ in atTop,
      coreL2Mass (fun x => coreMollify (coreBumpSequence n) G x - G x) +
        directionalEnergy actualGammaExitMeasure
          (fun x => coreMollify (coreBumpSequence n) G x - G x) < ENNReal.ofReal ε :=
    hconv.eventually (gt_mem_nhds (by positivity : (0 : ℝ≥0∞) < ENNReal.ofReal ε))
  obtain ⟨n, hn, he⟩ := (hs.and he).exists
  exact ⟨coreMollify (coreBumpSequence n) G,
    coreMollify_contDiff _ G hG2, coreMollify_hasCompactSupport _ G hGc, hn, he⟩

end ActualGammaCompactCoreDraft20261018

/- ASSEMBLY CONSTITUENT: original_ioc_smooth_consumer_uncompiled -/
/-
STATIC ORIGINAL-Ioc SMOOTH-CORE CONSUMER, 2026-10-18.
UNCOMPILED. No compiler, WT, canonical module or download was used.

Append after ActualGammaCompactCore.spectral-v1.static-assembled.immutable-source.lean
in the same source unit. The fragment consumes the accepted-v433 v6 AE/cutoff
theorems and the uncompiled spectral mollification terms already in that unit.
It introduces no owner body, extra zero extension, or Fourier convention.

The final input is precisely original u in L2(volume.restrict(Ioc(-a,a)))
and finite actual positive-scale Gamma energy of the EXISTING zero extension.
No smoothness, continuity, endpoint trace, logarithmic domain or additional
raw-Fourier L2 hypothesis is imposed on u. No assumed diagonal supplier is
used: the two approximation choices and the factor-two quadratic bound are
spelled out below. Arbitrary a is allowed, including an empty source interval.

All statements and proof terms below remain unelaborated candidates.
-/

noncomputable section

namespace ActualGammaCompactCoreDraft20261018

open MeasureTheory Set Filter
open ActualGammaCornerTransportDraft20261017
open ActualGammaRawFourierBridgeDraft20261017
open scoped ENNReal Topology

private def coreGraphSize (nu : Measure ℝ) (F : ℝ → ℂ) : ℝ≥0∞ :=
  coreL2Mass F + directionalEnergy nu F

private theorem coreComplexAdd_enorm_sq_le (z w : ℂ) :
    ‖z + w‖ₑ ^ 2 ≤ 2 * ‖z‖ₑ ^ 2 + 2 * ‖w‖ₑ ^ 2 := by
  have h := ENNReal.ofReal_le_ofReal (complex_norm_add_sq_le z w)
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_pow (norm_nonneg _) 2,
    ENNReal.ofReal_pow (norm_nonneg _) 2,
    ENNReal.ofReal_pow (norm_nonneg _) 2] at h
  simpa only [ofReal_norm, ENNReal.ofReal_ofNat] using h

private theorem coreL2Mass_add_le
    (F G : ℝ → ℂ) (hF : Measurable F) (hG : Measurable G) :
    coreL2Mass (fun x => F x + G x) ≤ 2 * coreL2Mass F + 2 * coreL2Mass G := by
  calc
    _ ≤ ∫⁻ x : ℝ, 2 * ‖F x‖ₑ ^ 2 + 2 * ‖G x‖ₑ ^ 2 :=
      lintegral_mono fun x => coreComplexAdd_enorm_sq_le (F x) (G x)
    _ = _ := by
      simp only [coreL2Mass]
      calc
        _ = (∫⁻ x : ℝ, 2 * ‖F x‖ₑ ^ 2) +
            ∫⁻ x : ℝ, 2 * ‖G x‖ₑ ^ 2 :=
          lintegral_add_left' ((measurable_const.mul (hF.enorm.pow_const 2)).aemeasurable) _
        _ = _ := by
          rw [lintegral_const_mul' _ _ (by norm_num),
            lintegral_const_mul' _ _ (by norm_num)]

private theorem coreDirectionalEnergy_add_le
    (nu : Measure ℝ) (F G : ℝ → ℂ) (hF : Measurable F) (hG : Measurable G) :
    directionalEnergy nu (fun x => F x + G x) ≤
      2 * directionalEnergy nu F + 2 * directionalEnergy nu G := by
  let DF (s x : ℝ) : ℂ := F x - F (x - s)
  let DG (s x : ℝ) : ℂ := G x - G (x - s)
  have hDF (s : ℝ) : Measurable (DF s) :=
    hF.sub (hF.comp (measurable_id.sub_const s))
  have hDG (s : ℝ) : Measurable (DG s) :=
    hG.sub (hG.comp (measurable_id.sub_const s))
  have hDFmass : Measurable (fun s : ℝ => coreL2Mass (DF s)) := by
    have hm : Measurable (fun p : ℝ × ℝ => ‖DF p.1 p.2‖ₑ ^ 2) := by
      dsimp only [DF]
      fun_prop
    exact hm.lintegral_prod_right'
  have hslice (s : ℝ) :
      (∫⁻ x : ℝ, ‖(F x + G x) - (F (x - s) + G (x - s))‖ₑ ^ 2) ≤
        2 * coreL2Mass (DF s) + 2 * coreL2Mass (DG s) := by
    calc
      _ = coreL2Mass (fun x => DF s x + DG s x) := by
        apply lintegral_congr_ae
        exact Eventually.of_forall fun x => by
          dsimp only [DF, DG]
          rw [show (F x + G x) - (F (x - s) + G (x - s)) =
            (F x - F (x - s)) + (G x - G (x - s)) by ring]
      _ ≤ _ := coreL2Mass_add_le (DF s) (DG s) (hDF s) (hDG s)
  calc
    _ ≤ ∫⁻ s : ℝ, (2 * coreL2Mass (DF s) + 2 * coreL2Mass (DG s)) ∂nu :=
      lintegral_mono hslice
    _ = _ := by
      simp only [directionalEnergy, coreL2Mass]
      calc
        _ = (∫⁻ s : ℝ, 2 * coreL2Mass (DF s) ∂nu) +
            ∫⁻ s : ℝ, 2 * coreL2Mass (DG s) ∂nu :=
          lintegral_add_left' ((measurable_const.mul hDFmass).aemeasurable) _
        _ = _ := by
          rw [lintegral_const_mul' _ _ (by norm_num),
            lintegral_const_mul' _ _ (by norm_num)]
          simp only [coreL2Mass, DF, DG]

private theorem coreGraphSize_add_le
    (nu : Measure ℝ) (F G : ℝ → ℂ) (hF : Measurable F) (hG : Measurable G) :
    coreGraphSize nu (fun x => F x + G x) ≤
      2 * coreGraphSize nu F + 2 * coreGraphSize nu G := by
  calc
    _ ≤ (2 * coreL2Mass F + 2 * coreL2Mass G) +
        (2 * directionalEnergy nu F + 2 * directionalEnergy nu G) :=
      add_le_add (coreL2Mass_add_le F G hF hG)
        (coreDirectionalEnergy_add_le nu F G hF hG)
    _ = _ := by unfold coreGraphSize; ring

private theorem coreGraphSize_congr_ae
    (nu : Measure ℝ) {F G : ℝ → ℂ} (hFG : F =ᵐ[volume] G) :
    coreGraphSize nu F = coreGraphSize nu G := by
  have hm : coreL2Mass F = coreL2Mass G := by
    apply lintegral_congr_ae
    filter_upwards [hFG] with x hx
    rw [hx]
  exact congrArg₂ (fun u v : ℝ≥0∞ => u + v) hm (directionalEnergy_congr_ae nu hFG)

private theorem core_eighth_budget {ε : ℝ} (hε : 0 < ε) :
    (2 : ℝ≥0∞) * ENNReal.ofReal (ε / 8) +
      2 * ENNReal.ofReal (ε / 8) < ENNReal.ofReal ε := by
  calc
    _ = ENNReal.ofReal (2 * (ε / 8) + 2 * (ε / 8)) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity)]
      norm_num
    _ < _ := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)

/-- Direct smooth-core approximation of the original Ioc L2 carrier,
measured on its existing real-line zero extension and actual Gamma form.
Only the two original domain assumptions occur in the input. -/
private theorem actual_ioc_exists_smooth_compact_core_approximation
    (a : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a)))
    (henergy : directionalEnergy actualGammaExitMeasure
      (ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u) < (⊤ : ℝ≥0∞))
    (ε : ℝ) (hε : 0 < ε) :
    let F := ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u
    ∃ H : ℝ → ℂ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      tsupport H ⊆ Ioo (-a) a ∧
      coreL2Mass (fun x => H x - F x) +
        directionalEnergy actualGammaExitMeasure (fun x => H x - F x) <
          ENNReal.ofReal ε := by
  dsimp only
  let F := ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u
  obtain ⟨M, hM, hM₂, hMzero, hFM, _hmass, _hmassIoc, henergyEq⟩ :=
    actual_ioc_exists_measurable_zero_supported_energy_representative a u hu
  have hME : directionalEnergy actualGammaExitMeasure M < (⊤ : ℝ≥0∞) := by
    rw [← henergyEq]
    exact henergy
  have hMmass : coreL2Mass M < (⊤ : ℝ≥0∞) := by
    rw [coreL2Mass, squared_mass_eq_eLpNorm M hM₂.aestronglyMeasurable]
    exact ENNReal.pow_lt_top hM₂
  have hMsize : coreGraphSize actualGammaExitMeasure M < (⊤ : ℝ≥0∞) :=
    ENNReal.add_lt_top.mpr ⟨hMmass, hME⟩
  have hcutlim : Tendsto (fun δ => coreGraphSize actualGammaExitMeasure
      (fun x => (actualCutoffEta a δ x : ℂ) * M x - M x))
      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞)) :=
    (actual_gamma_interior_cutoff_form_approximation a M hM hM₂ hMzero hME).2
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[Ioi (0 : ℝ)] 0,
      coreGraphSize actualGammaExitMeasure
        (fun x => (actualCutoffEta a δ x : ℂ) * M x - M x) < ENNReal.ofReal (ε / 8) :=
    hcutlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 8)))
  have hpositive : ∀ᶠ δ : ℝ in 𝓝[Ioi (0 : ℝ)] 0, 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hδ, hsmall⟩ := (hpositive.and hsmall).exists
  let C : ℝ → ℂ := fun x => (actualCutoffEta a δ x : ℂ) * M x
  have hCm : Measurable C :=
    (Complex.ofRealCLM.continuous.comp (actualCutoffEta_contDiff a δ).continuous).measurable.mul hM
  have hC₂ : MemLp C 2 volume := by
    apply hM₂.of_le hCm.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      change ‖(actualCutoffEta a δ x : ℂ) * M x‖ ≤ ‖M x‖
      rw [norm_mul, Complex.norm_of_nonneg (actualCutoffEta_range a δ x).1]
      calc
        _ ≤ 1 * ‖M x‖ := mul_le_mul_of_nonneg_right
          (actualCutoffEta_range a δ x).2 (norm_nonneg _)
        _ = _ := one_mul _
  have hCcompact : HasCompactSupport C := actualCutoffEta_mul_hasCompactSupport hδ M
  have hCsupport : tsupport C ⊆ Icc (-a + δ) (a - δ) :=
    actualCutoffEta_mul_tsupport_subset_Icc hδ M
  have hCerrorfin :
      coreGraphSize actualGammaExitMeasure (fun x => C x - M x) < (⊤ : ℝ≥0∞) :=
    hsmall.trans ENNReal.ofReal_lt_top
  have hCeq : C = (fun x => (C x - M x) + M x) := by
    funext x
    ring
  have hCsize : coreGraphSize actualGammaExitMeasure C < (⊤ : ℝ≥0∞) := by
    calc
      _ = coreGraphSize actualGammaExitMeasure (fun x => (C x - M x) + M x) :=
        congrArg (coreGraphSize actualGammaExitMeasure) hCeq
      _ ≤ 2 * coreGraphSize actualGammaExitMeasure (fun x => C x - M x) +
          2 * coreGraphSize actualGammaExitMeasure M :=
        coreGraphSize_add_le actualGammaExitMeasure _ _ (hCm.sub hM) hM
      _ < (⊤ : ℝ≥0∞) := ENNReal.add_lt_top.mpr
        ⟨ENNReal.mul_lt_top (by norm_num) hCerrorfin,
          ENNReal.mul_lt_top (by norm_num) hMsize⟩
  have hCE : directionalEnergy actualGammaExitMeasure C < (⊤ : ℝ≥0∞) :=
    (ENNReal.add_lt_top.mp hCsize).2
  obtain ⟨H, hHsmooth, hHcompact, hHsupport, hHsmall⟩ :=
    exists_smooth_actual_gamma_approximation_of_inward_support
      C hCm hC₂ hCcompact hCE a δ hδ hCsupport (ε / 8) (by positivity)
  have hHM : coreGraphSize actualGammaExitMeasure (fun x => H x - M x) <
      ENNReal.ofReal ε := by
    have hsplit : (fun x => H x - M x) =
        (fun x => (H x - C x) + (C x - M x)) := by
      funext x
      ring
    calc
      _ = coreGraphSize actualGammaExitMeasure
          (fun x => (H x - C x) + (C x - M x)) :=
        congrArg (coreGraphSize actualGammaExitMeasure) hsplit
      _ ≤ 2 * coreGraphSize actualGammaExitMeasure (fun x => H x - C x) +
          2 * coreGraphSize actualGammaExitMeasure (fun x => C x - M x) :=
        coreGraphSize_add_le actualGammaExitMeasure _ _
          (hHsmooth.continuous.measurable.sub hCm) (hCm.sub hM)
      _ ≤ 2 * ENNReal.ofReal (ε / 8) + 2 * ENNReal.ofReal (ε / 8) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (by simpa [coreGraphSize] using hHsmall.le) (by norm_num))
          (mul_le_mul_of_nonneg_left hsmall.le (by norm_num))
      _ < ENNReal.ofReal ε := core_eighth_budget hε
  refine ⟨H, hHsmooth, hHcompact, hHsupport, ?_⟩
  change coreGraphSize actualGammaExitMeasure (fun x => H x - F x) < ENNReal.ofReal ε
  have herr : (fun x => H x - F x) =ᵐ[volume] (fun x => H x - M x) := by
    filter_upwards [hFM] with x hx
    dsimp only [F]
    rw [hx]
  rw [coreGraphSize_congr_ae actualGammaExitMeasure herr]
  exact hHM

/-- The physical error in the whole-line zero-extension convention is
literally the original Ioc L2 error once H has support in the open window. -/
private theorem coreL2Mass_error_eq_original_ioc
    (a : ℝ) (u H : ℝ → ℂ) (hHsupport : tsupport H ⊆ Ioo (-a) a) :
    coreL2Mass (fun x => H x -
      ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u x) =
        ∫⁻ x in Ioc (-a) a, ‖H x - u x‖ₑ ^ 2 := by
  have hend : -a + 2 * a = a := by ring
  calc
    _ = ∫⁻ x : ℝ, (Ioc (-a) a).indicator (fun y => ‖H y - u y‖ₑ ^ 2) x := by
      apply lintegral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : x ∈ Ioc (-a) a
        · simp [ActualGammaDomainPassageDraft.zeroExtension, hend, hx]
        · have hHzero : H x = 0 := by
            by_contra h
            have hi := hHsupport (subset_tsupport H h)
            exact hx ⟨hi.1, hi.2.le⟩
          simp [ActualGammaDomainPassageDraft.zeroExtension, hend, hx, hHzero]
    _ = _ := lintegral_indicator measurableSet_Ioc _

/-- The same smooth-core theorem with its physical error expressed on the
original Ioc carrier, and its actual Gamma energy on the same zero extension. -/
private theorem actual_ioc_exists_smooth_compact_core_approximation_on_source
    (a : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a)))
    (henergy : directionalEnergy actualGammaExitMeasure
      (ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u) < (⊤ : ℝ≥0∞))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℝ → ℂ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      tsupport H ⊆ Ioo (-a) a ∧
      (∫⁻ x in Ioc (-a) a, ‖H x - u x‖ₑ ^ 2) +
        directionalEnergy actualGammaExitMeasure
          (fun x => H x - ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u x) <
            ENNReal.ofReal ε := by
  obtain ⟨H, hHs, hHc, hHsupport, herror⟩ :=
    actual_ioc_exists_smooth_compact_core_approximation a u hu henergy ε hε
  refine ⟨H, hHs, hHc, hHsupport, ?_⟩
  rw [← coreL2Mass_error_eq_original_ioc a u H hHsupport]
  exact herror

end ActualGammaCompactCoreDraft20261018

/-
STATIC AE-EVEN WEIL-TEST CORE BRIDGE, Mathlib v4.35 adaptation, 2026-10-18.
UNCOMPILED. Source inspection only; no elaboration or kernel acceptance.

Append in the SAME source unit after the frozen spectral-Ioc-v2 assembly
(or its host-repaired version preserving the consumed names and statements).
Hoist the imports listed in source-api-notes.md to the TOP of that unit.
The canonical WeilTestFunction is the existing D5.S3.Weil.TestFunctions bundle.
No owner body, zero extension, energy measure or test bundle is repeated.

The only extra domain hypothesis is AE evenness of the ORIGINAL zero extension.
The original u need not be continuous, smooth or pointwise even. A measurable
representative is used only inside the proof. At each FIXED scale s, reflection
preserves jump energy by the volume substitution x -> s-x; the outer measure
nu is untouched. Averaging therefore contracts L2 mass plus actual energy.
The output is exactly even and supported in the same original open window.

All 18 original declarations are retained with their full bodies. The original
Ioc endpoint and its hypotheses are unchanged. This fragment and its frozen
spectral-Ioc prerequisite are UNCOMPILED; no acceptance transfers from earlier
constituents. This source preparation establishes no signed Weil positivity,
full Weil criterion or RH result.
-/

noncomputable section

namespace ActualGammaCompactCoreDraft20261018

open MeasureTheory Set Filter
open scoped ENNReal Topology

private def coreReflect (F : ℝ → ℂ) : ℝ → ℂ := fun x => F (-x)

private def coreEvenPart (F : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (1 / 2 : ℂ) * (F x + coreReflect F x)

private theorem coreL2Mass_reflect (F : ℝ → ℂ) :
    coreL2Mass (coreReflect F) = coreL2Mass F := by
  change (∫⁻ x : ℝ, ‖F (-x)‖ₑ ^ 2 ∂volume) =
    ∫⁻ x : ℝ, ‖F x‖ₑ ^ 2 ∂volume
  exact lintegral_neg_eq_self (μ := (volume : Measure ℝ))
    (fun x : ℝ => ‖F x‖ₑ ^ 2)

/-- The scale measure is unchanged: the inner substitution is x -> s-x,
not s -> -s. No symmetry assumption on nu is needed. -/
private theorem coreDirectionalEnergy_reflect (nu : Measure ℝ) (F : ℝ → ℂ) :
    directionalEnergy nu (coreReflect F) = directionalEnergy nu F := by
  unfold directionalEnergy
  apply lintegral_congr_ae
  exact Eventually.of_forall fun s => by
    calc
      (∫⁻ x : ℝ, ‖coreReflect F x - coreReflect F (x - s)‖ₑ ^ 2) =
          ∫⁻ x : ℝ, ‖F ((s - x) - s) - F (s - x)‖ₑ ^ 2 := by
        apply lintegral_congr_ae
        exact Eventually.of_forall fun x => by
          have h₁ : (s - x) - s = -x := by ring
          have h₂ : -(x - s) = s - x := by ring
          simp only [coreReflect, h₁, h₂]
      _ = ∫⁻ x : ℝ, ‖F (x - s) - F x‖ₑ ^ 2 :=
        lintegral_sub_left_eq_self (μ := (volume : Measure ℝ))
          (fun x : ℝ => ‖F (x - s) - F x‖ₑ ^ 2) s
      _ = ∫⁻ x : ℝ, ‖F x - F (x - s)‖ₑ ^ 2 := by
        apply lintegral_congr_ae
        exact Eventually.of_forall fun x => by
          change ‖F (x - s) - F x‖ₑ ^ 2 = ‖F x - F (x - s)‖ₑ ^ 2
          rw [show F (x - s) - F x = -(F x - F (x - s)) by ring, enorm_neg]

private theorem coreGraphSize_reflect (nu : Measure ℝ) (F : ℝ → ℂ) :
    coreGraphSize nu (coreReflect F) = coreGraphSize nu F := by
  simp only [coreGraphSize, coreL2Mass_reflect, coreDirectionalEnergy_reflect]

private theorem coreL2Mass_const_mul (c : ℂ) (F : ℝ → ℂ) :
    coreL2Mass (fun x => c * F x) = ‖c‖ₑ ^ 2 * coreL2Mass F := by
  unfold coreL2Mass
  simp_rw [enorm_mul, mul_pow]
  exact lintegral_const_mul' (μ := (volume : Measure ℝ))
    (‖c‖ₑ ^ 2) (fun x : ℝ => ‖F x‖ₑ ^ 2)
    (ENNReal.pow_ne_top (enorm_ne_top (x := c)))

private theorem coreDirectionalEnergy_const_mul
    (nu : Measure ℝ) (c : ℂ) (F : ℝ → ℂ) :
    directionalEnergy nu (fun x => c * F x) =
      ‖c‖ₑ ^ 2 * directionalEnergy nu F := by
  have hc : ‖c‖ₑ ^ 2 ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.pow_ne_top (enorm_ne_top (x := c))
  unfold directionalEnergy
  simp_rw [← mul_sub, enorm_mul, mul_pow,
    lintegral_const_mul' (μ := (volume : Measure ℝ)) (‖c‖ₑ ^ 2) _ hc]
  exact lintegral_const_mul' (μ := nu) (‖c‖ₑ ^ 2) _ hc

private theorem coreGraphSize_const_mul (nu : Measure ℝ) (c : ℂ) (F : ℝ → ℂ) :
    coreGraphSize nu (fun x => c * F x) = ‖c‖ₑ ^ 2 * coreGraphSize nu F := by
  simp only [coreGraphSize, coreL2Mass_const_mul,
    coreDirectionalEnergy_const_mul, mul_add]

/-- Orthogonal averaging with reflection is contractive for the actual
quadratic graph size. The statement also permits infinite graph size. -/
private theorem coreGraphSize_evenPart_le
    (nu : Measure ℝ) (F : ℝ → ℂ) (hF : Measurable F) :
    coreGraphSize nu (coreEvenPart F) ≤ coreGraphSize nu F := by
  have hRF : Measurable (coreReflect F) := hF.comp measurable_neg
  have hnorm : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
    rw [norm_div]
    norm_num
  have hq : ‖(1 / 2 : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (1 / 4 : ℝ) := by
    calc
      ‖(1 / 2 : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (1 / 2 : ℝ) ^ 2 := by
        rw [← ofReal_norm, hnorm]
      _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ 2) :=
        (ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2) 2).symm
      _ = ENNReal.ofReal (1 / 4 : ℝ) := congrArg ENNReal.ofReal (by norm_num)
  have hcoeff : ENNReal.ofReal (1 / 4 : ℝ) * 2 +
      ENNReal.ofReal (1 / 4 : ℝ) * 2 = (1 : ℝ≥0∞) := by
    have hreal : (1 / 4 : ℝ) * 2 + (1 / 4 : ℝ) * 2 = 1 := by norm_num
    have hnonneg : (0 : ℝ) ≤ (1 / 4 : ℝ) * 2 := by norm_num
    simpa only [ENNReal.ofReal_add hnonneg hnonneg,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using congrArg ENNReal.ofReal hreal
  calc
    coreGraphSize nu (coreEvenPart F) = ENNReal.ofReal (1 / 4 : ℝ) *
        coreGraphSize nu (fun x => F x + coreReflect F x) := by
      change coreGraphSize nu (fun x => (1 / 2 : ℂ) * (F x + coreReflect F x)) = _
      rw [coreGraphSize_const_mul, hq]
    _ ≤ ENNReal.ofReal (1 / 4 : ℝ) *
        (2 * coreGraphSize nu F + 2 * coreGraphSize nu (coreReflect F)) :=
      mul_le_mul_of_nonneg_left (coreGraphSize_add_le nu F (coreReflect F) hF hRF)
        (by positivity)
    _ = (ENNReal.ofReal (1 / 4 : ℝ) * 2 +
        ENNReal.ofReal (1 / 4 : ℝ) * 2) * coreGraphSize nu F := by
      rw [coreGraphSize_reflect]
      ring
    _ = coreGraphSize nu F := by rw [hcoeff, one_mul]

private theorem coreEvenPart_contDiff {H : ℝ → ℂ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (coreEvenPart H) := by
  change ContDiff ℝ ∞ (fun x : ℝ => (1 / 2 : ℂ) * (H x + H (-x)))
  exact contDiff_const.mul (hH.add (hH.comp contDiff_neg))

private theorem coreEvenPart_hasCompactSupport {H : ℝ → ℂ}
    (hH : HasCompactSupport H) : HasCompactSupport (coreEvenPart H) := by
  have hneg : HasCompactSupport (coreReflect H) := by
    change HasCompactSupport (H ∘ (Homeomorph.neg ℝ))
    exact hH.comp_homeomorph (Homeomorph.neg ℝ)
  change HasCompactSupport
    ((fun _ : ℝ => (1 / 2 : ℂ)) * (H + coreReflect H))
  exact (hH.add hneg).mul_left (f := fun _ : ℝ => (1 / 2 : ℂ))

private theorem coreEvenPart_even (H : ℝ → ℂ) (x : ℝ) :
    coreEvenPart H (-x) = coreEvenPart H x := by
  simp only [coreEvenPart, coreReflect, neg_neg, add_comm]

private theorem coreEvenPart_tsupport_subset {H : ℝ → ℂ} {a : ℝ}
    (hH : tsupport H ⊆ Ioo (-a) a) :
    tsupport (coreEvenPart H) ⊆ Ioo (-a) a := by
  have hneg : tsupport (coreReflect H) ⊆ Ioo (-a) a := by
    intro x hx
    have hpre : tsupport (coreReflect H) =
        (Homeomorph.neg ℝ) ⁻¹' tsupport H := by
      change tsupport (H ∘ (Homeomorph.neg ℝ)) =
        (Homeomorph.neg ℝ) ⁻¹' tsupport H
      exact tsupport_comp_eq_preimage H (Homeomorph.neg ℝ)
    rw [hpre] at hx
    change -x ∈ tsupport H at hx
    have hnx : -x ∈ Ioo (-a) a := hH hx
    exact ⟨by linarith [hnx.2], by linarith [hnx.1]⟩
  have hsum : tsupport (fun x : ℝ => H x + coreReflect H x) ⊆ Ioo (-a) a :=
    (tsupport_add H (coreReflect H)).trans (union_subset hH hneg)
  change tsupport (fun x : ℝ => (1 / 2 : ℂ) * (H x + coreReflect H x)) ⊆ Ioo (-a) a
  exact (tsupport_mul_subset_right
    (f := fun _ : ℝ => (1 / 2 : ℂ))
    (g := fun x : ℝ => H x + coreReflect H x)).trans hsum

/-- Canonical bundle, using its existing evenness field rather than a
parallel notion of an admissible test. -/
private def coreEvenWeilTest (H : ℝ → ℂ)
    (hHs : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H) :
    D5.S3.Weil.TestFunctions.WeilTestFunction where
  toFun := coreEvenPart H
  contDiff' := coreEvenPart_contDiff hHs
  hasCompactSupport' := coreEvenPart_hasCompactSupport hHc
  even' := coreEvenPart_even H

/-- AE evenness suffices. No pointwise-even representative is imposed on F. -/
private theorem coreGraphSize_evenPart_error_le
    (nu : Measure ℝ) (F H : ℝ → ℂ)
    (hF : Measurable F) (hH : Measurable H)
    (heven : ∀ᵐ x : ℝ ∂volume, F (-x) = F x) :
    coreGraphSize nu (fun x => coreEvenPart H x - F x) ≤
      coreGraphSize nu (fun x => H x - F x) := by
  have herr : (fun x => coreEvenPart H x - F x) =ᵐ[volume]
      coreEvenPart (fun x => H x - F x) := by
    filter_upwards [heven] with x hx
    dsimp only [coreEvenPart, coreReflect]
    rw [hx]
    ring
  rw [coreGraphSize_congr_ae nu herr]
  exact coreGraphSize_evenPart_le nu _ (hH.sub hF)

private theorem core_ae_even_transfer
    {F M : ℝ → ℂ} (hFM : F =ᵐ[volume] M)
    (heven : ∀ᵐ x : ℝ ∂volume, F (-x) = F x) :
    ∀ᵐ x : ℝ ∂volume, M (-x) = M x := by
  have hneg : (fun x : ℝ => F (-x)) =ᵐ[volume] (fun x : ℝ => M (-x)) := by
    simpa only [Function.comp_def] using
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp hFM
  filter_upwards [hFM, hneg, heven] with x hx hnx hex
  exact hnx.symm.trans (hex.trans hx)

/-- Every original Ioc L2 carrier with finite actual Gamma energy and AE-even
zero extension is approximated in that same graph size by canonical bundled
Weil tests, compactly supported strictly inside its original open window. -/
private theorem actual_ioc_exists_weil_test_core_approximation
    (a : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a)))
    (henergy : directionalEnergy actualGammaExitMeasure
      (ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u) < (⊤ : ℝ≥0∞))
    (heven : ∀ᵐ x : ℝ ∂volume,
      ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u (-x) =
        ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u x)
    (ε : ℝ) (hε : 0 < ε) :
    let F := ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u
    ∃ g : D5.S3.Weil.TestFunctions.WeilTestFunction,
      tsupport (g : ℝ → ℂ) ⊆ Ioo (-a) a ∧
      coreL2Mass (fun x => g x - F x) +
        directionalEnergy actualGammaExitMeasure (fun x => g x - F x) <
          ENNReal.ofReal ε := by
  dsimp only
  let F := ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u
  obtain ⟨H, hHs, hHc, hHsupport, hHerror⟩ :=
    actual_ioc_exists_smooth_compact_core_approximation a u hu henergy ε hε
  obtain ⟨M, hM, _hM₂, _hMzero, hFM, _hmass, _hmassIoc, _henergyEq⟩ :=
    actual_ioc_exists_measurable_zero_supported_energy_representative a u hu
  have hMeven : ∀ᵐ x : ℝ ∂volume, M (-x) = M x :=
    core_ae_even_transfer hFM heven
  have hHFM : (fun x => H x - F x) =ᵐ[volume] (fun x => H x - M x) := by
    filter_upwards [hFM] with x hx
    dsimp only [F]
    rw [hx]
  have hJFM : (fun x => coreEvenPart H x - F x) =ᵐ[volume]
      (fun x => coreEvenPart H x - M x) := by
    filter_upwards [hFM] with x hx
    dsimp only [F]
    rw [hx]
  refine ⟨coreEvenWeilTest H hHs hHc, coreEvenPart_tsupport_subset hHsupport, ?_⟩
  change coreGraphSize actualGammaExitMeasure (fun x => coreEvenPart H x - F x) <
    ENNReal.ofReal ε
  calc
    _ = coreGraphSize actualGammaExitMeasure (fun x => coreEvenPart H x - M x) :=
      coreGraphSize_congr_ae actualGammaExitMeasure hJFM
    _ ≤ coreGraphSize actualGammaExitMeasure (fun x => H x - M x) :=
      coreGraphSize_evenPart_error_le actualGammaExitMeasure M H hM
        hHs.continuous.measurable hMeven
    _ = coreGraphSize actualGammaExitMeasure (fun x => H x - F x) :=
      (coreGraphSize_congr_ae actualGammaExitMeasure hHFM).symm
    _ < ENNReal.ofReal ε := hHerror

/-- The same canonical bundled conclusion with the physical L2 error on the
original Ioc carrier. Gamma energy keeps the existing zero extension. -/
private theorem actual_ioc_exists_weil_test_core_approximation_on_source
    (a : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a)))
    (henergy : directionalEnergy actualGammaExitMeasure
      (ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u) < (⊤ : ℝ≥0∞))
    (heven : ∀ᵐ x : ℝ ∂volume,
      ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u (-x) =
        ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : D5.S3.Weil.TestFunctions.WeilTestFunction,
      tsupport (g : ℝ → ℂ) ⊆ Ioo (-a) a ∧
      (∫⁻ x in Ioc (-a) a, ‖g x - u x‖ₑ ^ 2) +
        directionalEnergy actualGammaExitMeasure
          (fun x => g x - ActualGammaDomainPassageDraft.zeroExtension (2 * a) (-a) u x) <
            ENNReal.ofReal ε := by
  obtain ⟨g, hgsupport, hgerror⟩ :=
    actual_ioc_exists_weil_test_core_approximation a u hu henergy heven ε hε
  refine ⟨g, hgsupport, ?_⟩
  rw [← coreL2Mass_error_eq_original_ioc a u (g : ℝ → ℂ) hgsupport]
  exact hgerror

end ActualGammaCompactCoreDraft20261018
