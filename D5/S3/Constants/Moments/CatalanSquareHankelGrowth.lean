/- GID: D5/S3/Constants/Moments/CatalanSquareHankelGrowth
   generality: I
   mirror-B: D5/B/S3/Constants/Moments/CatalanSquareHankelGrowth
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Probability.Distributions.Beta]
   utility: none
   digest: Squared-Catalan product Grams are positive with Chebyshev upper bounds. -/

import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Probability.Distributions.Beta
import Mathlib.Tactic
import D5.S3.Arith.GoldenResource.IntegerHadamard

/- Library search (2026-09-23): the repository and pinned Mathlib contain no Catalan
   moment theorem, Andreief identity, or exact squared-Catalan Hankel result. Pinned
   Mathlib supplies `betaMeasure`, product integration, the Catalan closed formula,
   and the beta/gamma identities used below. Its Chebyshev orthogonality file marks
   second-kind orthogonality as TODO. Loogle returned only the beta measure and its
   probability instance; unauthenticated GitHub code search was gated, while the
   queried LeanSearch and Reservoir endpoints were unavailable. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction

namespace D5.S3.Constants.Moments.CatalanSquareHankelGrowth

/-- The beta law whose dilation by four is the Catalan moment law. -/
def catalanBetaMeasure : Measure Real :=
  betaMeasure (1 / 2 : Real) (3 / 2 : Real)

/-- The `m`-th moment after dilating the beta variable by four. -/
def catalanMoment (m : Nat) : Real :=
  ∫ x, (4 * x) ^ m ∂catalanBetaMeasure

/-- The `m`-th moment of the product of two independent dilated beta variables. -/
def catalanProductMoment (m : Nat) : Real :=
  ∫ p : Real × Real, ((4 * p.1) * (4 * p.2)) ^ m
    ∂(catalanBetaMeasure.prod catalanBetaMeasure)

/-- The exact squared-Catalan Hankel matrix with an arbitrary shift. -/
def catalanSquareHankelMatrix (n r : Nat) : Matrix (Fin n) (Fin n) Real :=
  fun i j => (catalan (i.1 + j.1 + r) : Real) ^ 2

/-- The exact determinant convention, including determinant one at size zero. -/
def catalanSquareHankelDet (r n : Nat) : Real :=
  Matrix.det (catalanSquareHankelMatrix n r)

private lemma beta_moment_formula (m : Nat) :
    catalanMoment m = (catalan m : Real) := by
  rw [catalanMoment, catalanBetaMeasure, betaMeasure]
  change (∫ x : Real, (4 * x) ^ m
      ∂volume.withDensity (fun x => ENNReal.ofReal (betaPDFReal (1 / 2) (3 / 2) x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_betaPDFReal _ _).ennreal_ofReal (by simp)]
  simp only [smul_eq_mul]
  have hnonneg (x : Real) : 0 ≤ betaPDFReal (1 / 2) (3 / 2) x := by
    by_cases hx : x ∈ Set.Ioo (0 : Real) 1
    · exact (betaPDFReal_pos hx.1 hx.2 (by norm_num) (by norm_num)).le
    · rw [betaPDFReal, if_neg (by simpa only [Set.mem_Ioo] using hx)]
  simp_rw [ENNReal.toReal_ofReal (hnonneg _)]
  have hsupport : (fun x : Real => betaPDFReal (1 / 2) (3 / 2) x * (4 * x) ^ m) =
      Set.indicator (Set.Ioo (0 : Real) 1)
        (fun x => betaPDFReal (1 / 2) (3 / 2) x * (4 * x) ^ m) := by
    funext x
    by_cases hx : x ∈ Set.Ioo (0 : Real) 1
    · simp [Set.indicator_of_mem hx]
    · rw [betaPDFReal, if_neg (by simpa only [Set.mem_Ioo] using hx)]
      simp [Set.indicator, hx]
  rw [hsupport, integral_indicator measurableSet_Ioo]
  rw [show (∫ x in Set.Ioo (0 : Real) 1,
      betaPDFReal (1 / 2) (3 / 2) x * (4 * x) ^ m) =
      ∫ x in Set.Ioo (0 : Real) 1,
        (4 ^ m / beta (1 / 2) (3 / 2)) *
          (x ^ ((m : Real) + 1 / 2 - 1) *
            (1 - x) ^ ((3 : Real) / 2 - 1)) by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    change (if 0 < x ∧ x < 1 then
      (1 / beta (1 / 2) (3 / 2)) * x ^ (1 / 2 - 1) *
        (1 - x) ^ (3 / 2 - 1) else 0) * (4 * x) ^ m = _
    rw [if_pos (by simpa only [Set.mem_Ioo] using hx)]
    rw [mul_pow, show x ^ m = x ^ (m : Real) by rw [Real.rpow_natCast]]
    have hxcombine : x ^ ((1 : Real) / 2 - 1) * x ^ (m : Real) =
        x ^ ((m : Real) + 1 / 2 - 1) := by
      calc
        x ^ ((1 : Real) / 2 - 1) * x ^ (m : Real) =
            x ^ (((1 : Real) / 2 - 1) + (m : Real)) :=
          (Real.rpow_add hx.1 ((1 : Real) / 2 - 1) (m : Real)).symm
        _ = x ^ ((m : Real) + 1 / 2 - 1) := by congr 1 <;> ring
    calc
      1 / beta (1 / 2) (3 / 2) * x ^ ((1 : Real) / 2 - 1) *
            (1 - x) ^ ((3 : Real) / 2 - 1) * (4 ^ m * x ^ (m : Real)) =
          (4 ^ m / beta (1 / 2) (3 / 2)) *
            ((x ^ ((1 : Real) / 2 - 1) * x ^ (m : Real)) *
              (1 - x) ^ ((3 : Real) / 2 - 1)) := by ring
      _ = (4 ^ m / beta (1 / 2) (3 / 2)) *
          (x ^ ((m : Real) + 1 / 2 - 1) *
            (1 - x) ^ ((3 : Real) / 2 - 1)) := by rw [hxcombine]]
  rw [integral_const_mul]
  have beta_integral_real (a b : Real) (ha : 0 < a) (hb : 0 < b) :
      ∫ x in Set.Ioo (0 : Real) 1, x ^ (a - 1) * (1 - x) ^ (b - 1) = beta a b := by
    rw [beta_eq_betaIntegralReal a b ha hb, Complex.betaIntegral]
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Ioc_eq_integral_Ioo,
      ← RCLike.re_to_complex, ← integral_re]
    · refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
      rcases hx with ⟨hx0, hx1⟩
      norm_cast
      rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow, RCLike.re_to_complex,
        Complex.re_mul_ofReal, Complex.ofReal_re]
      · linarith
      · exact hx0.le
    · convert! Complex.betaIntegral_convergent
        (u := a) (v := b) (by simpa) (by simpa)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num), IntegrableOn]
  have hbeta := beta_integral_real ((m : Real) + 1 / 2) (3 / 2)
    (by positivity) (by norm_num)
  have hratio :
      4 ^ m * beta ((m : Real) + 1 / 2) (3 / 2) / beta (1 / 2) (3 / 2) =
        (catalan m : Real) := by
    have hhalf : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
    have hthree : Real.Gamma (3 / 2) = (1 / 2) * Real.sqrt Real.pi := by
      rw [show (3 / 2 : Real) = 1 / 2 + 1 by ring,
        Real.Gamma_add_one (by norm_num), hhalf]
    have hmTwo : Real.Gamma ((m : Real) + 2) = ((m + 1).factorial : Real) := by
      convert Real.Gamma_nat_eq_factorial (m + 1) using 1 <;> push_cast <;> ring_nf
    have htwo : Real.Gamma (2 : Real) = 1 := by norm_num [Real.Gamma_add_one]
    rw [beta, beta, Real.Gamma_nat_add_half, hthree]
    rw [show ((m : Real) + 1 / 2) + 3 / 2 = (m : Real) + 2 by ring, hmTwo]
    rw [show (1 / 2 : Real) + 3 / 2 = 2 by ring, htwo, hhalf]
    have hsqrt : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
    cases m with
    | zero => norm_num [catalan_zero, hsqrt]
    | succ m =>
        have hcat := succ_mul_catalan_eq_centralBinom (m + 1)
        rw [Nat.centralBinom] at hcat
        have hchoose := Nat.choose_mul_factorial_mul_factorial
          (by omega : m + 1 ≤ 2 * (m + 1))
        rw [show 2 * (m + 1) - (m + 1) = m + 1 by omega] at hchoose
        have hfac := Nat.factorial_eq_mul_doubleFactorial (2 * (m + 1) - 1)
        rw [show 2 * (m + 1) - 1 + 1 = 2 * (m + 1) by omega,
          Nat.doubleFactorial_two_mul] at hfac
        have hsucc : (m + 2).factorial = (m + 2) * (m + 1).factorial := by
          rw [show m + 2 = (m + 1) + 1 by omega, Nat.factorial_succ]
        have hpow : (4 : Real) ^ (m + 1) =
            2 ^ (m + 1) * 2 ^ (m + 1) := by
          rw [show (4 : Real) = 2 * 2 by norm_num, mul_pow]
        have hcatReal : ((m + 2 : Nat) : Real) * (catalan (m + 1) : Real) =
            ((2 * (m + 1)).choose (m + 1) : Real) := by
          exact_mod_cast hcat
        have hchooseReal : ((2 * (m + 1)).choose (m + 1) : Real) *
            ((m + 1).factorial : Real) * ((m + 1).factorial : Real) =
            ((2 * (m + 1)).factorial : Real) := by
          exact_mod_cast hchoose
        have hfacReal : ((2 * (m + 1)).factorial : Real) =
            2 ^ (m + 1) * ((m + 1).factorial : Real) *
              ((2 * (m + 1) - 1).doubleFactorial : Real) := by
          exact_mod_cast hfac
        have hsuccReal : ((m + 2).factorial : Real) =
            ((m + 2 : Nat) : Real) * ((m + 1).factorial : Real) := by
          exact_mod_cast hsucc
        rw [hpow]
        field_simp [hsqrt]
        have hfactorialpos : (0 : Real) < (m + 1).factorial := by positivity
        have hmul : ((m + 1).factorial : Real) *
            ((m + 2).factorial * catalan (m + 1)) =
            ((m + 1).factorial : Real) *
              (2 ^ (m + 1) * (2 * (m + 1) - 1).doubleFactorial) := by
          calc
            ((m + 1).factorial : Real) *
                  ((m + 2).factorial * catalan (m + 1)) =
                ((2 * (m + 1)).choose (m + 1) : Real) *
                  (m + 1).factorial * (m + 1).factorial := by
              rw [hsuccReal, ← hcatReal]
              ring
            _ = ((2 * (m + 1)).factorial : Real) := hchooseReal
            _ = 2 ^ (m + 1) * (m + 1).factorial *
                (2 * (m + 1) - 1).doubleFactorial := hfacReal
            _ = ((m + 1).factorial : Real) *
                (2 ^ (m + 1) * (2 * (m + 1) - 1).doubleFactorial) := by ring
        have htarget : ((m + 2).factorial : Real) * catalan (m + 1) =
            2 ^ (m + 1) * (2 * (m + 1) - 1).doubleFactorial :=
          mul_left_cancel₀ (ne_of_gt hfactorialpos) hmul
        exact htarget.symm
  calc
    4 ^ m / beta (1 / 2) (3 / 2) *
          ∫ a in Set.Ioo (0 : Real) 1,
            a ^ ((m : Real) + 1 / 2 - 1) * (1 - a) ^ ((3 : Real) / 2 - 1) =
        4 ^ m / beta (1 / 2) (3 / 2) * beta ((m : Real) + 1 / 2) (3 / 2) :=
      congrArg (fun z : Real => 4 ^ m / beta (1 / 2) (3 / 2) * z) hbeta
    _ = 4 ^ m * beta ((m : Real) + 1 / 2) (3 / 2) /
        beta (1 / 2) (3 / 2) := by ring
    _ = (catalan m : Real) := hratio

/- Preregistered source-specific bridge: the scaled beta moment is literally Catalan;
   independence squares it, and every target-matrix entry is that product moment. -/
private lemma catalan_moment_product_and_matrix_entry (m n r : Nat) (i j : Fin n) :
    catalanMoment m = (catalan m : Real) ∧
    catalanProductMoment m = (catalan m : Real) ^ 2 ∧
    catalanSquareHankelMatrix n r i j = catalanProductMoment (i.1 + j.1 + r) := by
  have hscalar (k : Nat) : catalanMoment k = (catalan k : Real) :=
    beta_moment_formula k
  have hproduct (k : Nat) : catalanProductMoment k = (catalan k : Real) ^ 2 := by
    letI : IsProbabilityMeasure catalanBetaMeasure := by
      dsimp [catalanBetaMeasure]
      exact isProbabilityMeasureBeta (by norm_num) (by norm_num)
    calc
      catalanProductMoment k =
          (∫ x : Real, (4 * x) ^ k ∂catalanBetaMeasure) *
            ∫ y : Real, (4 * y) ^ k ∂catalanBetaMeasure := by
        simpa only [catalanProductMoment, mul_pow] using
          (integral_prod_mul (fun x : Real => (4 * x) ^ k)
            (fun y : Real => (4 * y) ^ k))
      _ = (catalan k : Real) ^ 2 := by rw [← catalanMoment, hscalar]; ring
  exact ⟨hscalar m, hproduct m, by
    simp only [catalanSquareHankelMatrix]
    rw [hproduct]⟩

private local instance : IsProbabilityMeasure catalanBetaMeasure := by
  dsimp [catalanBetaMeasure]
  exact isProbabilityMeasureBeta (by norm_num) (by norm_num)

private def clippedCatalanCoordinate : Real →ᵇ Real :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : Real => 4 * (Set.projIcc 0 1 zero_le_one x : Real))
    (continuous_const.mul (continuous_subtype_val.comp continuous_projIcc)) 4 (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact mul_le_of_le_one_right (by norm_num) (Set.projIcc 0 1 zero_le_one x).2.2
      · exact mul_nonneg (by norm_num) (Set.projIcc 0 1 zero_le_one x).2.1)

private def shiftOneGramVector (i : Nat) : Real →ᵇ Real :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : Real => Real.sqrt (clippedCatalanCoordinate x) * clippedCatalanCoordinate x ^ i)
    ((Real.continuous_sqrt.comp clippedCatalanCoordinate.continuous).mul
      (clippedCatalanCoordinate.continuous.pow i))
    (2 * 4 ^ i) (fun x => by
      have hx0 : 0 ≤ clippedCatalanCoordinate x := by
        simp only [clippedCatalanCoordinate, BoundedContinuousFunction.coe_ofNormedAddCommGroup]
        exact mul_nonneg (by norm_num) (Set.projIcc 0 1 zero_le_one x).2.1
      have hx4 : clippedCatalanCoordinate x ≤ 4 := by
        simp only [clippedCatalanCoordinate, BoundedContinuousFunction.coe_ofNormedAddCommGroup]
        exact mul_le_of_le_one_right (by norm_num) (Set.projIcc 0 1 zero_le_one x).2.2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hx0 _))]
      exact mul_le_mul (Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith⟩)
        (pow_le_pow_left₀ hx0 hx4 i) (pow_nonneg hx0 _) (by norm_num))

private def shiftTwoGramVector (i : Nat) : Real →ᵇ Real :=
  clippedCatalanCoordinate ^ (i + 1)

private def shiftOneLpVector (i : Nat) : Lp Real 2 catalanBetaMeasure :=
  BoundedContinuousFunction.toLp 2 catalanBetaMeasure Real (shiftOneGramVector i)

private def shiftTwoLpVector (i : Nat) : Lp Real 2 catalanBetaMeasure :=
  BoundedContinuousFunction.toLp 2 catalanBetaMeasure Real (shiftTwoGramVector i)

private lemma inner_shiftOneLpVector (i j : Nat) :
    inner Real (shiftOneLpVector i) (shiftOneLpVector j) =
      (catalan (i + j + 1) : Real) := by
  simp only [shiftOneLpVector]
  rw [BoundedContinuousFunction.inner_toLp]
  rw [← beta_moment_formula (i + j + 1), catalanMoment]
  have hsupport : ∀ᵐ x ∂catalanBetaMeasure, x ∈ Set.Ioo (0 : Real) 1 := by
    rw [catalanBetaMeasure, betaMeasure]
    refine (ae_withDensity_iff
      (measurable_betaPDFReal (1 / 2) (3 / 2)).ennreal_ofReal).2 ?_
    filter_upwards with x hx
    contrapose! hx
    rw [betaPDFReal, if_neg (by simpa only [Set.mem_Ioo] using hx)]
    simp
  apply integral_congr_ae
  filter_upwards [hsupport] with x hx
  have hclip : clippedCatalanCoordinate x = 4 * x := by
    simp only [clippedCatalanCoordinate,
      BoundedContinuousFunction.coe_ofNormedAddCommGroup]
    rw [Set.projIcc_of_mem zero_le_one ⟨hx.1.le, hx.2.le⟩]
  rw [show shiftOneGramVector j x =
      Real.sqrt (4 * x) * (4 * x) ^ j by simp [shiftOneGramVector,
        hclip],
    show shiftOneGramVector i x =
      Real.sqrt (4 * x) * (4 * x) ^ i by simp [shiftOneGramVector,
        hclip]]
  simp only [map_mul, conj_trivial]
  calc
    Real.sqrt (4 * x) * (4 * x) ^ j *
          (Real.sqrt (4 * x) * (4 * x) ^ i) =
        (Real.sqrt (4 * x) * Real.sqrt (4 * x)) *
          ((4 * x) ^ i * (4 * x) ^ j) := by ring
    _ = (4 * x) * (4 * x) ^ (i + j) := by
      rw [Real.mul_self_sqrt (mul_nonneg (by norm_num) hx.1.le), pow_add]
    _ = (4 * x) ^ (i + j + 1) := by rw [pow_succ']

private lemma inner_shiftTwoLpVector (i j : Nat) :
    inner Real (shiftTwoLpVector i) (shiftTwoLpVector j) =
      (catalan (i + j + 2) : Real) := by
  simp only [shiftTwoLpVector]
  rw [BoundedContinuousFunction.inner_toLp]
  rw [← beta_moment_formula (i + j + 2), catalanMoment]
  have hsupport : ∀ᵐ x ∂catalanBetaMeasure, x ∈ Set.Ioo (0 : Real) 1 := by
    rw [catalanBetaMeasure, betaMeasure]
    refine (ae_withDensity_iff
      (measurable_betaPDFReal (1 / 2) (3 / 2)).ennreal_ofReal).2 ?_
    filter_upwards with x hx
    contrapose! hx
    rw [betaPDFReal, if_neg (by simpa only [Set.mem_Ioo] using hx)]
    simp
  apply integral_congr_ae
  filter_upwards [hsupport] with x hx
  have hclip : clippedCatalanCoordinate x = 4 * x := by
    simp only [clippedCatalanCoordinate,
      BoundedContinuousFunction.coe_ofNormedAddCommGroup]
    rw [Set.projIcc_of_mem zero_le_one ⟨hx.1.le, hx.2.le⟩]
  rw [show shiftTwoGramVector j x = (4 * x) ^ (j + 1) by
      simp [shiftTwoGramVector, hclip],
    show shiftTwoGramVector i x = (4 * x) ^ (i + 1) by
      simp [shiftTwoGramVector, hclip]]
  simp only [map_pow, conj_trivial]
  rw [← pow_add]
  congr 1
  omega

private lemma linearIndependent_toLp_weighted_powers (n : Nat)
    (v : Fin n → Real →ᵇ Real) (weight : Real → Real)
    (hv : ∀ (i : Fin n) (x : Real), x ∈ Set.Ioo (0 : Real) 1 →
      v i x = weight x * (4 * x) ^ i.1)
    (hweight : ∀ x : Real, x ∈ Set.Ioo (0 : Real) 1 → weight x ≠ 0) :
    LinearIndependent Real
      (fun i => BoundedContinuousFunction.toLp 2 catalanBetaMeasure Real (v i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let F : Real →ᵇ Real := ∑ i, c i • v i
  have hFLp : BoundedContinuousFunction.toLp 2 catalanBetaMeasure Real F = 0 := by
    dsimp [F]
    rw [map_sum]
    simpa only [map_smul] using hc
  have hbeta : ∀ᵐ x ∂catalanBetaMeasure, F x = 0 := by
    have hcoe := F.coeFn_toLp 2 catalanBetaMeasure Real
    rw [hFLp] at hcoe
    filter_upwards [hcoe.symm] with x hx
    simpa using hx
  have hvolume : ∀ᵐ x ∂volume.restrict (Set.Ioo (0 : Real) 1), F x = 0 := by
    rw [catalanBetaMeasure, betaMeasure] at hbeta
    have hdensity := (ae_withDensity_iff
      (measurable_betaPDFReal (1 / 2) (3 / 2)).ennreal_ofReal).1 hbeta
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hdensity] with x hx
    intro hxi
    apply hx
    exact ENNReal.ofReal_ne_zero_iff.mpr
      (betaPDFReal_pos hxi.1 hxi.2 (by norm_num) (by norm_num))
  have hpoint : Set.EqOn F 0 (Set.Ioo (0 : Real) 1) :=
    Measure.eqOn_open_of_ae_eq hvolume isOpen_Ioo F.continuous.continuousOn
      continuous_zero.continuousOn
  let p : Polynomial Real := ∑ i : Fin n, Polynomial.monomial i.1 (c i)
  have hpRoot : Set.Ioo (0 : Real) 4 ⊆ {x | p.IsRoot x} := by
    intro y hy
    have hy4 : y / 4 ∈ Set.Ioo (0 : Real) 1 := by constructor <;> nlinarith [hy.1, hy.2]
    have hzero := hpoint hy4
    simp only [F, BoundedContinuousFunction.coe_sum, Finset.sum_apply,
      BoundedContinuousFunction.coe_smul, smul_eq_mul, Pi.zero_apply] at hzero
    simp_rw [hv _ _ hy4] at hzero
    have hpoly : ∑ i : Fin n, c i * y ^ i.1 = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left (hweight _ hy4)
      calc
        weight (y / 4) * ∑ i : Fin n, c i * y ^ i.1 =
            ∑ i : Fin n, c i * (weight (y / 4) * (4 * (y / 4)) ^ i.1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = 0 := by convert hzero using 1
    change p.IsRoot y
    rw [Polynomial.IsRoot.def]
    dsimp [p]
    rw [Polynomial.eval_finsetSum]
    simpa [Polynomial.eval_monomial, mul_comm] using hpoly
  have hpzero : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p
    ((Set.Ioo_infinite (by norm_num : (0 : Real) < 4)).mono hpRoot)
  intro i
  have hcoeff := congrArg (fun q : Polynomial Real => q.coeff i.1) hpzero
  simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Polynomial.coeff_zero] at hcoeff
  have hval (x : Fin n) : (x.1 = i.1) ↔ x = i := Fin.ext_iff.symm
  simp_rw [hval] at hcoeff
  simpa using hcoeff

private lemma shiftOneLpVector_linearIndependent (n : Nat) :
    LinearIndependent Real (fun i : Fin n => shiftOneLpVector i.1) := by
  simpa only [shiftOneLpVector] using
    linearIndependent_toLp_weighted_powers n (fun i => shiftOneGramVector i.1)
      (fun x => Real.sqrt (4 * x))
      (fun i x hx => by
        have hclip : clippedCatalanCoordinate x = 4 * x := by
          simp only [clippedCatalanCoordinate,
            BoundedContinuousFunction.coe_ofNormedAddCommGroup]
          rw [Set.projIcc_of_mem zero_le_one ⟨hx.1.le, hx.2.le⟩]
        simp [shiftOneGramVector, hclip])
      (fun x hx => ne_of_gt (Real.sqrt_pos.2 (mul_pos (by norm_num) hx.1)))

private lemma shiftTwoLpVector_linearIndependent (n : Nat) :
    LinearIndependent Real (fun i : Fin n => shiftTwoLpVector i.1) := by
  simpa only [shiftTwoLpVector] using
    linearIndependent_toLp_weighted_powers n (fun i => shiftTwoGramVector i.1)
      (fun x => 4 * x)
      (fun i x hx => by
        change clippedCatalanCoordinate x ^ (i.1 + 1) =
          4 * x * (4 * x) ^ i.1
        simp only [clippedCatalanCoordinate,
          BoundedContinuousFunction.coe_ofNormedAddCommGroup]
        rw [Set.projIcc_of_mem zero_le_one ⟨hx.1.le, hx.2.le⟩]
        rw [pow_succ'])
      (fun x hx => ne_of_gt (mul_pos (by norm_num) hx.1))

private def catalanHankelMatrix (n r : Nat) : Matrix (Fin n) (Fin n) Real :=
  fun i j => catalan (i.1 + j.1 + r)

private lemma catalanHankelMatrix_one_posDef (n : Nat) :
    Matrix.PosDef (catalanHankelMatrix n 1) := by
  have hgram := Matrix.posDef_gram_of_linearIndependent (shiftOneLpVector_linearIndependent n)
  rw [show catalanHankelMatrix n 1 =
      Matrix.gram Real (fun i : Fin n => shiftOneLpVector i.1) by
    ext i j
    simp only [catalanHankelMatrix, Matrix.gram_apply]
    rw [inner_shiftOneLpVector]]
  exact hgram

private lemma catalanHankelMatrix_two_posDef (n : Nat) :
    Matrix.PosDef (catalanHankelMatrix n 2) := by
  have hgram := Matrix.posDef_gram_of_linearIndependent (shiftTwoLpVector_linearIndependent n)
  rw [show catalanHankelMatrix n 2 =
      Matrix.gram Real (fun i : Fin n => shiftTwoLpVector i.1) by
    ext i j
    simp only [catalanHankelMatrix, Matrix.gram_apply]
    rw [inner_shiftTwoLpVector]]
  exact hgram

private def clippedCatalanProductCoordinate : Real × Real →ᵇ Real :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p : Real × Real => clippedCatalanCoordinate p.1 * clippedCatalanCoordinate p.2)
    ((clippedCatalanCoordinate.continuous.comp continuous_fst).mul
      (clippedCatalanCoordinate.continuous.comp continuous_snd))
    16 (fun p => by
      have hnonneg (x : Real) : 0 ≤ clippedCatalanCoordinate x := by
        simp only [clippedCatalanCoordinate,
          BoundedContinuousFunction.coe_ofNormedAddCommGroup]
        exact mul_nonneg (by norm_num) (Set.projIcc 0 1 zero_le_one x).2.1
      have hle (x : Real) : clippedCatalanCoordinate x ≤ 4 := by
        simp only [clippedCatalanCoordinate,
          BoundedContinuousFunction.coe_ofNormedAddCommGroup]
        exact mul_le_of_le_one_right (by norm_num) (Set.projIcc 0 1 zero_le_one x).2.2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnonneg p.1) (hnonneg p.2))]
      have hbound := mul_le_mul (hle p.1) (hle p.2) (hnonneg p.2) (by norm_num)
      norm_num at hbound
      exact hbound)

private def productShiftOneGramVector (i : Nat) : Real × Real →ᵇ Real :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p : Real × Real =>
      Real.sqrt (clippedCatalanProductCoordinate p) *
        clippedCatalanProductCoordinate p ^ i)
    ((Real.continuous_sqrt.comp clippedCatalanProductCoordinate.continuous).mul
      (clippedCatalanProductCoordinate.continuous.pow i))
    (4 * 16 ^ i) (fun p => by
      have hz0 : 0 ≤ clippedCatalanProductCoordinate p := by
        simp only [clippedCatalanProductCoordinate,
          BoundedContinuousFunction.coe_ofNormedAddCommGroup]
        apply mul_nonneg
        · simp only [clippedCatalanCoordinate,
            BoundedContinuousFunction.coe_ofNormedAddCommGroup]
          exact mul_nonneg (by norm_num) (Set.projIcc 0 1 zero_le_one p.1).2.1
        · simp only [clippedCatalanCoordinate,
            BoundedContinuousFunction.coe_ofNormedAddCommGroup]
          exact mul_nonneg (by norm_num) (Set.projIcc 0 1 zero_le_one p.2).2.1
      have hz16 : clippedCatalanProductCoordinate p ≤ 16 := by
        simp only [clippedCatalanProductCoordinate,
          BoundedContinuousFunction.coe_ofNormedAddCommGroup]
        have hnonneg (x : Real) : 0 ≤ clippedCatalanCoordinate x := by
          simp only [clippedCatalanCoordinate,
            BoundedContinuousFunction.coe_ofNormedAddCommGroup]
          exact mul_nonneg (by norm_num) (Set.projIcc 0 1 zero_le_one x).2.1
        have hle (x : Real) : clippedCatalanCoordinate x ≤ 4 := by
          simp only [clippedCatalanCoordinate,
            BoundedContinuousFunction.coe_ofNormedAddCommGroup]
          exact mul_le_of_le_one_right (by norm_num)
            (Set.projIcc 0 1 zero_le_one x).2.2
        have hbound := mul_le_mul (hle p.1) (hle p.2) (hnonneg p.2) (by norm_num)
        norm_num at hbound
        exact hbound
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hz0 _))]
      exact mul_le_mul (Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith⟩)
        (pow_le_pow_left₀ hz0 hz16 i) (pow_nonneg hz0 _) (by norm_num))

private def productShiftTwoGramVector (i : Nat) : Real × Real →ᵇ Real :=
  clippedCatalanProductCoordinate ^ (i + 1)

private def productShiftOneLpVector (i : Nat) :
    Lp Real 2 (catalanBetaMeasure.prod catalanBetaMeasure) :=
  BoundedContinuousFunction.toLp 2 (catalanBetaMeasure.prod catalanBetaMeasure) Real
    (productShiftOneGramVector i)

private def productShiftTwoLpVector (i : Nat) :
    Lp Real 2 (catalanBetaMeasure.prod catalanBetaMeasure) :=
  BoundedContinuousFunction.toLp 2 (catalanBetaMeasure.prod catalanBetaMeasure) Real
    (productShiftTwoGramVector i)

private lemma inner_productShiftOneLpVector (i j : Nat) :
    inner Real (productShiftOneLpVector i) (productShiftOneLpVector j) =
      (catalan (i + j + 1) : Real) ^ 2 := by
  simp only [productShiftOneLpVector]
  rw [BoundedContinuousFunction.inner_toLp]
  rw [← (catalan_moment_product_and_matrix_entry (i + j + 1) 1 0 0 0).2.1,
    catalanProductMoment]
  have hscalar : ∀ᵐ x ∂catalanBetaMeasure, x ∈ Set.Ioo (0 : Real) 1 := by
    rw [catalanBetaMeasure, betaMeasure]
    refine (ae_withDensity_iff
      (measurable_betaPDFReal (1 / 2) (3 / 2)).ennreal_ofReal).2 ?_
    filter_upwards with x hx
    contrapose! hx
    rw [betaPDFReal, if_neg (by simpa only [Set.mem_Ioo] using hx)]
    simp
  have hsupport :
      ∀ᵐ p ∂(catalanBetaMeasure.prod catalanBetaMeasure),
        p.1 ∈ Set.Ioo (0 : Real) 1 ∧ p.2 ∈ Set.Ioo (0 : Real) 1 := by
    change ∀ᵐ p ∂(catalanBetaMeasure.prod catalanBetaMeasure),
      p ∈ Set.Ioo (0 : Real) 1 ×ˢ Set.Ioo (0 : Real) 1
    rw [Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioo.prod measurableSet_Ioo)]
    filter_upwards [hscalar] with x hx
    filter_upwards [hscalar] with y hy
    exact ⟨hx, hy⟩
  apply integral_congr_ae
  filter_upwards [hsupport] with p hp
  have hclip : clippedCatalanProductCoordinate p = (4 * p.1) * (4 * p.2) := by
    simp only [clippedCatalanProductCoordinate, clippedCatalanCoordinate,
      BoundedContinuousFunction.coe_ofNormedAddCommGroup]
    rw [Set.projIcc_of_mem zero_le_one ⟨hp.1.1.le, hp.1.2.le⟩,
      Set.projIcc_of_mem zero_le_one ⟨hp.2.1.le, hp.2.2.le⟩]
  rw [show productShiftOneGramVector j p =
      Real.sqrt ((4 * p.1) * (4 * p.2)) * ((4 * p.1) * (4 * p.2)) ^ j by
    simp [productShiftOneGramVector, hclip],
    show productShiftOneGramVector i p =
      Real.sqrt ((4 * p.1) * (4 * p.2)) * ((4 * p.1) * (4 * p.2)) ^ i by
    simp [productShiftOneGramVector, hclip]]
  simp only [map_mul, conj_trivial]
  have hz0 : 0 ≤ (4 * p.1) * (4 * p.2) :=
    mul_nonneg (mul_nonneg (by norm_num) hp.1.1.le)
      (mul_nonneg (by norm_num) hp.2.1.le)
  calc
    Real.sqrt ((4 * p.1) * (4 * p.2)) * ((4 * p.1) * (4 * p.2)) ^ j *
          (Real.sqrt ((4 * p.1) * (4 * p.2)) * ((4 * p.1) * (4 * p.2)) ^ i) =
        (Real.sqrt ((4 * p.1) * (4 * p.2)) *
          Real.sqrt ((4 * p.1) * (4 * p.2))) *
          (((4 * p.1) * (4 * p.2)) ^ i * ((4 * p.1) * (4 * p.2)) ^ j) := by ring
    _ = ((4 * p.1) * (4 * p.2)) * ((4 * p.1) * (4 * p.2)) ^ (i + j) := by
      rw [Real.mul_self_sqrt hz0, pow_add]
    _ = ((4 * p.1) * (4 * p.2)) ^ (i + j + 1) := by rw [pow_succ']

private lemma inner_productShiftTwoLpVector (i j : Nat) :
    inner Real (productShiftTwoLpVector i) (productShiftTwoLpVector j) =
      (catalan (i + j + 2) : Real) ^ 2 := by
  simp only [productShiftTwoLpVector]
  rw [BoundedContinuousFunction.inner_toLp]
  rw [← (catalan_moment_product_and_matrix_entry (i + j + 2) 1 0 0 0).2.1,
    catalanProductMoment]
  have hscalar : ∀ᵐ x ∂catalanBetaMeasure, x ∈ Set.Ioo (0 : Real) 1 := by
    rw [catalanBetaMeasure, betaMeasure]
    refine (ae_withDensity_iff
      (measurable_betaPDFReal (1 / 2) (3 / 2)).ennreal_ofReal).2 ?_
    filter_upwards with x hx
    contrapose! hx
    rw [betaPDFReal, if_neg (by simpa only [Set.mem_Ioo] using hx)]
    simp
  have hsupport :
      ∀ᵐ p ∂(catalanBetaMeasure.prod catalanBetaMeasure),
        p.1 ∈ Set.Ioo (0 : Real) 1 ∧ p.2 ∈ Set.Ioo (0 : Real) 1 := by
    change ∀ᵐ p ∂(catalanBetaMeasure.prod catalanBetaMeasure),
      p ∈ Set.Ioo (0 : Real) 1 ×ˢ Set.Ioo (0 : Real) 1
    rw [Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioo.prod measurableSet_Ioo)]
    filter_upwards [hscalar] with x hx
    filter_upwards [hscalar] with y hy
    exact ⟨hx, hy⟩
  apply integral_congr_ae
  filter_upwards [hsupport] with p hp
  have hclip : clippedCatalanProductCoordinate p = (4 * p.1) * (4 * p.2) := by
    simp only [clippedCatalanProductCoordinate, clippedCatalanCoordinate,
      BoundedContinuousFunction.coe_ofNormedAddCommGroup]
    rw [Set.projIcc_of_mem zero_le_one ⟨hp.1.1.le, hp.1.2.le⟩,
      Set.projIcc_of_mem zero_le_one ⟨hp.2.1.le, hp.2.2.le⟩]
  rw [show productShiftTwoGramVector j p = ((4 * p.1) * (4 * p.2)) ^ (j + 1) by
    simp [productShiftTwoGramVector, hclip],
    show productShiftTwoGramVector i p = ((4 * p.1) * (4 * p.2)) ^ (i + 1) by
    simp [productShiftTwoGramVector, hclip]]
  simp only [map_pow, conj_trivial]
  rw [← pow_add]
  congr 1
  omega

private lemma catalanSquareHankelMatrix_eq_product_gram_one (n : Nat) :
    catalanSquareHankelMatrix n 1 =
      Matrix.gram Real (fun i : Fin n => productShiftOneLpVector i.1) := by
  ext i j
  simp only [catalanSquareHankelMatrix, Matrix.gram_apply]
  rw [inner_productShiftOneLpVector]

private lemma catalanSquareHankelMatrix_eq_product_gram_two (n : Nat) :
    catalanSquareHankelMatrix n 2 =
      Matrix.gram Real (fun i : Fin n => productShiftTwoLpVector i.1) := by
  ext i j
  simp only [catalanSquareHankelMatrix, Matrix.gram_apply]
  rw [inner_productShiftTwoLpVector]

private lemma det_gram_monic_polynomial_change {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Real E] (n : Nat) (v : Fin n → E)
    (p : Fin n → Polynomial Real) (hdegree : ∀ i, (p i).natDegree = i.1)
    (hmonic : ∀ i, (p i).Monic) :
    (Matrix.gram Real (fun j : Fin n =>
      ∑ i : Fin n, (p j).coeff i.1 • v i)).det =
      (Matrix.gram Real v).det := by
  let C : Matrix (Fin n) (Fin n) Real :=
    Matrix.of fun i j => (p j).coeff i.1
  have hCdet : C.det = 1 := by
    exact Matrix.det_matrixOfPolynomials p hdegree hmonic
  have hgram : Matrix.gram Real (fun j : Fin n =>
      ∑ i : Fin n, (p j).coeff i.1 • v i) =
      C.transpose * Matrix.gram Real v * C := by
    ext i j
    simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply]
    dsimp [C]
    simp only [inner_sum, sum_inner, inner_smul_left, inner_smul_right, conj_trivial]
    apply Finset.sum_congr rfl
    intro a _
    rw [mul_comm]
  rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hCdet,
    one_mul, mul_one]

private def upperChebyshevAffine : Polynomial Real :=
  (1 / 8 : Real) • (Polynomial.X - Polynomial.C 8)

private def upperChebyshevPolynomial (k : Nat) : Polynomial Real :=
  if k = 0 then 1 else
    (2 * 4 ^ k : Real) •
      (Polynomial.Chebyshev.T Real (k : Int)).comp
        upperChebyshevAffine

private lemma upper_changed_gram_diagonal_le
    (n : Nat) (j : Fin n) (v : Nat → Real × Real →ᵇ Real)
    (hv : ∀ (i : Nat) (p : Real × Real),
      v i p = v 0 p * clippedCatalanProductCoordinate p ^ i) :
    inner Real
        (∑ i : Fin n, (upperChebyshevPolynomial j.1).coeff i.1 •
          BoundedContinuousFunction.toLp 2
            (catalanBetaMeasure.prod catalanBetaMeasure) Real (v i.1))
        (∑ i : Fin n, (upperChebyshevPolynomial j.1).coeff i.1 •
          BoundedContinuousFunction.toLp 2
            (catalanBetaMeasure.prod catalanBetaMeasure) Real (v i.1)) ≤
      (4 * 16 ^ j.1) *
        inner Real
          (BoundedContinuousFunction.toLp 2
            (catalanBetaMeasure.prod catalanBetaMeasure) Real (v 0))
          (BoundedContinuousFunction.toLp 2
            (catalanBetaMeasure.prod catalanBetaMeasure) Real (v 0)) := by
  let w : Real × Real →ᵇ Real :=
    ∑ i : Fin n, (upperChebyshevPolynomial j.1).coeff i.1 • v i.1
  have hAffineDegree : upperChebyshevAffine.natDegree = 1 := by
    rw [upperChebyshevAffine, Polynomial.natDegree_smul_of_smul_regular,
      Polynomial.natDegree_X_sub_C]
    exact IsSMulRegular.of_ne_zero (by norm_num)
  have hAffineLeading : upperChebyshevAffine.leadingCoeff = 1 / 8 := by
    rw [upperChebyshevAffine, Polynomial.leadingCoeff_smul_of_smul_regular,
      Polynomial.leadingCoeff_X_sub_C]
    · simp
    · exact IsSMulRegular.of_ne_zero (by norm_num)
  have hdegree (k : Nat) : (upperChebyshevPolynomial k).natDegree = k := by
    by_cases hk : k = 0
    · simp [upperChebyshevPolynomial, hk]
    · rw [upperChebyshevPolynomial, if_neg hk,
        Polynomial.natDegree_smul_of_smul_regular]
      · rw [Polynomial.natDegree_comp_eq_of_mul_ne_zero]
        · simp [Polynomial.Chebyshev.natDegree_T, hAffineDegree]
        · simp [Polynomial.Chebyshev.leadingCoeff_T, hk, hAffineLeading]
      · exact IsSMulRegular.of_ne_zero (by positivity)
  have hw : ∀ p : Real × Real,
      w p = (upperChebyshevPolynomial j.1).eval
        (clippedCatalanProductCoordinate p) * v 0 p := by
    intro p
    dsimp only [w]
    change (BoundedContinuousFunction.evalCLM Real p)
      (∑ i : Fin n, (upperChebyshevPolynomial j.1).coeff i.1 • v i.1) = _
    rw [map_sum]
    simp only [map_smul, BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
    change (∑ i : Fin n,
      (upperChebyshevPolynomial j.1).coeff i.1 * v i.1 p) = _
    rw [Fin.sum_univ_eq_sum_range (fun i : Nat =>
        (upperChebyshevPolynomial j.1).coeff i * v i p) n,
      Polynomial.eval_eq_sum_range'
        (show (upperChebyshevPolynomial j.1).natDegree < n by
          rw [hdegree]
          exact j.2)]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [hv i p]
    ring
  have htoLp :
      (∑ i : Fin n, (upperChebyshevPolynomial j.1).coeff i.1 •
          BoundedContinuousFunction.toLp 2
            (catalanBetaMeasure.prod catalanBetaMeasure) Real (v i.1)) =
        BoundedContinuousFunction.toLp 2
          (catalanBetaMeasure.prod catalanBetaMeasure) Real w := by
    simp only [w, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (map_smul (BoundedContinuousFunction.toLp 2
      (catalanBetaMeasure.prod catalanBetaMeasure) Real)
      ((upperChebyshevPolynomial j.1).coeff i.1) (v i.1)).symm
  rw [htoLp, BoundedContinuousFunction.inner_toLp,
    BoundedContinuousFunction.inner_toLp]
  simp only [map_mul, conj_trivial]
  rw [← integral_const_mul]
  apply integral_mono
  · change Integrable (⇑(w * w)) (catalanBetaMeasure.prod catalanBetaMeasure)
    exact (w * w).memLp_top.mono_exponent
      (show (1 : ℝ≥0∞) ≤ ∞ by simp) |>.integrable le_rfl
  · have hi : Integrable (⇑(v 0 * v 0))
        (catalanBetaMeasure.prod catalanBetaMeasure) :=
      (v 0 * v 0).memLp_top.mono_exponent
        (show (1 : ℝ≥0∞) ≤ ∞ by simp) |>.integrable le_rfl
    exact hi.const_mul (4 * 16 ^ j.1)
  · intro p
    change w p * w p ≤ (4 * 16 ^ j.1) * (v 0 p * v 0 p)
    rw [hw]
    have hz : clippedCatalanProductCoordinate p ∈ Set.Icc (0 : Real) 16 := by
      have hz0 (x : Real) : 0 ≤ clippedCatalanCoordinate x := by
        simp only [clippedCatalanCoordinate,
          BoundedContinuousFunction.coe_ofNormedAddCommGroup]
        exact mul_nonneg (by norm_num) (Set.projIcc 0 1 zero_le_one x).2.1
      have hz4 (x : Real) : clippedCatalanCoordinate x ≤ 4 := by
        simp only [clippedCatalanCoordinate,
          BoundedContinuousFunction.coe_ofNormedAddCommGroup]
        exact mul_le_of_le_one_right (by norm_num)
          (Set.projIcc 0 1 zero_le_one x).2.2
      constructor
      · simp only [clippedCatalanProductCoordinate,
          BoundedContinuousFunction.coe_ofNormedAddCommGroup]
        exact mul_nonneg (hz0 p.1) (hz0 p.2)
      · simp only [clippedCatalanProductCoordinate,
          BoundedContinuousFunction.coe_ofNormedAddCommGroup]
        nlinarith [mul_le_mul (hz4 p.1) (hz4 p.2) (hz0 p.2) (by norm_num)]
    have hQ : |(upperChebyshevPolynomial j.1).eval
        (clippedCatalanProductCoordinate p)| ≤ 2 * 4 ^ j.1 := by
      have heval : (upperChebyshevPolynomial j.1).eval
          (clippedCatalanProductCoordinate p) =
          if j.1 = 0 then 1 else
            (2 * 4 ^ j.1 : Real) *
              (Polynomial.Chebyshev.T Real (j.1 : Int)).eval
                (clippedCatalanProductCoordinate p / 8 - 1) := by
        by_cases hk : j.1 = 0
        · simp [upperChebyshevPolynomial, hk]
        · simp [upperChebyshevPolynomial, upperChebyshevAffine, hk,
            Polynomial.eval_comp]
          ring_nf
      rw [heval]
      by_cases hk : j.1 = 0
      · simp [hk]
      · rw [if_neg hk, abs_mul]
        have hx : clippedCatalanProductCoordinate p / 8 - 1 ∈
            Set.Icc (-1 : Real) 1 := by
          constructor <;> nlinarith [hz.1, hz.2]
        have hT := Polynomial.Chebyshev.abs_eval_T_real_le_one (j.1 : Int)
          (show |clippedCatalanProductCoordinate p / 8 - 1| ≤ 1 by
            exact abs_le.mpr hx)
        rw [abs_of_nonneg (by positivity : (0 : Real) ≤ 2 * 4 ^ j.1)]
        have hc : (0 : Real) ≤ 2 * 4 ^ j.1 := by positivity
        simpa using mul_le_mul_of_nonneg_left hT hc
    have hQsq : (upperChebyshevPolynomial j.1).eval
          (clippedCatalanProductCoordinate p) ^ 2 ≤ (2 * 4 ^ j.1) ^ 2 := by
      exact sq_le_sq.mpr (by
        simpa [abs_of_nonneg (show (0 : Real) ≤ 2 * 4 ^ j.1 by positivity)] using hQ)
    calc
      ((upperChebyshevPolynomial j.1).eval
            (clippedCatalanProductCoordinate p) * v 0 p) *
          ((upperChebyshevPolynomial j.1).eval
            (clippedCatalanProductCoordinate p) * v 0 p) =
          (upperChebyshevPolynomial j.1).eval
              (clippedCatalanProductCoordinate p) ^ 2 * (v 0 p) ^ 2 := by ring
      _ ≤ (2 * 4 ^ j.1) ^ 2 * (v 0 p) ^ 2 :=
        mul_le_mul_of_nonneg_right hQsq (sq_nonneg _)
      _ = (4 * 16 ^ j.1) * (v 0 p * v 0 p) := by
        rw [show (2 * 4 ^ j.1 : Real) ^ 2 = 4 * 16 ^ j.1 by
          calc
            (2 * 4 ^ j.1 : Real) ^ 2 = 4 * (4 ^ j.1 * 4 ^ j.1) := by ring
            _ = 4 * (4 * 4) ^ j.1 := by rw [mul_pow]
            _ = 4 * 16 ^ j.1 := by norm_num]
        ring

/-- Every determinant in both OEIS sequences is strictly positive, including the
empty determinant at `n = 0`. -/
theorem catalan_square_hankel_det_positive (n : Nat) :
    0 < catalanSquareHankelDet 1 n ∧ 0 < catalanSquareHankelDet 2 n := by
  have hmatrix (r : Nat) : catalanSquareHankelMatrix n r =
      Matrix.hadamard (catalanHankelMatrix n r) (catalanHankelMatrix n r) := by
    ext i j
    simp [catalanSquareHankelMatrix, catalanHankelMatrix,
      Matrix.hadamard_apply, pow_two]
  constructor
  · rw [catalanSquareHankelDet, hmatrix]
    exact (catalanHankelMatrix_one_posDef n).hadamard
      (catalanHankelMatrix_one_posDef n) |>.det_pos
  · rw [catalanSquareHankelDet, hmatrix]
    exact (catalanHankelMatrix_two_posDef n).hadamard
      (catalanHankelMatrix_two_posDef n) |>.det_pos

/-- Chebyshev--Hadamard upper bounds for the two literal squared-Catalan
Hankel determinants. These are sharper than the corresponding bounds with an
additional factor of `n !`. -/
theorem catalan_square_hankel_det_upper (n : Nat) :
    catalanSquareHankelDet 1 n ≤
        (4 : Real) ^ n * 16 ^ (n * (n - 1) / 2) ∧
      catalanSquareHankelDet 2 n ≤
        (16 : Real) ^ n * 16 ^ (n * (n - 1) / 2) := by
  have prove_shift
      (r : Nat) (A : Real)
      (vLp : Nat → Lp Real 2 (catalanBetaMeasure.prod catalanBetaMeasure))
      (vBCF : Nat → Real × Real →ᵇ Real)
      (hvLp : ∀ i, vLp i = BoundedContinuousFunction.toLp 2
        (catalanBetaMeasure.prod catalanBetaMeasure) Real (vBCF i))
      (hvpow : ∀ (i : Nat) (p : Real × Real),
        vBCF i p = vBCF 0 p * clippedCatalanProductCoordinate p ^ i)
      (hgram : catalanSquareHankelMatrix n r =
        Matrix.gram Real (fun i : Fin n => vLp i.1))
      (hpositive : 0 < catalanSquareHankelDet r n)
      (hbase : inner Real (vLp 0) (vLp 0) = (A : Real)) :
      catalanSquareHankelDet r n ≤
        (4 * A) ^ n * 16 ^ (n * (n - 1) / 2) := by
    have hAffineDegree : upperChebyshevAffine.natDegree = 1 := by
      rw [upperChebyshevAffine, Polynomial.natDegree_smul_of_smul_regular,
        Polynomial.natDegree_X_sub_C]
      exact IsSMulRegular.of_ne_zero (by norm_num)
    have hAffineLeading : upperChebyshevAffine.leadingCoeff = 1 / 8 := by
      rw [upperChebyshevAffine, Polynomial.leadingCoeff_smul_of_smul_regular,
        Polynomial.leadingCoeff_X_sub_C]
      · simp
      · exact IsSMulRegular.of_ne_zero (by norm_num)
    have hdegree (k : Nat) : (upperChebyshevPolynomial k).natDegree = k := by
      by_cases hk : k = 0
      · simp [upperChebyshevPolynomial, hk]
      · rw [upperChebyshevPolynomial, if_neg hk,
          Polynomial.natDegree_smul_of_smul_regular]
        · rw [Polynomial.natDegree_comp_eq_of_mul_ne_zero]
          · simp [Polynomial.Chebyshev.natDegree_T, hAffineDegree]
          · simp [Polynomial.Chebyshev.leadingCoeff_T, hk, hAffineLeading]
        · exact IsSMulRegular.of_ne_zero (by positivity)
    have hmonic (k : Nat) : (upperChebyshevPolynomial k).Monic := by
      by_cases hk : k = 0
      · simp [upperChebyshevPolynomial, hk]
      · rw [Polynomial.Monic, upperChebyshevPolynomial, if_neg hk,
          Polynomial.leadingCoeff_smul_of_smul_regular _
            (IsSMulRegular.of_ne_zero (by positivity)),
          Polynomial.leadingCoeff_comp]
        · obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
          rw [Polynomial.Chebyshev.leadingCoeff_T,
            Polynomial.Chebyshev.natDegree_T, hAffineLeading]
          rw [show ((l.succ : Nat) : Int).natAbs = l.succ by omega]
          norm_num only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one,
            Nat.add_sub_cancel, pow_succ]
          calc
            2 * (4 ^ l * 4) * (2 ^ l * ((1 / 8) ^ l * (1 / 8))) =
                (2 * 4 * (1 / 8) : Real) * (4 * 2 * (1 / 8)) ^ l := by
                  rw [mul_pow, mul_pow]
                  ring
            _ = 1 := by norm_num
        · simp [hAffineDegree]
    let u : Fin n → Lp Real 2 (catalanBetaMeasure.prod catalanBetaMeasure) :=
      fun j => ∑ i : Fin n, (upperChebyshevPolynomial j.1).coeff i.1 • vLp i.1
    have hdet : (Matrix.gram Real u).det = catalanSquareHankelDet r n := by
      change (Matrix.gram Real (fun j : Fin n =>
        ∑ i : Fin n, (upperChebyshevPolynomial j.1).coeff i.1 • vLp i.1)).det = _
      rw [det_gram_monic_polynomial_change n (fun i : Fin n => vLp i.1)
        (fun j : Fin n => upperChebyshevPolynomial j.1)
        (fun j => hdegree j.1) (fun j => hmonic j.1), ← hgram]
      rfl
    have hpd : (Matrix.gram Real u).PosDef :=
      (Matrix.posSemidef_gram Real u).posDef_iff_det_ne_zero.mpr
        (hdet.trans_ne (ne_of_gt hpositive))
    calc
      catalanSquareHankelDet r n = (Matrix.gram Real u).det := hdet.symm
      _ ≤ ∏ j : Fin n, Matrix.gram Real u j j :=
        (D5.S3.Arith.GoldenResource.IntegerHadamard.real_posDef_hadamard hpd).1
      _ ≤ ∏ j : Fin n, (4 * A) * 16 ^ j.1 := by
        apply Finset.prod_le_prod
        · intro j _
          rw [Matrix.gram_apply]
          exact real_inner_self_nonneg
        · intro j _
          rw [Matrix.gram_apply]
          change inner Real
              (∑ i : Fin n, (upperChebyshevPolynomial j.1).coeff i.1 • vLp i.1)
              (∑ i : Fin n, (upperChebyshevPolynomial j.1).coeff i.1 • vLp i.1) ≤ _
          have hs :
              (∑ i : Fin n, (upperChebyshevPolynomial j.1).coeff i.1 • vLp i.1) =
                ∑ i : Fin n, (upperChebyshevPolynomial j.1).coeff i.1 •
                  BoundedContinuousFunction.toLp 2
                    (catalanBetaMeasure.prod catalanBetaMeasure) Real (vBCF i.1) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hvLp]
          rw [hs]
          have hd := upper_changed_gram_diagonal_le n j vBCF hvpow
          rw [← hvLp 0, hbase] at hd
          simpa only [mul_assoc, mul_left_comm, mul_comm] using hd
      _ = (4 * A) ^ n * 16 ^ (n * (n - 1) / 2) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, Finset.prod_pow_eq_pow_sum]
        congr 2
        exact (Fin.sum_univ_eq_sum_range (fun i : Nat => i) n).trans
          (Finset.sum_range_id n)
  constructor
  · convert prove_shift 1 1 productShiftOneLpVector productShiftOneGramVector
      (fun _ => rfl) (by
        intro i p
        simp [productShiftOneGramVector, pow_succ'])
      (catalanSquareHankelMatrix_eq_product_gram_one n)
      (catalan_square_hankel_det_positive n).1
      (by rw [inner_productShiftOneLpVector]; norm_num) using 1 <;> norm_num
  · convert prove_shift 2 4 productShiftTwoLpVector productShiftTwoGramVector
      (fun _ => rfl) (by
        intro i p
        simp [productShiftTwoGramVector, pow_succ', pow_add])
      (catalanSquareHankelMatrix_eq_product_gram_two n)
      (catalan_square_hankel_det_positive n).2
      (by rw [inner_productShiftTwoLpVector, catalan_two]; norm_num) using 1 <;> norm_num

end D5.S3.Constants.Moments.CatalanSquareHankelGrowth
