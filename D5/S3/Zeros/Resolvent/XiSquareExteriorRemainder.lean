/- GID: D5/S3/Zeros/Resolvent/XiSquareExteriorRemainder
   generality: I
   mirror-B: D5/B/S3/Zeros/Resolvent/XiSquareExteriorRemainder
   mirror-E: none(waiver:canonical-product-remainder-not-separately-evidence-modeled)
   anchors: []
   utility: none
   digest: The actual xi square divisor has a complete exterior and sharp square-mass remainder. -/


import D5.S3.Zeros.Resolvent.XiNormalizedResolvent
import D5.S3.Analytic.Isolation.EntireEvenSquareDescent
import D5.S3.Analytic.Dilation.ScalarUnitDressing
import D5.S3.Analytic.Fourier.XiThetaTransform
import D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
import D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation
import D5.S3.Weil.ZetaBridge.OffLineNonrealZeroNegativeWeilSquare
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
The canonical-product estimates are classical complex analysis; no ordinary
mathematical originality is claimed. The finite sharp square-budget recurrence
is the new reusable proof content in this repository. The actual xi source,
zero-order transport, reflection pairing, exact multiplicities, and complete
infinite exterior are applications of the cited protected analytic suppliers.
No Riemann hypothesis, real spectral parameter, simple-zero premise, finite-tail
replacement, or small principal-log disk is assumed. The remainder bound does
not establish joint finite extraction, node signs, or the Riemann hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder

open Complex Filter
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open D5.S3.Zeros.CompletedZeta
open D5.S3.Analytic.Dilation.ScalarUnitDressing
open scoped Topology
private def repeatedIndex (Z : ZeroData) := Σ i : ℕ, Fin (Z.multiplicity i)
private def squareReciprocal (Z : ZeroData) (k : repeatedIndex Z) : ℂ :=
  if 0 < (Z.gamma k.1).re then ((Z.gamma k.1) ^ 2)⁻¹ else 0
private def squareCanonicalProduct (Z : ZeroData) (z : ℂ) : ℂ :=
  ∏' k : repeatedIndex Z, (1 - z * squareReciprocal Z k)

def xiSquareSource (z : ℂ) : ℂ :=
  xiReading ((1 / 2 : ℂ) + Complex.I * Complex.sqrt z) / xiReading (1 / 2)
private theorem xi_center_nonzero : xiReading (1 / 2 : ℂ) ≠ 0 := by
  have hp := D5.S3.Analytic.Fourier.XiThetaTransform.source_theta_normalized.2.1
  intro hz
  have hr := congrArg Complex.re hz
  simp only [Complex.zero_re] at hr
  linarith
private theorem xi_square_source_entire_and_composition :
    Differentiable ℂ xiSquareSource ∧
      ∀ w : ℂ, xiSquareSource (w ^ 2) =
        xiReading ((1 / 2 : ℂ) + Complex.I * w) / xiReading (1 / 2) := by
  have hf : Differentiable ℂ (fun w : ℂ => xiReading ((1 / 2 : ℂ) + Complex.I * w)) :=
    xi_reading_differentiable.comp (by fun_prop)
  have he : Function.Even (fun w : ℂ => xiReading ((1 / 2 : ℂ) + Complex.I * w)) := by
    intro w
    change xiReading ((1 / 2 : ℂ) + Complex.I * (-w)) =
      xiReading ((1 / 2 : ℂ) + Complex.I * w)
    rw [show (1 / 2 : ℂ) + Complex.I * (-w) =
      1 - ((1 / 2 : ℂ) + Complex.I * w) by ring]
    exact xi_reading_reflection _
  obtain ⟨F, hF, _⟩ :=
    D5.S3.Analytic.Isolation.EntireEvenSquareDescent.entire_even_square_descent hf he
  have heq : xiSquareSource = fun z : ℂ => F z / xiReading (1 / 2) := by
    funext z
    have hsq : (Complex.sqrt z) ^ 2 = z :=
      Complex.cpow_nat_inv_pow z (by norm_num : (2 : ℕ) ≠ 0)
    have hid := hF.2 (Complex.sqrt z)
    rw [hsq] at hid
    simp only [xiSquareSource, ← hid]
  constructor
  · rw [heq]
    exact hF.1.div_const _
  · intro w
    rw [heq]
    exact congrArg (fun x : ℂ => x / xiReading (1 / 2)) (hF.2 w)
private theorem xi_square_source_at_zero : xiSquareSource 0 = 1 := by
  have h := xi_square_source_entire_and_composition.2 0
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero,
    div_self xi_center_nonzero] using h
private theorem actual_square_zero_order (Z : ZeroData) (n : ℕ) :
    analyticOrderNatAt xiSquareSource ((Z.gamma n) ^ 2) = Z.multiplicity n := by
  have hgamma : Z.gamma n ≠ 0 := by
    intro h
    have hz := Z.zero_eq_critical_add_I_mul_gamma n
    have hi := D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation.ZeroData.im_ne_zero
      Z n (Z.zero_isNontrivial n)
    apply hi
    rw [h] at hz
    simpa [Weil.Convention.criticalAbscissa] using congrArg Complex.im hz
  have hz : (1 / 2 : ℂ) + Complex.I * Z.gamma n = Z.zero n := by
    simpa [Weil.Convention.criticalAbscissa] using (Z.zero_eq_critical_add_I_mul_gamma n).symm
  have hxiOrder : analyticOrderNatAt xiReading (Z.zero n) = Z.multiplicity n := by
    have hn := Z.zero_isNontrivial n
    have h0 : Z.zero n ≠ 0 := by intro h; simpa [h] using hn.2.1
    have h1 : Z.zero n ≠ 1 := by intro h; simpa [h] using hn.2.2
    have he : xiReading =ᶠ[𝓝 (Z.zero n)]
        (fun z : ℂ => ((1 / 2 : ℂ) * z * (z - 1)) * completedRiemannZeta z) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds h0,
        isOpen_compl_singleton.mem_nhds h1] with z hz0 hz1
      exact xi_reading_eq_completed_zeta hz0 hz1
    have ho := (nonzero_scalar_dressing_preserves_zero_and_analytic_order
      (Zeta23.RvM.analyticAt_completedRiemannZeta h0 h1)
      (g := fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1)) (by fun_prop)
      (by exact mul_ne_zero (mul_ne_zero (by norm_num) h0) (sub_ne_zero.mpr h1))).2
    rw [analyticOrderNatAt, analyticOrderAt_congr he, ho]
    exact (Zeta23.RvM.analyticOrderNatAt_completedRiemannZeta hn.2.1 h1).trans
      (multiplicity_eq_zeroMult Z n).symm
  have hc : analyticOrderAt (xiSquareSource ∘ (fun w : ℂ => w ^ 2)) (Z.gamma n) =
      analyticOrderAt xiSquareSource ((Z.gamma n) ^ 2) := by
    apply analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop)
    simpa using mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hgamma
  have hfun : xiSquareSource ∘ (fun w : ℂ => w ^ 2) =
      (fun w : ℂ => xiReading ((1 / 2 : ℂ) + Complex.I * w) / xiReading (1 / 2)) := by
    funext w
    exact xi_square_source_entire_and_composition.2 w
  have hscalar : analyticOrderAt
      (fun w : ℂ => xiReading ((1 / 2 : ℂ) + Complex.I * w) / xiReading (1 / 2))
      (Z.gamma n) =
      analyticOrderAt (fun w : ℂ => xiReading ((1 / 2 : ℂ) + Complex.I * w))
        (Z.gamma n) := by
    have h := (nonzero_scalar_dressing_preserves_zero_and_analytic_order
      (f := fun w : ℂ => xiReading ((1 / 2 : ℂ) + Complex.I * w))
      (s := Z.gamma n)
      ((xi_reading_differentiable.analyticAt _).comp (by fun_prop))
      (g := fun _ : ℂ => (xiReading (1 / 2))⁻¹) analyticAt_const
      (inv_ne_zero xi_center_nonzero)).2
    simpa only [div_eq_mul_inv, mul_comm] using h
  have ha : analyticOrderAt (fun w : ℂ => xiReading ((1 / 2 : ℂ) + Complex.I * w))
      (Z.gamma n) = analyticOrderAt xiReading (Z.zero n) := by
    have h := analyticOrderAt_comp_of_deriv_ne_zero (f := xiReading)
      (g := fun w : ℂ => (1 / 2 : ℂ) + Complex.I * w) (z₀ := Z.gamma n)
      (by fun_prop) (by simpa using Complex.I_ne_zero)
    simpa only [Function.comp_def, hz] using h
  unfold analyticOrderNatAt
  rw [← hc, hfun, hscalar, ha]
  exact hxiOrder
private theorem weighted_inverse_square_summable (Z : ZeroData) :
    Summable (fun i : ℕ => (Z.multiplicity i : ℝ) / ‖Z.gamma i‖ ^ 2) := by
  have h := (zeroEquiv Z).summable_iff.mpr (Zeta23.WeilEF.zero_sum_inv_sq Zeta23.zetaSeam)
  have hw : Summable (fun i : ℕ => (Z.multiplicity i : ℝ) /
      (1 + ‖Z.gamma i‖ ^ 2)) := by
    convert h using 1
    funext i
    change _ = (Zeta23.zeroMult (Z.zero i) : ℝ) /
      (1 + Complex.normSq (Zeta23.gammaOf (Z.zero i)))
    rw [← multiplicity_eq_zeroMult Z i, gammaOf_eq_spectralParameter]
    simp only [ZeroData.gamma, Complex.normSq_eq_norm_sq]
  have he : ∀ᶠ i in cofinite, 1 ≤ ‖Z.gamma i‖ := by
    apply Filter.mem_cofinite.mpr
    apply (Z.locallyFinite 1).subset
    intro i hi
    change ‖Z.gamma i‖ ≤ 1
    have hni : ¬1 ≤ ‖Z.gamma i‖ := hi
    exact (lt_of_not_ge hni).le
  apply (hw.mul_left 2).of_norm_bounded_eventually
  filter_upwards [he] with i hi
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hp : 0 < ‖Z.gamma i‖ ^ 2 := by positivity
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hp (by positivity : 0 < 1 + ‖Z.gamma i‖ ^ 2)).mpr
  have hq : 0 ≤ ‖Z.gamma i‖ ^ 2 - 1 := by nlinarith
  nlinarith [mul_nonneg (Nat.cast_nonneg (Z.multiplicity i)) hq]
private theorem square_reciprocal_norm_summable (Z : ZeroData) :
    Summable (fun k : repeatedIndex Z => ‖squareReciprocal Z k‖) := by
  classical
  apply (summable_sigma_of_nonneg (fun k => norm_nonneg (squareReciprocal Z k))).mpr
  constructor
  · intro i
    exact Summable.of_finite
  · have hw := weighted_inverse_square_summable Z
    apply hw.of_nonneg_of_le
    · intro i; positivity
    · intro i
      simp only [tsum_fintype, squareReciprocal]
      by_cases hi : 0 < (Z.gamma i).re
      · simp only [if_pos hi, norm_inv, norm_pow, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, one_div]
        rfl
      · simp only [if_neg hi, norm_zero, Finset.sum_const_zero]
        positivity
private theorem square_product_compact_convergence (Z : ZeroData)
    (K : Set ℂ) (hK : IsCompact K) :
    HasProdUniformlyOn (fun k : repeatedIndex Z => fun z => 1 - z * squareReciprocal Z k)
      (squareCanonicalProduct Z) K := by
  obtain ⟨M, hM, hb⟩ := hK.isBounded.exists_pos_norm_le
  have hs := (square_reciprocal_norm_summable Z).mul_left M
  have hp := hs.hasProdUniformlyOn_one_add hK
    (f := fun k : repeatedIndex Z => fun z : ℂ => -(z * squareReciprocal Z k))
    (Filter.Eventually.of_forall (fun k z hz => by
      rw [norm_neg, norm_mul]
      exact mul_le_mul_of_nonneg_right (hb z hz) (norm_nonneg _)))
    (fun k => by fun_prop)
  convert! hp using 1 <;> simp only [sub_eq_add_neg, squareCanonicalProduct]
private theorem square_product_locally_uniform (Z : ZeroData) :
    HasProdLocallyUniformlyOn
      (fun k : repeatedIndex Z => fun z => 1 - z * squareReciprocal Z k)
      (squareCanonicalProduct Z) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  exact square_product_compact_convergence Z K hK
private theorem square_product_entire (Z : ZeroData) :
    Differentiable ℂ (squareCanonicalProduct Z) := by
  classical
  rw [← differentiableOn_univ]
  apply (square_product_locally_uniform Z).differentiableOn
    (Filter.Eventually.of_forall (fun s => ?_)) isOpen_univ
  exact (Differentiable.fun_finsetProd (fun k hk => by fun_prop)).differentiableOn
private theorem square_product_at_zero (Z : ZeroData) :
    squareCanonicalProduct Z 0 = 1 := by
  simp [squareCanonicalProduct]
theorem xi_logDeriv_reflection (s : ℂ) :
    logDeriv xiReading (1 - s) = -logDeriv xiReading s := by
  have hc := logDeriv_comp (xi_reading_differentiable (1 - s))
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s)
  have heq : xiReading ∘ (fun z : ℂ => 1 - z) = xiReading := by
    funext z
    exact xi_reading_reflection z
  rw [heq] at hc
  have hd : deriv (fun z : ℂ => 1 - z) s = -1 := by simp
  rw [hd, mul_neg_one] at hc
  simpa only [neg_neg] using (congrArg Neg.neg hc).symm
private theorem xi_square_logDeriv_composition (w : ℂ) :
    logDeriv xiSquareSource (w ^ 2) * (2 * w) =
      Complex.I * logDeriv xiReading ((1 / 2 : ℂ) + Complex.I * w) := by
  have hF := xi_square_source_entire_and_composition
  have hc := logDeriv_comp (g := fun z : ℂ => z ^ 2) (hF.1 (w ^ 2))
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z ^ 2) w)
  have heq : xiSquareSource ∘ (fun z : ℂ => z ^ 2) =
      fun z : ℂ => xiReading ((1 / 2 : ℂ) + Complex.I * z) * (xiReading (1 / 2))⁻¹ := by
    funext z
    simpa only [Function.comp_apply, div_eq_mul_inv] using hF.2 z
  rw [heq, logDeriv_mul_const _ _ (inv_ne_zero xi_center_nonzero)] at hc
  have hg := logDeriv_comp (g := fun z : ℂ => (1 / 2 : ℂ) + Complex.I * z)
    (xi_reading_differentiable ((1 / 2 : ℂ) + Complex.I * w))
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (1 / 2 : ℂ) + Complex.I * z) w)
  have hdp : deriv (fun z : ℂ => z ^ 2) w = 2 * w := by simp
  have hdl : deriv (fun z : ℂ => (1 / 2 : ℂ) + Complex.I * z) w = Complex.I := by simp
  rw [hdp] at hc
  rw [hdl] at hg
  exact hc.symm.trans (hg.trans (mul_comm _ _))
private theorem actual_square_resolvent_hasSum (Z : ZeroData) (w : ℂ)
    (hw : w ≠ 0) (hF : xiSquareSource (w ^ 2) ≠ 0) :
    HasSum (fun i : ℕ => (Z.multiplicity i : ℂ) / (w ^ 2 - (Z.gamma i) ^ 2))
      (2 * logDeriv xiSquareSource (w ^ 2)) := by
  let sp : ℂ := (1 / 2 : ℂ) + Complex.I * w
  let sm : ℂ := (1 / 2 : ℂ) - Complex.I * w
  have hsp : xiReading sp ≠ 0 := by
    have hid := xi_square_source_entire_and_composition.2 w
    intro hz
    dsimp [sp] at hz
    rw [hz, zero_div] at hid
    exact hF hid
  have hsm : xiReading sm ≠ 0 := by
    have heq : sm = 1 - sp := by dsimp [sp, sm]; ring
    rw [heq, xi_reading_reflection]
    exact hsp
  have hp := D5.S3.Zeros.Resolvent.XiNormalizedResolvent.xi_reading_normalized_resolvent_hasSum
    Z sp hsp
  have hm := D5.S3.Zeros.Resolvent.XiNormalizedResolvent.xi_reading_normalized_resolvent_hasSum
    Z sm hsm
  have h := (hp.sub hm).mul_left (Complex.I / (2 * w))
  have hvalue : Complex.I / (2 * w) *
      ((logDeriv xiReading sp - logDeriv xiReading 0) -
        (logDeriv xiReading sm - logDeriv xiReading 0)) =
      2 * logDeriv xiSquareSource (w ^ 2) := by
    have hsmr : sm = 1 - sp := by dsimp [sp, sm]; ring
    rw [hsmr, xi_logDeriv_reflection]
    have hc := xi_square_logDeriv_composition w
    change logDeriv xiSquareSource (w ^ 2) * (2 * w) =
      Complex.I * logDeriv xiReading sp at hc
    field_simp [hw]
    linear_combination -2 * hc
  rw [hvalue] at h
  apply h.congr_fun
  intro i
  have hp0 : sp - Z.zero i ≠ 0 := by
    intro hz
    apply hsp
    rw [sub_eq_zero.mp hz]
    exact (D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup.xiReading_eq_zero_iff_nontrivial
      _).mpr (zeroEquiv Z i).property
  have hm0 : sm - Z.zero i ≠ 0 := by
    intro hz
    apply hsm
    rw [sub_eq_zero.mp hz]
    exact (D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup.xiReading_eq_zero_iff_nontrivial
      _).mpr (zeroEquiv Z i).property
  have hden : w ^ 2 - (Z.gamma i) ^ 2 ≠ 0 := by
    have hid : w ^ 2 - (Z.gamma i) ^ 2 = (sp - Z.zero i) * (sm - Z.zero i) := by
      rw [Z.zero_eq_critical_add_I_mul_gamma]
      dsimp [sp, sm, D5.S3.Weil.Convention.criticalAbscissa]
      ring_nf
      norm_num [Complex.I_sq]
      ring
    rw [hid]
    exact mul_ne_zero hp0 hm0
  have hcancel :
      (Z.multiplicity i : ℂ) * (1 / (sp - Z.zero i) + 1 / Z.zero i) -
      (Z.multiplicity i : ℂ) * (1 / (sm - Z.zero i) + 1 / Z.zero i) =
      (Z.multiplicity i : ℂ) * (1 / (sp - Z.zero i) - 1 / (sm - Z.zero i)) := by ring
  rw [hcancel]
  field_simp [hw, hp0, hm0, hden]
  rw [Z.zero_eq_critical_add_I_mul_gamma]
  dsimp [sp, sm, D5.S3.Weil.Convention.criticalAbscissa]
  ring_nf
  norm_num [Complex.I_sq]
  ring

-- These bindings are development helpers for the single complete actual-source
-- product/remainder endpoint. No separate retention or admission is claimed.
private def positiveSquareResolvent (Z : ZeroData) (z : ℂ) (i : ℕ) : ℂ :=
  if 0 < (Z.gamma i).re then (Z.multiplicity i : ℂ) / (z - (Z.gamma i) ^ 2) else 0
private theorem gamma_real_nonzero (Z : ZeroData) (i : ℕ) : (Z.gamma i).re ≠ 0 := by
  have h := D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation.ZeroData.im_ne_zero
    Z i (Z.zero_isNontrivial i)
  have heq : (Z.gamma i).re = (Z.zero i).im := by
    simp [ZeroData.gamma, spectralParameter, D5.S3.Weil.Convention.criticalAbscissa,
      Complex.div_re, Complex.normSq_I]
  rwa [heq]
private theorem actual_positive_square_resolvent_hasSum (Z : ZeroData) (w : ℂ)
    (hw : w ≠ 0) (hF : xiSquareSource (w ^ 2) ≠ 0) :
    HasSum (positiveSquareResolvent Z (w ^ 2)) (logDeriv xiSquareSource (w ^ 2)) := by
  classical
  let p := positiveSquareResolvent Z (w ^ 2)
  have ha := actual_square_resolvent_hasSum Z w hw hF
  have hp : Summable p := by
    have hh := ha.summable.indicator {i : ℕ | 0 < (Z.gamma i).re}
    convert! hh using 1
  have hr : HasSum (fun i => p (Z.reflection i)) (∑' i, p i) :=
    Z.reflection.hasSum_iff.mpr hp.hasSum
  have hpair : ∀ i : ℕ, (Z.multiplicity i : ℂ) / (w ^ 2 - (Z.gamma i) ^ 2) =
      p i + p (Z.reflection i) := by
    intro i
    dsimp [p, positiveSquareResolvent]
    rw [Z.gamma_reflection, Z.multiplicity_reflection, neg_sq, Complex.neg_re]
    by_cases hi : 0 < (Z.gamma i).re
    · rw [if_pos hi, if_neg (by linarith), add_zero]
    · have hn : (Z.gamma i).re < 0 := lt_of_le_of_ne (le_of_not_gt hi) (gamma_real_nonzero Z i)
      rw [if_neg hi, if_pos (by linarith), zero_add]
  have hs := (hp.hasSum.add hr).congr_fun hpair
  have he : 2 * (∑' i, p i) = 2 * logDeriv xiSquareSource (w ^ 2) := by
    simpa only [two_mul] using hs.unique ha
  have hv := mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) he
  exact hv ▸ hp.hasSum
private theorem actual_positive_square_resolvent_hasSum_at (Z : ZeroData) (z : ℂ)
    (hz : z ≠ 0) (hF : xiSquareSource z ≠ 0) :
    HasSum (positiveSquareResolvent Z z) (logDeriv xiSquareSource z) := by
  let w := Complex.sqrt z
  have hsq : w ^ 2 = z :=
    Complex.cpow_nat_inv_pow z (by norm_num : (2 : ℕ) ≠ 0)
  have hw : w ≠ 0 := by
    intro hw
    rw [hw, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
    exact hz hsq.symm
  simpa only [hsq] using actual_positive_square_resolvent_hasSum Z w hw (hsq ▸ hF)
private def squareProductRadius (Z : ZeroData) : ℝ :=
  (4 * (1 + ∑' k : repeatedIndex Z, ‖squareReciprocal Z k‖))⁻¹
private theorem square_product_radius_positive (Z : ZeroData) : 0 < squareProductRadius Z := by
  have h : 0 ≤ ∑' k : repeatedIndex Z, ‖squareReciprocal Z k‖ := tsum_nonneg (fun _ => norm_nonneg _)
  dsimp [squareProductRadius]
  positivity
private theorem small_square_factor_bound (Z : ZeroData) (z : ℂ)
    (hz : ‖z‖ < squareProductRadius Z) (k : repeatedIndex Z) :
    ‖z * squareReciprocal Z k‖ ≤ 1 / 4 ∧
      1 / 2 ≤ ‖1 - z * squareReciprocal Z k‖ := by
  let S : ℝ := ∑' j : repeatedIndex Z, ‖squareReciprocal Z j‖
  have hS : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
  have hk : ‖squareReciprocal Z k‖ ≤ S :=
    (square_reciprocal_norm_summable Z).le_tsum k (fun _ _ => norm_nonneg _)
  have hp : ‖z * squareReciprocal Z k‖ ≤ 1 / 4 := by
    rw [norm_mul]
    calc
      ‖z‖ * ‖squareReciprocal Z k‖ ≤ squareProductRadius Z * (1 + S) :=
        mul_le_mul hz.le (by linarith) (norm_nonneg _) (square_product_radius_positive Z).le
      _ = 1 / 4 := by
        dsimp [squareProductRadius, S]
        field_simp
      _ ≤ 1 / 4 := le_rfl
  refine ⟨hp, ?_⟩
  have hb := norm_sub_norm_le (1 : ℂ) (z * squareReciprocal Z k)
  rw [norm_one] at hb
  linarith
private theorem linear_factor_logDeriv (a z : ℂ) :
    logDeriv (fun v : ℂ => 1 - v * a) z = -a / (1 - z * a) := by
  have hd : deriv (fun v : ℂ => 1 - v * a) z = -a := by
    convert! ((hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_id z).mul_const a)).deriv using 1
    simp
  rw [logDeriv_apply, hd]
private theorem square_factor_logDeriv_norm_summable (Z : ZeroData) (z : ℂ)
    (hz : ‖z‖ < squareProductRadius Z) :
    Summable (fun k : repeatedIndex Z =>
      ‖logDeriv (fun v : ℂ => 1 - v * squareReciprocal Z k) z‖) := by
  apply ((square_reciprocal_norm_summable Z).mul_left 2).of_nonneg_of_le
  · intro k; positivity
  · intro k
    rw [linear_factor_logDeriv, norm_div, norm_neg]
    have hd := (small_square_factor_bound Z z hz k).2
    apply (div_le_iff₀ (by linarith : 0 < ‖1 - z * squareReciprocal Z k‖)).mpr
    nlinarith [norm_nonneg (squareReciprocal Z k)]
private theorem square_factor_logDeriv_hasSum_fiber (Z : ZeroData) (z : ℂ)
    (hz : ‖z‖ < squareProductRadius Z) (i : ℕ) :
    HasSum (fun j : Fin (Z.multiplicity i) =>
      logDeriv (fun v : ℂ => 1 - v * squareReciprocal Z ⟨i, j⟩) z)
      (positiveSquareResolvent Z z i) := by
  classical
  have hγ0 : Z.gamma i ≠ 0 := by
    intro hzero
    exact gamma_real_nonzero Z i (congrArg Complex.re hzero)
  have hγ : (Z.gamma i) ^ 2 ≠ 0 := pow_ne_zero 2 hγ0
  have hterm : ∀ j : Fin (Z.multiplicity i),
      logDeriv (fun v : ℂ => 1 - v * squareReciprocal Z ⟨i, j⟩) z =
        if 0 < (Z.gamma i).re then 1 / (z - (Z.gamma i) ^ 2) else 0 := by
    intro j
    rw [linear_factor_logDeriv]
    by_cases hi : 0 < (Z.gamma i).re
    · have hfac : 1 - z * ((Z.gamma i) ^ 2)⁻¹ ≠ 0 := by
        have hb := (small_square_factor_bound Z z hz ⟨i, j⟩).2
        simp only [squareReciprocal, if_pos hi] at hb
        intro hf
        rw [hf, norm_zero] at hb
        norm_num at hb
      have hden : z - (Z.gamma i) ^ 2 ≠ 0 := by
        intro he
        apply hfac
        rw [sub_eq_zero.mp he, mul_inv_cancel₀ hγ, sub_self]
      have hdiff : -z + (Z.gamma i) ^ 2 ≠ 0 := by
        rw [show -z + (Z.gamma i) ^ 2 = -(z - (Z.gamma i) ^ 2) by ring]
        exact neg_ne_zero.mpr hden
      simp only [squareReciprocal, if_pos hi]
      field_simp [hγ0, hγ, hden, hfac, hdiff]
      calc
        _ = (-z + (Z.gamma i) ^ 2) * (-z + (Z.gamma i) ^ 2)⁻¹ := by ring
        _ = 1 := mul_inv_cancel₀ hdiff
    · simp [squareReciprocal, hi]
  have hs := hasSum_fintype (fun j : Fin (Z.multiplicity i) =>
      logDeriv (fun v : ℂ => 1 - v * squareReciprocal Z ⟨i, j⟩) z)
  convert hs using 1
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    positiveSquareResolvent]
  split_ifs <;> simp [div_eq_mul_inv]
private theorem square_product_logDeriv_eq_source_off_zero (Z : ZeroData) (z : ℂ)
    (hz : z ≠ 0) (hsmall : ‖z‖ < squareProductRadius Z)
    (hF : xiSquareSource z ≠ 0) (hP : squareCanonicalProduct Z z ≠ 0) :
    logDeriv (squareCanonicalProduct Z) z = logDeriv xiSquareSource z := by
  have hs := (square_factor_logDeriv_norm_summable Z z hsmall).of_norm
  have hprod : logDeriv (squareCanonicalProduct Z) z =
      ∑' k : repeatedIndex Z, logDeriv (fun v : ℂ => 1 - v * squareReciprocal Z k) z := by
    apply logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ z)
    · intro k
      have hb := (small_square_factor_bound Z z hsmall k).2
      intro he
      rw [he, norm_zero] at hb
      norm_num at hb
    · intro k; exact (by fun_prop : Differentiable ℂ (fun v : ℂ => 1 - v * squareReciprocal Z k)).differentiableOn
    · exact hs
    · exact (square_product_locally_uniform Z).multipliableLocallyUniformlyOn
    · exact hP
  have hf := hs.hasSum.sigma (square_factor_logDeriv_hasSum_fiber Z z hsmall)
  have ha := actual_positive_square_resolvent_hasSum_at Z z hz hF
  exact hprod.trans (hf.unique ha)
private theorem actual_xi_square_complete_product (Z : ZeroData) :
    xiSquareSource = squareCanonicalProduct Z := by
  have hF := xi_square_source_entire_and_composition.1
  have hP := square_product_entire Z
  have hfn : ∀ᶠ z in 𝓝 (0 : ℂ), xiSquareSource z ≠ 0 :=
    hF.continuous.continuousAt.eventually_ne (by rw [xi_square_source_at_zero]; exact one_ne_zero)
  have hpn : ∀ᶠ z in 𝓝 (0 : ℂ), squareCanonicalProduct Z z ≠ 0 :=
    hP.continuous.continuousAt.eventually_ne (by rw [square_product_at_zero]; exact one_ne_zero)
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp (hfn.and hpn)
  let r : ℝ := min ε (squareProductRadius Z)
  have hr : 0 < r := lt_min hε (square_product_radius_positive Z)
  have hgood : ∀ z ∈ Metric.ball (0 : ℂ) r,
      xiSquareSource z ≠ 0 ∧ squareCanonicalProduct Z z ≠ 0 := by
    intro z hz
    exact hεball ((Metric.ball_subset_ball (min_le_left _ _)) hz)
  have hsmall : ∀ z ∈ Metric.ball (0 : ℂ) r, ‖z‖ < squareProductRadius Z := by
    intro z hz
    have hnorm : ‖z‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    exact hnorm.trans_le (min_le_right _ _)
  have hnear : logDeriv (squareCanonicalProduct Z) =ᶠ[𝓝[≠] (0 : ℂ)] logDeriv xiSquareSource := by
    have hb : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ Metric.ball (0 : ℂ) r :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) hr)
    filter_upwards [hb, self_mem_nhdsWithin] with z hz hzne
    exact square_product_logDeriv_eq_source_off_zero Z z hzne (hsmall z hz)
      (hgood z hz).1 (hgood z hz).2
  have hPc : ContinuousAt (logDeriv (squareCanonicalProduct Z)) 0 := by
    change ContinuousAt (fun z => deriv (squareCanonicalProduct Z) z / squareCanonicalProduct Z z) 0
    exact (hP.analyticAt 0).deriv.continuousAt.div hP.continuous.continuousAt
      (by rw [square_product_at_zero]; exact one_ne_zero)
  have hFc : ContinuousAt (logDeriv xiSquareSource) 0 := by
    change ContinuousAt (fun z => deriv xiSquareSource z / xiSquareSource z) 0
    exact (hF.analyticAt 0).deriv.continuousAt.div hF.continuous.continuousAt
      (by rw [xi_square_source_at_zero]; exact one_ne_zero)
  have hzero : logDeriv (squareCanonicalProduct Z) 0 = logDeriv xiSquareSource 0 :=
    tendsto_nhds_unique (hPc.tendsto.mono_left nhdsWithin_le_nhds)
      ((hFc.tendsto.mono_left nhdsWithin_le_nhds).congr' hnear.symm)
  have heq : Set.EqOn (logDeriv (squareCanonicalProduct Z)) (logDeriv xiSquareSource)
      (Metric.ball (0 : ℂ) r) := by
    intro z hz
    by_cases hzne : z = 0
    · simpa only [hzne] using hzero
    · exact square_product_logDeriv_eq_source_off_zero Z z hzne (hsmall z hz)
        (hgood z hz).1 (hgood z hz).2
  obtain ⟨c, _, hc⟩ := (logDeriv_eqOn_iff hP.differentiableOn hF.differentiableOn
    Metric.isOpen_ball (convex_ball (0 : ℂ) r).isPreconnected
    (fun z hz => (hgood z hz).1) (fun z hz => (hgood z hz).2)).mp heq
  have hc1 : c = 1 := by
    have hid := hc (Metric.mem_ball_self hr)
    simpa only [square_product_at_zero, Pi.smul_apply, smul_eq_mul,
      xi_square_source_at_zero, mul_one] using hid.symm
  rw [hc1] at hc
  simp only [one_smul] at hc
  have hevent : squareCanonicalProduct Z =ᶠ[𝓝 (0 : ℂ)] xiSquareSource :=
    Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℂ) hr) hc
  exact ((hP.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    (hF.differentiableOn.analyticOnNhd isOpen_univ) hevent).symm
private def primaryFactor (u : ℂ) : ℂ := (1 - u) * Complex.exp u
private theorem primary_factor_norm_bound (u : ℂ) :
    ‖primaryFactor u‖ ≤ Real.exp (‖u‖ ^ 2 / 2) := by
  have hn : ‖1 - u‖ ^ 2 = 1 - 2 * u.re + ‖u‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im]
    ring
  have hs : ‖primaryFactor u‖ ^ 2 ≤ (Real.exp (‖u‖ ^ 2 / 2)) ^ 2 := by
    dsimp [primaryFactor]
    rw [norm_mul, mul_pow, Complex.norm_exp, hn,
      ← Real.exp_nat_mul u.re 2, ← Real.exp_nat_mul (‖u‖ ^ 2 / 2) 2]
    calc
      (1 - 2 * u.re + ‖u‖ ^ 2) * Real.exp (2 * u.re) ≤
          Real.exp (-2 * u.re + ‖u‖ ^ 2) * Real.exp (2 * u.re) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp (-2 * u.re + ‖u‖ ^ 2)]
      _ = Real.exp (2 * (‖u‖ ^ 2 / 2)) := by rw [← Real.exp_add]; congr 1; ring
  nlinarith [norm_nonneg (primaryFactor u), Real.exp_pos (‖u‖ ^ 2 / 2)]
private theorem primary_factor_remainder_integral (u : ℂ) :
    primaryFactor u - 1 = -u ^ 2 *
      ∫ t : ℝ in 0..1, (t : ℂ) * Complex.exp ((t : ℂ) * u) := by
  have hd (t : ℝ) : HasDerivAt
      (fun s : ℝ => primaryFactor ((s : ℂ) * u))
      (-u ^ 2 * ((t : ℂ) * Complex.exp ((t : ℂ) * u))) t := by
    have hu := (hasDerivAt_id (t : ℂ)).mul_const u
    have hh := (((hasDerivAt_const (t : ℂ) (1 : ℂ)).sub hu).mul hu.cexp).comp_ofReal
    convert! hh using 1 <;> dsimp [primaryFactor] <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t)
    ((by fun_prop : Continuous (fun t : ℝ =>
      -u ^ 2 * ((t : ℂ) * Complex.exp ((t : ℂ) * u)))).intervalIntegrable 0 1)
  simpa only [intervalIntegral.integral_const_mul, Complex.ofReal_one, one_mul,
    Complex.ofReal_zero, zero_mul, primaryFactor, sub_zero, Complex.exp_zero, mul_one]
    using hi.symm
private theorem primary_factor_remainder_bound (u : ℂ) :
    ‖primaryFactor u - 1‖ ≤
      (Real.exp (1 / 2) - 1) * ‖u‖ ^ 2 * Real.exp (‖u‖ ^ 2 / 2) := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => Real.exp (s ^ 2 / 2))
      (t * Real.exp (t ^ 2 / 2)) t := by
    convert! (((hasDerivAt_id t).pow 2).div_const 2).exp using 1 <;>
      simp only [Pi.pow_apply, id_eq] <;> ring
  have hi : (∫ t : ℝ in 0..1, t * Real.exp (t ^ 2 / 2)) = Real.exp (1 / 2) - 1 := by
    simpa only [one_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, Real.exp_zero]
      using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
        ((by fun_prop : Continuous (fun t : ℝ => t * Real.exp (t ^ 2 / 2))).intervalIntegrable 0 1)
  have hb : ‖∫ t : ℝ in 0..1, (t : ℂ) * Complex.exp ((t : ℂ) * u)‖ ≤
      Real.exp (‖u‖ ^ 2 / 2) * (Real.exp (1 / 2) - 1) := by
    calc
      _ ≤ ∫ t : ℝ in 0..1,
          Real.exp (‖u‖ ^ 2 / 2) * (t * Real.exp (t ^ 2 / 2)) := by
        apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ) ≤ 1)
        · apply Filter.Eventually.of_forall
          intro t ht
          have hy : t * u.re ≤ ‖u‖ ^ 2 / 2 + t ^ 2 / 2 := by
            have hh := mul_le_mul_of_nonneg_left (Complex.re_le_norm u) ht.1.le
            nlinarith [sq_nonneg (‖u‖ - t)]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1,
            Complex.norm_exp]
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
            sub_zero]
          calc
            t * Real.exp (t * u.re) ≤ t * Real.exp (‖u‖ ^ 2 / 2 + t ^ 2 / 2) :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hy) ht.1.le
            _ = _ := by rw [Real.exp_add]; ring
        · exact (by fun_prop : Continuous (fun t : ℝ =>
            Real.exp (‖u‖ ^ 2 / 2) * (t * Real.exp (t ^ 2 / 2)))).intervalIntegrable 0 1
      _ = _ := by rw [intervalIntegral.integral_const_mul, hi]
  rw [primary_factor_remainder_integral, norm_mul, norm_neg, norm_pow]
  exact (mul_le_mul_of_nonneg_left hb (sq_nonneg ‖u‖)).trans_eq (by ring)
private theorem finite_primary_product_remainder_bound {ι : Type*}
    (s : Finset ι) (a : ι → ℂ) :
    ‖(∏ i ∈ s, primaryFactor (a i)) - 1‖ ≤
      (Real.exp (1 / 2) - 1) * (∑ i ∈ s, ‖a i‖ ^ 2) *
        Real.exp ((∑ i ∈ s, ‖a i‖ ^ 2) / 2) := by
  classical
  have hc : 0 ≤ Real.exp (1 / 2) - 1 := by
    have h := Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [Real.exp_zero] at h
    linarith
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    let S : ℝ := ∑ j ∈ s, ‖a j‖ ^ 2
    have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hE : 1 ≤ Real.exp (S / 2) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    calc
      ‖primaryFactor (a i) * (∏ j ∈ s, primaryFactor (a j)) - 1‖ =
          ‖primaryFactor (a i) * ((∏ j ∈ s, primaryFactor (a j)) - 1) +
            (primaryFactor (a i) - 1)‖ := by congr 1; ring
      _ ≤ ‖primaryFactor (a i) * ((∏ j ∈ s, primaryFactor (a j)) - 1)‖ +
          ‖primaryFactor (a i) - 1‖ := norm_add_le _ _
      _ ≤ Real.exp (‖a i‖ ^ 2 / 2) *
            ((Real.exp (1 / 2) - 1) * S * Real.exp (S / 2)) +
          (Real.exp (1 / 2) - 1) * ‖a i‖ ^ 2 * Real.exp (‖a i‖ ^ 2 / 2) := by
        rw [norm_mul]
        exact add_le_add
          (mul_le_mul (primary_factor_norm_bound _) ih (norm_nonneg _) (Real.exp_pos _).le)
          (primary_factor_remainder_bound _)
      _ ≤ Real.exp (‖a i‖ ^ 2 / 2) *
            ((Real.exp (1 / 2) - 1) * S * Real.exp (S / 2)) +
          ((Real.exp (1 / 2) - 1) * ‖a i‖ ^ 2 * Real.exp (‖a i‖ ^ 2 / 2)) *
            Real.exp (S / 2) := by
        apply add_le_add le_rfl
        exact le_mul_of_one_le_right (by positivity) hE
      _ = _ := by rw [show (‖a i‖ ^ 2 + S) / 2 = ‖a i‖ ^ 2 / 2 + S / 2 by ring,
          Real.exp_add]; ring
private def primaryProduct {ι : Type*} (a : ι → ℂ) (w : ℂ) : ℂ :=
  ∏' i, primaryFactor (w * a i)
private theorem primary_product_compact_convergence {ι : Type*} (a : ι → ℂ)
    (ha : Summable (fun i => ‖a i‖ ^ 2)) (K : Set ℂ) (hK : IsCompact K) :
    HasProdUniformlyOn (fun i w => primaryFactor (w * a i)) (primaryProduct a) K := by
  obtain ⟨M, hM, hb⟩ := hK.isBounded.exists_pos_norm_le
  let S : ℝ := ∑' i, ‖a i‖ ^ 2
  let c : ℝ := Real.exp (1 / 2) - 1
  let C : ℝ := c * M ^ 2 * Real.exp (M ^ 2 * S / 2)
  have hc : 0 ≤ c := by
    dsimp [c]
    have h := Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [Real.exp_zero] at h
    linarith
  have hu := (ha.mul_left C).hasProdUniformlyOn_one_add hK
    (f := fun i w => primaryFactor (w * a i) - 1)
    (Filter.Eventually.of_forall (fun i w hw => by
      have hi : ‖a i‖ ^ 2 ≤ S := ha.le_tsum i (fun _ _ => sq_nonneg _)
      have hw2 : ‖w * a i‖ ^ 2 ≤ M ^ 2 * ‖a i‖ ^ 2 := by
        rw [norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb w hw) 2)
          (sq_nonneg _)
      have hs : ‖w * a i‖ ^ 2 ≤ M ^ 2 * S :=
        hw2.trans (mul_le_mul_of_nonneg_left hi (sq_nonneg M))
      calc
        ‖primaryFactor (w * a i) - 1‖ ≤
            c * ‖w * a i‖ ^ 2 * Real.exp (‖w * a i‖ ^ 2 / 2) :=
          primary_factor_remainder_bound _
        _ ≤ c * (M ^ 2 * ‖a i‖ ^ 2) * Real.exp (M ^ 2 * S / 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hw2 hc)
            (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (by positivity)
        _ = C * ‖a i‖ ^ 2 := by dsimp [C]; ring))
    (fun i => by dsimp [primaryFactor]; fun_prop)
  convert! hu using 1 <;> simp only [add_sub_cancel] <;> rfl

private theorem primary_product_locally_uniform {ι : Type*} (a : ι → ℂ)
    (ha : Summable (fun i => ‖a i‖ ^ 2)) :
    HasProdLocallyUniformlyOn (fun i w => primaryFactor (w * a i))
      (primaryProduct a) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  exact primary_product_compact_convergence a ha K hK

private theorem primary_product_entire {ι : Type*} (a : ι → ℂ)
    (ha : Summable (fun i => ‖a i‖ ^ 2)) : Differentiable ℂ (primaryProduct a) := by
  classical
  rw [← differentiableOn_univ]
  apply (primary_product_locally_uniform a ha).differentiableOn
    (Filter.Eventually.of_forall (fun s => ?_)) isOpen_univ
  exact (Differentiable.fun_finsetProd (fun i _ => by dsimp [primaryFactor]; fun_prop)).differentiableOn

private theorem complete_primary_product_remainder_bound {ι : Type*} (a : ι → ℂ)
    (ha : Summable (fun i => ‖a i‖ ^ 2)) (w : ℂ) :
    ‖primaryProduct a w - 1‖ ≤
      (Real.exp (1 / 2) - 1) * ‖w‖ ^ 2 * (∑' i, ‖a i‖ ^ 2) *
        Real.exp (‖w‖ ^ 2 * (∑' i, ‖a i‖ ^ 2) / 2) := by
  have hs : Summable (fun i => ‖w * a i‖ ^ 2) := by
    simpa only [norm_mul, mul_pow] using ha.mul_left (‖w‖ ^ 2)
  have hp : Tendsto (fun s : Finset ι => ∏ i ∈ s, primaryFactor (w * a i)) atTop
      (𝓝 (primaryProduct a w)) :=
    (primary_product_locally_uniform a ha).hasProd (Set.mem_univ w)
  have hsum : Tendsto (fun s : Finset ι => ∑ i ∈ s, ‖w * a i‖ ^ 2) atTop
      (𝓝 (∑' i, ‖w * a i‖ ^ 2)) := hs.hasSum
  have hL : Tendsto (fun s : Finset ι => ‖(∏ i ∈ s, primaryFactor (w * a i)) - 1‖) atTop
      (𝓝 ‖primaryProduct a w - 1‖) := (hp.sub tendsto_const_nhds).norm
  have hR : Tendsto (fun s : Finset ι =>
      (Real.exp (1 / 2) - 1) * (∑ i ∈ s, ‖w * a i‖ ^ 2) *
        Real.exp ((∑ i ∈ s, ‖w * a i‖ ^ 2) / 2)) atTop
      (𝓝 ((Real.exp (1 / 2) - 1) * (∑' i, ‖w * a i‖ ^ 2) *
        Real.exp ((∑' i, ‖w * a i‖ ^ 2) / 2))) :=
    (tendsto_const_nhds.mul hsum).mul
      ((Real.continuous_exp.tendsto _).comp (hsum.div_const 2))
  have hr := le_of_tendsto_of_tendsto' hL hR
    (fun s => finite_primary_product_remainder_bound s (fun i => w * a i))
  simpa only [norm_mul, mul_pow, tsum_mul_left, mul_assoc] using hr

private def linearProduct {ι : Type*} (c : ι → ℂ) (z : ℂ) : ℂ := ∏' i, (1 - z * c i)

private def shiftedCoefficient {ι : Type*} (c : ι → ℂ) (a : ℂ) (i : ι) : ℂ :=
  c i / (1 - a * c i)

private theorem linear_product_locally_uniform {ι : Type*} (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) :
    HasProdLocallyUniformlyOn (fun i z => 1 - z * c i) (linearProduct c) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨M, _, hb⟩ := hK.isBounded.exists_pos_norm_le
  have hp := (hc.mul_left M).hasProdUniformlyOn_one_add hK
    (f := fun i z => -(z * c i))
    (Filter.Eventually.of_forall (fun i z hz => by
      rw [norm_neg, norm_mul]
      exact mul_le_mul_of_nonneg_right (hb z hz) (norm_nonneg _)))
    (fun i => by fun_prop)
  convert! hp using 1 <;> simp only [sub_eq_add_neg] <;> rfl

private theorem linear_product_entire {ι : Type*} (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) : Differentiable ℂ (linearProduct c) := by
  classical
  rw [← differentiableOn_univ]
  apply (linear_product_locally_uniform c hc).differentiableOn
    (Filter.Eventually.of_forall (fun s => ?_)) isOpen_univ
  exact (Differentiable.fun_finsetProd (fun i _ => by fun_prop)).differentiableOn

private theorem linear_factor_nonzero {ι : Type*} (c : ι → ℂ) (a : ℂ)
    (ha : linearProduct c a ≠ 0) (i : ι) : 1 - a * c i ≠ 0 := by
  intro hi
  exact ha (tprod_of_exists_eq_zero ⟨i, hi⟩)

private theorem shifted_coefficient_norm_summable {ι : Type*} (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (a : ℂ) :
    Summable (fun i => ‖shiftedCoefficient c a i‖) := by
  have he : ∀ᶠ i in cofinite, ‖a * c i‖ ≤ 1 / 2 := by
    simpa only [norm_mul] using
      (hc.mul_left ‖a‖).tendsto_cofinite_zero.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)
  apply (hc.mul_left 2).of_norm_bounded_eventually
  filter_upwards [he] with i hi
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hd : 1 / 2 ≤ ‖1 - a * c i‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (a * c i)
    rw [norm_one] at h
    linarith
  rw [shiftedCoefficient, norm_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖1 - a * c i‖)).mpr
  nlinarith [norm_nonneg (c i)]

private theorem shifted_coefficient_square_summable {ι : Type*} (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (a : ℂ) :
    Summable (fun i => ‖shiftedCoefficient c a i‖ ^ 2) := by
  have hb := shifted_coefficient_norm_summable c hc a
  have he := hb.tendsto_cofinite_zero.eventually_le_const (by norm_num : (0 : ℝ) < 1)
  apply hb.of_norm_bounded_eventually
  filter_upwards [he] with i hi
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [norm_nonneg (shiftedCoefficient c a i)]

private theorem linear_product_logDeriv {ι : Type*} (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (a : ℂ) (ha : linearProduct c a ≠ 0) :
    logDeriv (linearProduct c) a = -(∑' i, shiftedCoefficient c a i) := by
  have hb := (shifted_coefficient_norm_summable c hc a).of_norm
  have hs : Summable (fun i => logDeriv (fun z : ℂ => 1 - z * c i) a) := by
    convert! hb.neg using 1
    funext i
    rw [linear_factor_logDeriv, neg_div]
    rfl
  have h := logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ a)
    (linear_factor_nonzero c a ha) (fun i => (by fun_prop : Differentiable ℂ
      (fun z : ℂ => 1 - z * c i)).differentiableOn) hs
    (linear_product_locally_uniform c hc).multipliableLocallyUniformlyOn ha
  change logDeriv (fun z : ℂ => ∏' i, (1 - z * c i)) a = _
  simpa only [linear_factor_logDeriv, neg_div, tsum_neg,
    shiftedCoefficient] using h

private theorem linear_product_recenter_identity {ι : Type*} (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (a : ℂ) (ha : linearProduct c a ≠ 0) (w : ℂ) :
    primaryProduct (shiftedCoefficient c a) w =
      linearProduct c (a + w) / linearProduct c a *
        Complex.exp (-w * logDeriv (linearProduct c) a) := by
  have hp := linear_product_locally_uniform c hc
  have hratio := (hp.hasProd (Set.mem_univ (a + w))).div₀
    (hp.hasProd (Set.mem_univ a)) ha
  have he := (((shifted_coefficient_norm_summable c hc a).of_norm.hasSum).mul_left w).cexp
  have hh := hratio.mul he
  have hpoint (i : ι) : primaryFactor (w * shiftedCoefficient c a i) =
      ((1 - (a + w) * c i) / (1 - a * c i)) *
        Complex.exp (w * shiftedCoefficient c a i) := by
    have hden := linear_factor_nonzero c a ha i
    have hr : 1 - w * shiftedCoefficient c a i = (1 - (a + w) * c i) / (1 - a * c i) := by
      apply (eq_div_iff hden).mpr
      dsimp [shiftedCoefficient]
      rw [sub_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hden]
      ring
    rw [primaryFactor, hr]
  have hm := hh.congr_fun hpoint
  have hn := (primary_product_locally_uniform (shiftedCoefficient c a)
    (shifted_coefficient_square_summable c hc a)).hasProd (Set.mem_univ w)
  have hid := hn.unique hm
  simpa only [linear_product_logDeriv c hc a ha, neg_mul, mul_neg, neg_neg] using hid

private theorem complete_linear_product_recenter_remainder {ι : Type*} (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (a : ℂ) (ha : linearProduct c a ≠ 0) (w : ℂ) :
    ‖linearProduct c (a + w) / linearProduct c a *
        Complex.exp (-w * logDeriv (linearProduct c) a) - 1‖ ≤
      (Real.exp (1 / 2) - 1) * ‖w‖ ^ 2 * (∑' i, ‖shiftedCoefficient c a i‖ ^ 2) *
        Real.exp (‖w‖ ^ 2 * (∑' i, ‖shiftedCoefficient c a i‖ ^ 2) / 2) := by
  rw [← linear_product_recenter_identity c hc a ha w]
  exact complete_primary_product_remainder_bound _ (shifted_coefficient_square_summable c hc a) w

private def selectedRepeated (Z : ZeroData) (s : Finset ℕ) : Finset (repeatedIndex Z) :=
  s.sigma (fun i => Finset.univ)

private def exteriorReciprocal (Z : ZeroData) (s : Finset ℕ) (k : repeatedIndex Z) : ℂ :=
  if k.1 ∈ s then 0 else squareReciprocal Z k

def exteriorSource (Z : ZeroData) (s : Finset ℕ) : ℂ → ℂ :=
  linearProduct (exteriorReciprocal Z s)

def clusterSource (Z : ZeroData) (s : Finset ℕ) (z : ℂ) : ℂ :=
  ∏ k ∈ selectedRepeated Z s, (1 - z * squareReciprocal Z k)

private theorem exterior_reciprocal_norm_summable (Z : ZeroData) (s : Finset ℕ) :
    Summable (fun k : repeatedIndex Z => ‖exteriorReciprocal Z s k‖) := by
  classical
  apply (square_reciprocal_norm_summable Z).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro k
  dsimp [exteriorReciprocal]
  split_ifs <;> simp

private theorem actual_xi_cluster_exterior_factorization (Z : ZeroData) (s : Finset ℕ)
    (z : ℂ) : xiSquareSource z = clusterSource Z s z * exteriorSource Z s z := by
  classical
  let c : repeatedIndex Z → ℂ := fun k => if k.1 ∈ s then squareReciprocal Z k else 0
  have hc : Summable (fun k => ‖c k‖) := by
    apply (square_reciprocal_norm_summable Z).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro k
    dsimp [c]
    split_ifs <;> simp
  have hcp : linearProduct c z = clusterSource Z s z := by
    rw [linearProduct, tprod_eq_prod (s := selectedRepeated Z s) (fun k hk => ?_)]
    · apply Finset.prod_congr rfl
      intro k hk
      have hks : k.1 ∈ s := by
        change k ∈ s.sigma (fun i => Finset.univ) at hk
        exact (Finset.mem_sigma.mp hk).1
      simp only [c, if_pos hks, clusterSource]
    · have hks : k.1 ∉ s := by
        intro hi
        apply hk
        exact Finset.mem_sigma.mpr ⟨hi, Finset.mem_univ _⟩
      simp [c, hks]
  have hp := ((linear_product_locally_uniform c hc).hasProd (Set.mem_univ z)).mul
    ((linear_product_locally_uniform (exteriorReciprocal Z s)
      (exterior_reciprocal_norm_summable Z s)).hasProd (Set.mem_univ z))
  have hpoint (k : repeatedIndex Z) : 1 - z * squareReciprocal Z k =
      (1 - z * c k) * (1 - z * exteriorReciprocal Z s k) := by
    by_cases hk : k.1 ∈ s <;> simp [c, exteriorReciprocal, hk]
  have hid := ((square_product_locally_uniform Z).hasProd (Set.mem_univ z)).unique
    (hp.congr_fun hpoint)
  rw [actual_xi_square_complete_product Z]
  simpa only [hcp, exteriorSource] using hid

private theorem actual_exterior_entire (Z : ZeroData) (s : Finset ℕ) :
    Differentiable ℂ (exteriorSource Z s) :=
  linear_product_entire _ (exterior_reciprocal_norm_summable Z s)

private theorem actual_exterior_recenter_entire (Z : ZeroData) (s : Finset ℕ)
    (a : ℂ) (ha : exteriorSource Z s a ≠ 0) :
    Differentiable ℂ (fun w : ℂ =>
      exteriorSource Z s (a + w) / exteriorSource Z s a *
        Complex.exp (-w * logDeriv (exteriorSource Z s) a)) := by
  have hid := linear_product_recenter_identity (exteriorReciprocal Z s)
    (exterior_reciprocal_norm_summable Z s) a ha
  have heq : (fun w : ℂ =>
      exteriorSource Z s (a + w) / exteriorSource Z s a *
        Complex.exp (-w * logDeriv (exteriorSource Z s) a)) =
      primaryProduct (shiftedCoefficient (exteriorReciprocal Z s) a) := by
    funext w
    exact (hid w).symm
  rw [heq]
  exact primary_product_entire _
    (shifted_coefficient_square_summable _ (exterior_reciprocal_norm_summable Z s) a)

def exteriorSquareMass (Z : ZeroData) (s : Finset ℕ) (a : ℂ) : ℝ :=
  ∑' i : ℕ, if i ∉ s ∧ 0 < (Z.gamma i).re then
    (Z.multiplicity i : ℝ) / ‖a - (Z.gamma i) ^ 2‖ ^ 2 else 0

private theorem exterior_shifted_square_norm (Z : ZeroData) (s : Finset ℕ)
    (a : ℂ) (k : repeatedIndex Z) :
    ‖shiftedCoefficient (exteriorReciprocal Z s) a k‖ ^ 2 =
      if k.1 ∉ s ∧ 0 < (Z.gamma k.1).re then
        1 / ‖a - (Z.gamma k.1) ^ 2‖ ^ 2 else 0 := by
  classical
  by_cases hsel : k.1 ∈ s
  · simp [shiftedCoefficient, exteriorReciprocal, hsel]
  by_cases hpos : 0 < (Z.gamma k.1).re
  · have hg : (Z.gamma k.1) ^ 2 ≠ 0 := by
      apply pow_ne_zero
      intro hz
      exact gamma_real_nonzero Z k.1 (congrArg Complex.re hz)
    have hden : 1 - a * ((Z.gamma k.1) ^ 2)⁻¹ =
        ((Z.gamma k.1) ^ 2 - a) / (Z.gamma k.1) ^ 2 := by
      apply (eq_div_iff hg).mpr
      rw [sub_mul, one_mul, mul_assoc, inv_mul_cancel₀ hg, mul_one]
    have hshift : shiftedCoefficient (exteriorReciprocal Z s) a k =
        ((Z.gamma k.1) ^ 2 - a)⁻¹ := by
      simp only [shiftedCoefficient, exteriorReciprocal, if_neg hsel,
        squareReciprocal, if_pos hpos, hden, div_div_eq_mul_div,
        inv_mul_cancel₀ hg, one_div]
    rw [hshift]
    simp only [hsel, not_false_eq_true, hpos, and_self, if_true,
      norm_inv, inv_pow, norm_sub_rev, one_div]
  · simp [shiftedCoefficient, exteriorReciprocal, squareReciprocal, hsel, hpos]

private theorem actual_exterior_shifted_square_mass (Z : ZeroData) (s : Finset ℕ)
    (a : ℂ) :
    (∑' k : repeatedIndex Z, ‖shiftedCoefficient (exteriorReciprocal Z s) a k‖ ^ 2) =
      exteriorSquareMass Z s a := by
  classical
  have hs := shifted_coefficient_square_summable (exteriorReciprocal Z s)
    (exterior_reciprocal_norm_summable Z s) a
  unfold exteriorSquareMass
  change (∑' k : (Σ i : ℕ, Fin (Z.multiplicity i)),
      ‖shiftedCoefficient (exteriorReciprocal Z s) a k‖ ^ 2) = _
  rw [hs.tsum_sigma' (fun _ => Summable.of_finite)]
  apply tsum_congr
  intro i
  have hterm (j : Fin (Z.multiplicity i)) :
      ‖shiftedCoefficient (exteriorReciprocal Z s) a ⟨i, j⟩‖ ^ 2 =
        if i ∉ s ∧ 0 < (Z.gamma i).re then
          1 / ‖a - (Z.gamma i) ^ 2‖ ^ 2 else 0 :=
    exterior_shifted_square_norm Z s a ⟨i, j⟩
  simp_rw [hterm]
  rw [tsum_fintype]
  by_cases hi : i ∉ s ∧ 0 < (Z.gamma i).re <;> simp [hi, div_eq_mul_inv]

private theorem actual_exterior_whole_plane_remainder (Z : ZeroData) (s : Finset ℕ)
    (a : ℂ) (ha : exteriorSource Z s a ≠ 0) (w : ℂ) :
    ‖exteriorSource Z s (a + w) / exteriorSource Z s a *
        Complex.exp (-w * logDeriv (exteriorSource Z s) a) - 1‖ ≤
      (Real.exp (1 / 2) - 1) * ‖w‖ ^ 2 *
        (∑' k : repeatedIndex Z, ‖shiftedCoefficient (exteriorReciprocal Z s) a k‖ ^ 2) *
        Real.exp (‖w‖ ^ 2 *
          (∑' k : repeatedIndex Z, ‖shiftedCoefficient (exteriorReciprocal Z s) a k‖ ^ 2) / 2) :=
  complete_linear_product_recenter_remainder _ (exterior_reciprocal_norm_summable Z s) a ha w

theorem xi_square_cluster_exterior_remainder (Z : ZeroData)
    (s : Finset ℕ) (a : ℂ) (ha : exteriorSource Z s a ≠ 0) :
    (∀ i : ℕ, analyticOrderNatAt xiSquareSource ((Z.gamma i) ^ 2) = Z.multiplicity i) ∧
    (∀ z : ℂ, xiSquareSource z = clusterSource Z s z * exteriorSource Z s z) ∧
    Differentiable ℂ (exteriorSource Z s) ∧
    Differentiable ℂ (fun w : ℂ =>
      exteriorSource Z s (a + w) / exteriorSource Z s a *
        Complex.exp (-w * logDeriv (exteriorSource Z s) a)) ∧
    ∀ w : ℂ,
      ‖exteriorSource Z s (a + w) / exteriorSource Z s a *
          Complex.exp (-w * logDeriv (exteriorSource Z s) a) - 1‖ ≤
        (Real.exp (1 / 2) - 1) * ‖w‖ ^ 2 * exteriorSquareMass Z s a *
          Real.exp (‖w‖ ^ 2 * exteriorSquareMass Z s a / 2) := by
  refine ⟨actual_square_zero_order Z, actual_xi_cluster_exterior_factorization Z s,
    actual_exterior_entire Z s, actual_exterior_recenter_entire Z s a ha, ?_⟩
  intro w
  simpa only [actual_exterior_shifted_square_mass] using
    actual_exterior_whole_plane_remainder Z s a ha w

#print axioms actual_xi_square_complete_product
#print axioms actual_square_zero_order
#print axioms finite_primary_product_remainder_bound
#print axioms complete_primary_product_remainder_bound
#print axioms xi_square_cluster_exterior_remainder

end D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
