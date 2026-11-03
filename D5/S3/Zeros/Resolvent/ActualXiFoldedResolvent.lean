/- GID: D5/S3/Zeros/Resolvent/ActualXiFoldedResolvent
   generality: I
   mirror-B: D5/B/S3/Zeros/Resolvent/ActualXiFoldedResolvent
   mirror-E: none(waiver:actual-analytic-zero-source)
   anchors: []
   utility: none
   digest: Identify the independently defined actual xi expression with the complete folded resolvent. -/

import D5.S3.Zeros.Resolvent.ActualXiFoldedSpectrum
import Mathlib.Tactic

/-!
The left side is defined from the original xiReading and real firstLiMass.
Only convergent normalized sums are subtracted. The square-source product
and reflection proofs are reused, and the center is treated without dividing
by the spectral variable. No RH or positivity premise is used.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Zeros.Resolvent.ActualXiFoldedResolvent
open Complex Filter D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
open D5.S3.Zeros.Resolvent.ActualXiFoldedSpectrum
open scoped Topology ComplexConjugate

/-- The actual xi expression, independently of every zero sum. -/
def xiOdd (w : ℂ) : ℂ :=
  (I * logDeriv xiReading ((1 / 2 : ℂ) - I * w) - (firstLiMass : ℂ) * w) /
    (w ^ 2 + 1 / 4)

private theorem reflection_fold_hasSum (f : ℕ → ℂ) (a : ℂ)
    (hf : HasSum f a) (hr : ∀ n, f (actualData.reflection n) = f n) :
    HasSum (fun n : PositiveZero => 2 * f n) a := by
  classical
  let p : ℕ → ℂ := {n | 0 < (actualData.zero n).im}.indicator f
  have hp : Summable p := hf.summable.indicator _
  have hpr := actualData.reflection.hasSum_iff.mpr hp.hasSum
  have hpair (n : ℕ) : f n = p n + p (actualData.reflection n) := by
    have hn : (actualData.zero n).im ≠ 0 := by
      intro hz
      have h := actual_ordinate_sq_gt_one n
      rw [hz] at h
      norm_num at h
    dsimp [p, Set.indicator]
    simp only [actualData.zero_reflection, Complex.sub_im, Complex.one_im, zero_sub, hr]
    by_cases h : 0 < (actualData.zero n).im
    · rw [if_pos h, if_neg (by linarith), add_zero]
    · rw [if_neg h, if_pos (by rcases lt_or_gt_of_ne hn with h | h <;> linarith), zero_add]
  have he : (2 : ℂ) * (∑' n, p n) = a := by
    simpa only [two_mul] using ((hp.hasSum.add hpr).congr_fun hpair).unique hf
  have hs : HasSum (fun n => 2 * p n) a := he ▸ hp.hasSum.mul_left 2
  apply (hasSum_subtype_iff_indicator (s := {n : ℕ | 0 < (actualData.zero n).im})
    (f := fun n => 2 * f n)).mpr
  convert hs using 1
  funext n
  by_cases h : 0 < (actualData.zero n).im <;> simp [p, h]

theorem folded_mass_hasSum :
    HasSum (fun n : PositiveZero => 2 * (actualData.multiplicity n : ℂ) *
      (1 / (actualData.zero n * (1 - actualData.zero n)))) (firstLiMass : ℂ) := by
  have h := reflection_fold_hasSum _ _ actual_complex_pairWeight_hasSum (fun n => by
    rw [actualData.multiplicity_reflection, actualData.zero_reflection]
    congr 2 <;> ring)
  convert h using 1
  funext n
  ring

private theorem xi_disk_nonzero (w : ℂ) (hw : ‖w‖ < 1 / 4) :
    xiReading ((1 / 2 : ℂ) + I * w) ≠ 0 := by
  intro hz
  have hz' := (D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup.xiReading_eq_zero_iff_nontrivial
    _).mp hz
  obtain ⟨n, hn⟩ := actualData.zero_exhaustive hz'
  have hlow := actual_ordinate_sq_gt_one n
  have hi := congrArg Complex.im hn
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, zero_mul, zero_add, one_mul] at hi
  norm_num at hi
  rw [hi] at hlow
  have hs := Complex.sq_norm_sub_sq_re w
  nlinarith [norm_nonneg w, sq_nonneg w.im]

private theorem square_disk_nonzero (w : ℂ) (hw : ‖w‖ < 1 / 4) :
    xiSquareSource (w ^ 2) ≠ 0 := by
  rw [xi_square_source_entire_and_composition.2]
  exact div_ne_zero (xi_disk_nonzero w hw) (by
    have h := xi_disk_nonzero 0 (by norm_num)
    simpa using h)

theorem xiOdd_square (w : ℂ) :
    xiOdd w = w * (-2 * logDeriv xiSquareSource (w ^ 2) - firstLiMass) /
      (w ^ 2 + 1 / 4) := by
  have hc := xi_square_logDeriv_composition w
  have hr : logDeriv xiReading ((1 / 2 : ℂ) - I * w) =
      -logDeriv xiReading ((1 / 2 : ℂ) + I * w) := by
    rw [show (1 / 2 : ℂ) - I * w = 1 - ((1 / 2 : ℂ) + I * w) by ring]
    exact xi_logDeriv_reflection _
  unfold xiOdd
  rw [hr]
  congr 1
  linear_combination hc

theorem disk_denominator_ne_zero (w : ℂ) (hw : ‖w‖ < 1 / 4) :
    w ^ 2 + 1 / 4 ≠ 0 := by
  intro h
  have he : w ^ 2 = -(1 / 4 : ℂ) := eq_neg_of_add_eq_zero_left h
  have hn := congrArg norm he
  simp only [norm_pow, norm_neg, norm_div, norm_one, norm_ofNat] at hn
  nlinarith [norm_nonneg w]

theorem resolvent_denominator_ne_zero (n : PositiveZero) (w : ℂ) (hw : ‖w‖ < 1) :
    1 - node n * w ^ 2 ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have hn := congrArg norm h
  rw [norm_one, norm_mul, norm_pow] at hn
  have hx := node_norm_lt_one n
  have hp : ‖node n‖ * ‖w‖ ^ 2 < 1 :=
    (mul_le_mul_of_nonneg_right hx.le (sq_nonneg ‖w‖)).trans_lt
      (by nlinarith [norm_nonneg w])
  linarith

/-- The complete, multiplicity-faithful actual xi folded resolvent, including zero. -/
theorem actual_xi_folded_hasSum (w : ℂ) (hw : ‖w‖ < 1 / 4) :
    HasSum (fun n : PositiveZero => w * weight n / (1 - node n * w ^ 2)) (xiOdd w) := by
  classical
  by_cases hw0 : w = 0
  · subst w
    rw [xiOdd_square]
    simp
  have hF := square_disk_nonzero w hw
  have ha := actual_positive_square_resolvent_hasSum actualData w hw0 hF
  have hs : HasSum (fun n : PositiveZero =>
      (actualData.multiplicity n : ℂ) / (w ^ 2 - (actualData.gamma n) ^ 2))
      (logDeriv xiSquareSource (w ^ 2)) := by
    apply (hasSum_subtype_iff_indicator (s := {n : ℕ | 0 < (actualData.zero n).im})
      (f := fun n => (actualData.multiplicity n : ℂ) /
        (w ^ 2 - (actualData.gamma n) ^ 2))).mpr
    convert ha using 1
    funext n
    simp [positiveSquareResolvent, gamma_re, Set.indicator]
  have hd := disk_denominator_ne_zero w hw
  have h := (((hs.mul_left (-2)).sub folded_mass_hasSum).div_const
    (w ^ 2 + 1 / 4)).mul_left w
  rw [xiOdd_square]
  convert h.congr_fun (fun n => ?_) using 1
  · ring
  · have hg := gamma_ne_zero n
    have hg2 := pow_ne_zero 2 hg
    have hn := node_denominator_ne_zero n
    have hr := resolvent_denominator_ne_zero n w (by linarith)
    have hden : w ^ 2 - (actualData.gamma n) ^ 2 ≠ 0 := by
      intro hzero
      apply hr
      rw [sub_eq_zero.mp hzero]
      simp [node, hg2]
    have hgl : (actualData.gamma n) ^ 2 * node n = 1 := by simp [node, hg2]
    have hres : (actualData.multiplicity n : ℂ) /
        (w ^ 2 - (actualData.gamma n) ^ 2) =
        -((actualData.multiplicity n : ℂ) * node n) / (1 - node n * w ^ 2) := by
      apply (div_eq_div_iff hden hr).mpr
      linear_combination -(actualData.multiplicity n : ℂ) * hgl
    rw [weight_node, pair_weight_node, hres]
    conv_rhs => rw [← mul_div_assoc]
    apply (div_eq_div_iff hr hd).mpr
    have hn4 : (4 : ℂ) + node n ≠ 0 := by
      intro he
      apply hn
      linear_combination (1 / 4 : ℂ) * he
    have hr' : 1 - w ^ 2 * node n ≠ 0 := by simpa [mul_comm] using hr
    field_simp [hn, hr, hn4, hr']
    ring

end D5.S3.Zeros.Resolvent.ActualXiFoldedResolvent
