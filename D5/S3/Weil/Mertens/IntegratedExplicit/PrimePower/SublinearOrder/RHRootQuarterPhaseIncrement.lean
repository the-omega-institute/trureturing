/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootQuarterPhaseIncrement
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootQuarterPhaseIncrement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp forward increments of the full root spectrum under quarter-phase recurrence. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHRootLateIncrement
import D5.S3.Weil.Mertens.ZeroAbscissaPower
import D5.S3.Weil.ZeroData.ZetaOrdinateCompleteOptimizer
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula

/-! The quarter phase aligns the signed sine terms of both ordinate signs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped Topology ComplexConjugate

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff actualCoeff_hasSum)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower (rootCoeff rootCoeff_bound)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope (coeff_real)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit phaseOrbit_cluster_iff)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean (frequency exp_mode_norm)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder (phaseOrbit_eq_mode)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity (K K_zero)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelGlobalStrictPositivity (weight)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp (c R cusp_remainder_bound)
open D5.S3.Weil.Mertens.ZeroAbscissaPower (actual_high_weight)
open D5.S3.Weil.ZeroData
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness (PositiveZetaZero ordinate slope)
open D5.S3.Weil.ZeroData.ZetaOrdinateCompleteOptimizer (quarterPhase phaseHull)
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula (zeroEquiv multiplicity_eq_zeroMult)
open D5.S3.Analytic.Asymptotics.LogarithmicPhaseStiffness (phaseSlope phaseWeight)

private theorem weighted_coeff_error {r : ℝ} (hr : 1 < r) (k : ℕ) :
    |(actualZero k).im| * ‖rootCoeff r k + (r : ℂ) * actualCoeff k‖ ≤
      r * (r - 1) * ‖actualCoeff k‖ := by
  have h0 : actualZero k ≠ 0 := by
    intro hz
    simpa [hz] using zero_re_pos k
  have h1 : (1 : ℂ) - actualZero k ≠ 0 := by
    intro hz
    have he := congrArg Complex.re hz
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at he
    linarith [zero_re_lt_one k]
  have h2 : (r : ℂ) - actualZero k ≠ 0 := by
    intro hz
    have he := congrArg Complex.re hz
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at he
    linarith [zero_re_lt_one k]
  have hcoeff : rootCoeff r k + (r : ℂ) * actualCoeff k =
      ((r : ℂ) * ((r : ℂ) - 1) * actualCoeff k) / ((r : ℂ) - actualZero k) := by
    unfold rootCoeff actualCoeff
    field_simp
    ring
  have hgamma : |(actualZero k).im| ≤ ‖(r : ℂ) - actualZero k‖ := by
    simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] using
      Complex.abs_im_le_norm ((r : ℂ) - actualZero k)
  rw [hcoeff, norm_div, norm_mul, norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hr),
    abs_of_pos (sub_pos.mpr hr)]
  calc
    _ = (|(actualZero k).im| / ‖(r : ℂ) - actualZero k‖) *
        (r * (r - 1) * ‖actualCoeff k‖) := by ring
    _ ≤ 1 * (r * (r - 1) * ‖actualCoeff k‖) := by
      exact mul_le_mul_of_nonneg_right
        ((div_le_one₀ (norm_pos_iff.mpr h2)).2 hgamma) (by positivity)
    _ = _ := one_mul _

theorem tsum_occurrences_eq_twice_positive (f : ℂ → ℝ) (hconj : ∀ z : ℂ, f (conj z) = f z)
    (hs : Summable (fun k : ℕ => f (actualZero k))) :
    (∑' k : ℕ, f (actualZero k)) =
      2 * ∑' p : PositiveZetaZero, (Zeta23.zeroMult p.val : ℝ) * f p.val := by
  classical
  let term := fun n : ℕ => (actualData.multiplicity n : ℝ) * f (actualData.zero n)
  have hocc : Summable (fun p : ActualZeroOccurrence => f (actualData.zero p.1)) :=
    (actualOccurrenceEquiv.summable_iff).1
      (by simpa only [Function.comp_def, actualZero] using hs)
  have hterm : Summable term := by
    simpa only [term, tsum_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using hocc.sigma
  let pos : Set ℕ := {n | 0 < (actualData.zero n).im}
  let negEquiv : pos ≃ (posᶜ : Set ℕ) :=
    actualData.conjugation.subtypeEquiv (fun n => by
      change 0 < (actualData.zero n).im ↔ ¬ 0 < (actualData.zero (actualData.conjugation n)).im
      rw [actualData.zero_conjugation, Complex.conj_im, not_lt, neg_nonpos]
      have hn : (actualData.zero n).im ≠ 0 := abs_pos.mp
        ((by norm_num : (0 : ℝ) < 10).trans
          (actual_height_gt_ten _ (actualData.zero_isNontrivial n)))
      exact ⟨le_of_lt, fun hh => lt_of_le_of_ne hh (Ne.symm hn)⟩)
  let posEquiv : pos ≃ PositiveZetaZero :=
    ((zeroEquiv actualData).subtypeEquivOfSubtype
      (p := fun z => 0 < z.val.im)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter Zeta23.IsNontrivialZero (fun z => 0 < z.im))
  have hpair (n : pos) : term (negEquiv n).val = term n.val := by
    change term (actualData.conjugation n.val) = term n.val
    simp only [term, actualData.multiplicity_conjugation, actualData.zero_conjugation, hconj]
  have hneg : (∑' n : (posᶜ : Set ℕ), term n.val) = ∑' n : pos, term n.val :=
    (negEquiv.tsum_eq _).symm.trans (tsum_congr hpair)
  have hpos : (∑' n : pos, term n.val) =
      ∑' p : PositiveZetaZero, (Zeta23.zeroMult p.val : ℝ) * f p.val := by
    rw [← posEquiv.tsum_eq (fun p : PositiveZetaZero => (Zeta23.zeroMult p.val : ℝ) * f p.val)]
    exact tsum_congr (fun n => by
      change term n.val =
        (Zeta23.zeroMult (actualData.zero n.val) : ℝ) * f (actualData.zero n.val)
      simp only [term, multiplicity_eq_zeroMult])
  calc
    _ = ∑' p : ActualZeroOccurrence, f (actualData.zero p.1) := actualOccurrenceEquiv.tsum_eq _
    _ = ∑' n : ℕ, term n := by
      rw [hocc.tsum_sigma]
      simp only [term, tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    _ = (∑' n : pos, term n.val) + (∑' n : (posᶜ : Set ℕ), term n.val) :=
      ((hterm.subtype pos).tsum_add_tsum_compl (hterm.subtype posᶜ)).symm
    _ = _ := by rw [hneg, hpos, two_mul]

def phaseStep (t : ℝ) (k : ℕ) : ℂ :=
  Complex.exp (((actualZero k).im * t : ℝ) * Complex.I) - 1

def occurrenceQuarter (k : ℕ) : Circle :=
  ⟨if 0 < (actualZero k).im then Complex.I else -Complex.I, by
    change _ ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm]
    split_ifs <;> simp⟩

private def positiveOccurrence (k : ℕ) : PositiveZetaZero := by
  let n := (actualOccurrenceEquiv k).1
  by_cases hp : 0 < (actualZero k).im
  · exact ⟨actualZero k, actualData.zero_isNontrivial n, hp⟩
  · refine ⟨actualData.zero (actualData.conjugation n),
      actualData.zero_isNontrivial _, ?_⟩
    rw [actualData.zero_conjugation, Complex.conj_im, neg_pos]
    have hn : (actualZero k).im ≠ 0 := abs_pos.mp
      ((by norm_num : (0 : ℝ) < 10).trans
        (actual_height_gt_ten _ (actualData.zero_isNontrivial n)))
    exact lt_of_le_of_ne (le_of_not_gt hp) hn

private def liftPositivePhase (p : PositiveZetaZero → ℂ) (k : ℕ) : ℂ :=
  if 0 < (actualZero k).im then p (positiveOccurrence k) else conj (p (positiveOccurrence k))

private theorem occurrence_quarter_cluster (hq : quarterPhase ∈ phaseHull) :
    MapClusterPt occurrenceQuarter atTop phaseOrbit := by
  classical
  apply (phaseOrbit_cluster_iff occurrenceQuarter).2
  let coePhase : (ℕ → Circle) → (ℕ → ℂ) := fun p k => (p k : ℂ)
  have hcoe : Topology.IsInducing coePhase := by
    exact Topology.IsInducing.piMap (A := fun _ : ℕ => Circle)
      (B := fun _ => ℂ) (f := fun _ z => (z : ℂ)) fun _ => Topology.IsInducing.subtypeVal
  change occurrenceQuarter ∈ closure (range phaseOrbit : Set (ℕ → Circle))
  rw [hcoe.closure_eq_preimage_closure_image (range phaseOrbit)]
  change coePhase occurrenceQuarter ∈ closure (coePhase '' range phaseOrbit)
  have hcont : Continuous liftPositivePhase := by
    apply continuous_pi
    intro k
    by_cases hp : 0 < (actualZero k).im
    · simpa only [liftPositivePhase, ite_eq_left hp] using continuous_apply (positiveOccurrence k)
    · simpa only [liftPositivePhase, ite_eq_right hp, Function.comp_def] using
        Complex.continuous_conj.comp (continuous_apply (positiveOccurrence k))
  have hquarter : liftPositivePhase quarterPhase = coePhase occurrenceQuarter := by
    funext k
    by_cases hp : 0 < (actualZero k).im <;>
      simp [liftPositivePhase, hp, quarterPhase, coePhase, occurrenceQuarter]
  have horbit (t : ℝ) :
      liftPositivePhase (ZetaOrdinateCompleteOptimizer.phaseOrbit t) = coePhase (phaseOrbit t) := by
    funext k
    by_cases hp : 0 < (actualZero k).im
    · simp [liftPositivePhase, positiveOccurrence, hp, ZetaOrdinateCompleteOptimizer.phaseOrbit,
        ordinate, coePhase, phaseOrbit, Circle.coe_exp, mul_comm t]
    · have him : (positiveOccurrence k).val.im = -(actualZero k).im := by
        unfold positiveOccurrence
        rw [dite_eq_right hp]
        change (actualData.zero (actualData.conjugation (actualOccurrenceEquiv k).1)).im = _
        rw [actualData.zero_conjugation, Complex.conj_im]
        rfl
      simp only [liftPositivePhase, ite_eq_right hp, ZetaOrdinateCompleteOptimizer.phaseOrbit,
        ordinate, him, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
        coePhase, phaseOrbit, Circle.coe_exp]
      congr 1
      push_cast
      ring
  rw [← hquarter]
  refine hcont.continuousAt.continuousWithinAt.mem_closure hq ?_
  rintro _ ⟨t, rfl⟩
  exact ⟨phaseOrbit t, mem_range_self t, (horbit t).symm⟩

theorem norm_phaseStep_le (t : ℝ) (k : ℕ) :
    ‖phaseStep t k‖ ≤ 2 := by
  exact (norm_sub_le _ _).trans_eq (by rw [Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num)

private theorem norm_phaseStep_le_linear (t : ℝ) (k : ℕ) :
    ‖phaseStep t k‖ ≤ |(actualZero k).im| * |t| := by
  simpa only [phaseStep, mul_comm _ Complex.I, Real.norm_eq_abs, abs_mul] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := (actualZero k).im * t))

theorem coeff_norm_eq_weight (hRH : RiemannHypothesis) (k : ℕ) :
    ‖actualCoeff k‖ = weight k := by
  rw [coeff_real hRH, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rfl

theorem leading_increment_summable (r t : ℝ) (p : ℕ → Circle) :
    Summable (fun k => (-(r : ℂ) * actualCoeff k) * (p k : ℂ) * phaseStep t k) := by
  refine ((actualCoeff_hasSum.summable.norm.mul_left |r|).mul_right 2).of_norm_bounded ?_
  intro k
  rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    Circle.norm_coe, mul_one]
  exact mul_le_mul_of_nonneg_left (norm_phaseStep_le t k) (by positivity)

theorem quarter_sine_hasSum (hRH : RiemannHypothesis) (r t : ℝ) :
    HasSum (fun k : ℕ => r * weight k * Real.sin (|(actualZero k).im| * t)) (r * slope t) ∧
    (∑' k, (-(r : ℂ) * actualCoeff k) * (occurrenceQuarter k : ℂ) * phaseStep t k).re =
      r * slope t := by
  let f := fun z : ℂ => r * (1 / (1 / 4 + z.im ^ 2)) * Real.sin (|z.im| * t)
  let F := fun k : ℕ => (-(r : ℂ) * actualCoeff k) * (occurrenceQuarter k : ℂ) * phaseStep t k
  have hs : Summable F := leading_increment_summable r t occurrenceQuarter
  have hreal (k : ℕ) : (F k).re = f (actualZero k) := by
    dsimp only [F, f, occurrenceQuarter, phaseStep]
    rw [coeff_real hRH]
    by_cases hp : 0 < (actualZero k).im
    · rw [ite_eq_left hp, abs_of_pos hp]
      simp only [Complex.mul_re, Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
        Complex.one_im, Complex.exp_ofReal_mul_I_im]
      ring
    · have hnp := le_of_not_gt hp
      have harg : (-(actualZero k).im) * t = -((actualZero k).im * t) := by ring
      rw [ite_eq_right hp, abs_of_nonpos hnp, harg, Real.sin_neg]
      simp only [Complex.mul_re, Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
        Complex.one_im, Complex.exp_ofReal_mul_I_im]
      ring
  have hconj (z : ℂ) : f (conj z) = f z := by simp [f, Complex.conj_im, abs_neg]
  have hsum := (Complex.hasSum_re hs.hasSum).congr_fun (fun k => (hreal k).symm)
  have hvalue : (∑' k : ℕ, F k).re = r * slope t := by
    rw [← hsum.tsum_eq, tsum_occurrences_eq_twice_positive f hconj hsum.summable,
      ZetaOrdinatePhaseStiffness.slope, phaseSlope, ← tsum_mul_left, ← tsum_mul_left]
    apply tsum_congr
    intro p
    have hp : 0 < ordinate p := p.property.2
    dsimp only [f, ZetaOrdinatePhaseStiffness.weight, phaseWeight,
      ZetaOrdinatePhaseStiffness.multiplicity, ordinate] at *
    rw [abs_of_pos hp]
    field_simp [ne_of_gt hp]
  exact ⟨hvalue ▸ hsum, hvalue⟩

def increment (r t : ℝ) (p : ℕ → Circle) : ℝ :=
  readSignal r (r * t) p - readSignal r 0 p

private theorem increment_eq (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 < r)
    (t : ℝ) (p : ℕ → Circle) :
    increment r t p =
      (∑' k, rootCoeff r k * (p k : ℂ) * phaseStep t k).re / (1 / 2 - (2 * r)⁻¹) := by
  have hs (v : ℝ) :
      Summable (fun k => rootCoeff r k * (p k : ℂ) * Complex.exp (frequency k * (v : ℂ))) := by
    apply Summable.of_norm_bounded (actualCoeff_hasSum.summable.norm.mul_left r)
    intro k
    simpa only [norm_mul, Circle.norm_coe, exp_mode_norm hRH, mul_one] using rootCoeff_bound hr k
  have hrt : r * t / r = t := by field_simp
  have hsub := ((hs t).hasSum.sub (hs 0).hasSum).tsum_eq
  unfold increment readSignal
  rw [hrt, zero_div, ← sub_div, ← Complex.sub_re, ← hsub]
  congr 2
  apply tsum_congr
  intro k
  rw [← mul_sub, ← phaseOrbit_eq_mode hRH]
  simp only [phaseOrbit, Circle.coe_exp, phaseStep, mul_comm t, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero]

theorem increment_close_to_leading (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 < r)
    (t : ℝ) (p : ℕ → Circle) :
    let s : ℝ := 1 / 2 - (2 * r)⁻¹
    |s * increment r t p -
      (∑' k, (-(r : ℂ) * actualCoeff k) * (p k : ℂ) * phaseStep t k).re| ≤
        (r * (r - 1) * ∑' k, ‖actualCoeff k‖) * |t| := by
  dsimp only
  have hs : 0 < 1 / 2 - (2 * r)⁻¹ := by
    rw [inv_eq_one_div, sub_pos]
    exact (div_lt_iff₀ (by positivity)).2 (by linarith)
  have hroot : Summable (fun k => rootCoeff r k * (p k : ℂ) * phaseStep t k) := by
    refine ((actualCoeff_hasSum.summable.norm.mul_left r).mul_right 2).of_norm_bounded ?_
    intro k
    rw [norm_mul, norm_mul, Circle.norm_coe, mul_one]
    exact (mul_le_mul_of_nonneg_left (norm_phaseStep_le t k) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (rootCoeff_bound hr k) (by norm_num))
  rw [increment_eq hRH hr, ← mul_div_assoc, mul_comm (1 / 2 - (2 * r)⁻¹),
    mul_div_cancel_right₀ _ hs.ne', ← Complex.sub_re,
    ← hroot.tsum_sub (leading_increment_summable r t p)]
  apply (Complex.abs_re_le_norm _).trans
  have hmass := ((actualCoeff_hasSum.summable.norm.hasSum.mul_left (r * (r - 1))).mul_right |t|)
  refine tsum_of_norm_bounded hmass fun k => ?_
  rw [← sub_mul, ← sub_mul, neg_mul, sub_neg_eq_add, norm_mul, norm_mul, Circle.norm_coe, mul_one]
  calc
    _ ≤ ‖rootCoeff r k + (r : ℂ) * actualCoeff k‖ * (|(actualZero k).im| * |t|) :=
      mul_le_mul_of_nonneg_left (norm_phaseStep_le_linear t k) (norm_nonneg _)
    _ = (|(actualZero k).im| * ‖rootCoeff r k + (r : ℂ) * actualCoeff k‖) * |t| := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (weighted_coeff_error hr k) (abs_nonneg _)

private theorem norm_phaseStep_le_sine_cosine {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ‖phaseStep t k‖ ≤ Real.sin (|(actualZero k).im| * t) +
      (1 - Real.cos ((actualZero k).im * t)) +
        (if t⁻¹ < |(actualZero k).im| then 2 else 0) := by
  let x := (actualZero k).im * t
  have hx : |x| = |(actualZero k).im| * t := by rw [abs_mul, abs_of_pos ht]
  have h := Complex.norm_le_abs_re_add_abs_im (phaseStep t k)
  simp only [phaseStep, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, sub_zero] at h
  change ‖phaseStep t k‖ ≤ |Real.cos x - 1| + |Real.sin x| at h
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one x))] at h
  apply h.trans
  by_cases hk : t⁻¹ < |(actualZero k).im|
  · rw [ite_eq_left hk]
    linarith [Real.abs_sin_le_one x, Real.neg_one_le_sin (|(actualZero k).im| * t)]
  · rw [ite_eq_right hk, add_zero]
    have hxone : |x| ≤ 1 := by
      rw [hx, ← le_div_iff₀ ht, one_div]
      exact le_of_not_gt hk
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (hxone.trans (by linarith [Real.pi_gt_three])), hx]
    exact le_of_eq (add_comm ..)

theorem weight_le_inverse_square (k : ℕ) :
    weight k ≤ (actualZero k).im⁻¹ ^ 2 := by
  have hz : (actualZero k).im ≠ 0 :=
    abs_pos.mp ((by norm_num : (0 : ℝ) < 10).trans
      (actual_height_gt_ten _ (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)))
  rw [weight, inv_pow, ← one_div]
  exact div_le_div_of_nonneg_left zero_le_one (sq_pos_of_ne_zero hz)
    (le_add_of_nonneg_left (by norm_num))

private theorem leading_increment_upper (hRH : RiemannHypothesis) {r t B : ℝ} (hr : 0 < r)
    (ht : 0 < t)
    (htail : (∑' k : ℕ, if t⁻¹ < |(actualZero k).im| then (actualZero k).im⁻¹ ^ 2 else 0) ≤
      B * (1 + Real.log t⁻¹) / t⁻¹) (p : ℕ → Circle) :
    |(∑' k, (-(r : ℂ) * actualCoeff k) * (p k : ℂ) * phaseStep t k).re| ≤
      r * slope t + r * (K 0 - K t) + 2 * r * (B * (1 + Real.log t⁻¹) / t⁻¹) := by
  let high (k : ℕ) := if t⁻¹ < |(actualZero k).im| then (actualZero k).im⁻¹ ^ 2 else 0
  have hinv : Summable (fun k : ℕ => (actualZero k).im⁻¹ ^ 2) := by
    simpa only [Function.comp_def, actualZero] using
      actualOccurrenceEquiv.summable_iff.mpr actual_sigma_inverse_square_summable
  have hhigh : Summable high := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hinv
    · unfold high
      split_ifs <;> positivity
    · unfold high
      split_ifs
      · exact le_rfl
      · positivity
  have hsin := (quarter_sine_hasSum hRH r t).1
  have hcos : HasSum (fun k : ℕ => r * weight k * (1 - Real.cos ((actualZero k).im * t)))
      (r * (K 0 - K t)) := by
    convert ((cosine_difference_hasSum hRH t).mul_left (-r / 2)) using 1
    · funext k
      ring
    · ring
  apply (Complex.abs_re_le_norm _).trans
  refine (tsum_of_norm_bounded ((hsin.add hcos).add (hhigh.hasSum.mul_left (2 * r))) ?_).trans ?_
  · intro k
    rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      coeff_norm_eq_weight hRH, Circle.norm_coe, mul_one]
    have hw : 0 ≤ r * weight k := by unfold weight; positivity
    apply (mul_le_mul_of_nonneg_left (norm_phaseStep_le_sine_cosine ht k) hw).trans
    change r * weight k * (_ + _ + _) ≤
      r * weight k * Real.sin (|(actualZero k).im| * t) +
        r * weight k * (1 - Real.cos ((actualZero k).im * t)) + 2 * r * high k
    rw [mul_add, mul_add]
    apply add_le_add_right
    dsimp only [high]
    split_ifs
    · nlinarith only [mul_le_mul_of_nonneg_left (weight_le_inverse_square k) hr.le]
    · simp
  · exact add_le_add_right (mul_le_mul_of_nonneg_left htail (show 0 ≤ 2 * r by positivity)) _

private theorem origin_cosine_bound {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 2) :
    K 0 - K t ≤ (|c| + 2) * (t * (1 + Real.log t⁻¹)) := by
  have hlog : 0 ≤ Real.log t⁻¹ := Real.log_nonneg (one_le_inv₀ ht |>.mpr (by linarith))
  have hR := (abs_le.mp (cusp_remainder_bound ht ht')).1
  unfold R at hR
  have hlt : Real.log t = -Real.log t⁻¹ := by rw [Real.log_inv, neg_neg]
  rw [← K_zero, hlt] at hR
  have hc := mul_le_mul_of_nonneg_right (neg_abs_le c) ht.le
  have hquad := mul_nonneg ht.le (show 0 ≤ 1 - 2 * t by linarith)
  have hextra := mul_nonneg (show 0 ≤ (|c| + 2) - 1 / 2 by linarith [abs_nonneg c])
    (mul_nonneg ht.le hlog)
  nlinarith only [hR, hc, hquad, hextra, mul_nonneg ht.le (abs_nonneg c)]

/-- The full forward root increment has a uniform leading upper bound under RH.
At the quarter phase, the same leading term is approached with positive sign arbitrarily late. -/
theorem root_signal_quarter_phase_increment (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 < r) :
    let s : ℝ := 1 / 2 - (2 * r)⁻¹
    let P := fun t : ℝ => r / (2 * Real.pi * s) * t * (Real.log t⁻¹) ^ 2
    ∃ A C : ℝ, 2 ≤ A ∧ 0 ≤ C ∧ ∀ t : ℝ, 0 < t → A * t ≤ 1 →
      (∀ u : ℝ, |rootSignal r (u + r * t) - rootSignal r u| ≤
        P t + C * t * (1 + Real.log t⁻¹)) ∧
      (quarterPhase ∈ phaseHull → ∀ U b : ℝ, b < P t - C * t * (1 + Real.log t⁻¹) →
        ∃ u ≥ U, b < rootSignal r (u + r * t) - rootSignal r u) := by
  dsimp only
  let s : ℝ := 1 / 2 - (2 * r)⁻¹
  let P (t : ℝ) := r / (2 * Real.pi * s) * t * (Real.log t⁻¹) ^ 2
  let D := r * (r - 1) * ∑' k, ‖actualCoeff k‖
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hs : 0 < s := by
    dsimp only [s]
    rw [inv_eq_one_div, sub_pos]
    exact (div_lt_iff₀ (by positivity)).2 (by linarith)
  have hD : 0 ≤ D :=
    mul_nonneg (mul_nonneg hr0.le (sub_nonneg.mpr hr.le)) (tsum_nonneg fun _ => norm_nonneg _)
  obtain ⟨A, B, hA, hB, hslope⟩ := ZetaOrdinatePhaseStiffness.actual_zeta_phase_stiffness.2.2.2.2
  obtain ⟨Btail, hBtail, htail⟩ := actual_high_weight
  let C := (D + r * B + r * (|c| + 2) + 2 * r * Btail) / s
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨A, C, hA, hC, fun t ht htA => ?_⟩
  let E := t * (1 + Real.log t⁻¹)
  have ht' : t ≤ 1 / 2 := by nlinarith [mul_le_mul_of_nonneg_right hA ht.le]
  have hinv : 2 ≤ t⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ ht]
    linarith
  have hlog : 0 ≤ Real.log t⁻¹ := Real.log_nonneg (by linarith)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hDt : D * t ≤ D * E := by
    apply mul_le_mul_of_nonneg_left _ hD
    dsimp only [E]
    nlinarith [mul_nonneg ht.le hlog]
  have hslope' := (hslope t (by rwa [abs_of_pos ht]) (by rwa [abs_of_pos ht])).2
  rw [abs_of_pos ht] at hslope'
  have hscale := mul_le_mul_of_nonneg_left (abs_le.mp hslope').2 hr0.le
  have hscale' := mul_le_mul_of_nonneg_left (abs_le.mp hslope').1 hr0.le
  have hP : s * P t = r * ((1 / (2 * Real.pi)) * t * (Real.log t⁻¹) ^ 2) := by
    dsimp only [P]
    field_simp [hs.ne', Real.pi_ne_zero]
  have horbit (x : ℝ) :
      increment r t (phaseOrbit x) = rootSignal r (r * x + r * t) - rootSignal r (r * x) := by
    simp only [increment, read_signal_orbit hRH hr, add_zero]
  have hupper (p : ℕ → Circle) : |increment r t p| ≤ P t + C * E := by
    let leading := (∑' k, (-(r : ℂ) * actualCoeff k) * (p k : ℂ) * phaseStep t k).re
    have htriangle : |s * increment r t p| ≤ |s * increment r t p - leading| + |leading| := by
      simpa only [sub_add_cancel] using abs_add_le (s * increment r t p - leading) leading
    have herr := increment_close_to_leading hRH hr t p
    change |s * increment r t p - leading| ≤ D * |t| at herr
    rw [abs_of_pos ht] at herr
    have hlead := leading_increment_upper hRH hr0 ht (htail t⁻¹ hinv) p
    change |leading| ≤ _ at hlead
    have hcos := mul_le_mul_of_nonneg_left (origin_cosine_bound ht ht') hr0.le
    have htail' : Btail * (1 + Real.log t⁻¹) / t⁻¹ = Btail * E := by
      rw [div_eq_mul_inv, inv_inv]
      dsimp only [E]
      ring
    rw [htail'] at hlead
    apply le_of_mul_le_mul_left _ hs
    rw [← abs_of_pos hs, ← abs_mul, abs_of_pos hs, mul_add, hP]
    have hCE : s * (C * E) = (D + r * B + r * (|c| + 2) + 2 * r * Btail) * E := by
      dsimp only [C]
      field_simp [hs.ne']
    rw [hCE]
    dsimp only [E] at hDt hlead hcos ⊢
    nlinarith only [htriangle, herr, hDt, hlead, hcos, hscale]
  have hlower : P t - C * E ≤ increment r t occurrenceQuarter := by
    have herr := increment_close_to_leading hRH hr t occurrenceQuarter
    rw [(quarter_sine_hasSum hRH r t).2, abs_of_pos ht] at herr
    change |s * increment r t occurrenceQuarter - r * slope t| ≤ D * t at herr
    have hlo := (abs_le.mp herr).1
    apply le_of_mul_le_mul_left _ hs
    rw [mul_sub, hP]
    have hCE : s * (C * E) = (D + r * B + r * (|c| + 2) + 2 * r * Btail) * E := by
      dsimp only [C]
      field_simp [hs.ne']
    rw [hCE]
    have hrest := mul_nonneg (show 0 ≤ r * (|c| + 2) + 2 * r * Btail by positivity) hE
    dsimp only [E] at hDt hrest ⊢
    nlinarith only [hlo, hDt, hscale', hrest]
  constructor
  · intro u
    have hu : r * (u / r) = u := by field_simp
    simpa only [horbit, hu, P, E, s, mul_assoc] using hupper (phaseOrbit (u / r))
  · intro hq U b hb
    have hcont : Continuous (increment r t) :=
      (read_signal_continuous hRH hr (r * t)).sub (read_signal_continuous hRH hr 0)
    have hb₀ : b < P t - C * E := by simpa only [P, E, s, mul_assoc] using hb
    have hb' := hb₀.trans_le hlower
    have hreturn := ((occurrence_quarter_cluster hq).continuousAt_comp hcont.continuousAt).frequently
      (eventually_gt_nhds hb')
    obtain ⟨x, hx, hlate⟩ := (hreturn.and_eventually (eventually_ge_atTop (U / r))).exists
    refine ⟨r * x, ((div_le_iff₀ hr0).1 hlate).trans_eq (mul_comm _ _), ?_⟩
    simpa only [Function.comp_apply, horbit] using hx

#print axioms root_signal_quarter_phase_increment

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
