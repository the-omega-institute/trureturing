/- GID: D5/S3/Arith/Robin/ForwardKernel/MovingEndpointVariance
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MovingEndpointVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Comparable variances control increments between increasing moving endpoints. -/

import D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Topology.Order.ProjIcc

/-! Uniform square bounds for increments between two moving endpoints. -/

namespace D5.S3.Arith.Robin.ForwardKernel.MovingEndpointVariance

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs VarianceTransfer

noncomputable section

private lemma moving_shift_integral_le {E p p' : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) {l r Y m : ℝ}
    (hlr : l ≤ r) (hm : 0 < m) (hp : Continuous p)
    (hdp : ∀ x ∈ Icc l r, HasDerivWithinAt p (p' x) (Icc l r) x)
    (hlp : ∀ x ∈ Icc l r, m ≤ p' x)
    (himage : ∀ x ∈ Icc l r, p x ∈ Icc (1 : ℝ) Y) (w : ℝ) :
    (∫ x in l..r, increment E w (p x) ^ 2) ≤ cumulativeVariance E Y w / m := by
  have hinj : InjOn p (Icc l r) :=
    (strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc l r) hp.continuousOn
      (fun x hx => (hdp x (interior_subset hx)).mono interior_subset)
      (fun x hx => hm.trans_le (hlp x (interior_subset hx)))).injOn
  have hsub : p '' Icc l r ⊆ Icc (1 : ℝ) Y := by
    rintro _ ⟨x, hx, rfl⟩
    exact himage x hx
  have hY : 1 ≤ Y := (himage l ⟨le_rfl, hlr⟩).1.trans (himage l ⟨le_rfl, hlr⟩).2
  have hi : IntegrableOn (fun y => increment E w y ^ 2) (Icc (1 : ℝ) Y) := by
    simpa only [pow_two, id_eq] using
      increment_product_comp_integrableOn hE isCompact_Icc
        continuous_const continuous_id continuous_const continuous_id
  have hiweighted := (integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Icc hdp hinj (fun y => increment E w y ^ 2)).mp (hi.mono_set hsub)
  have hip : IntegrableOn (fun x => increment E w (p x) ^ 2) (Icc l r) := by
    simpa only [pow_two] using increment_product_comp_integrableOn hE isCompact_Icc
      continuous_const hp continuous_const hp
  apply (le_div_iff₀ hm).mpr
  rw [mul_comm, intervalIntegral.integral_of_le hlr, ← integral_Icc_eq_integral_Ioc,
    ← integral_const_mul]
  calc
    _ ≤ ∫ x in Icc l r, |p' x| • increment E w (p x) ^ 2 := by
      apply setIntegral_mono_on (hip.const_mul m) hiweighted measurableSet_Icc
      intro x hx
      rw [smul_eq_mul, abs_of_nonneg (hm.le.trans (hlp x hx))]
      exact mul_le_mul_of_nonneg_right (hlp x hx) (sq_nonneg _)
    _ = ∫ y in p '' Icc l r, increment E w y ^ 2 :=
      (integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hdp hinj
        (fun y => increment E w y ^ 2)).symm
    _ ≤ ∫ y in Icc (1 : ℝ) Y, increment E w y ^ 2 :=
      setIntegral_mono_set hi (Eventually.of_forall (fun _ => sq_nonneg _))
        (Eventually.of_forall hsub)
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hY]
      rfl

private lemma averaged_variance_integral_le {E p p' : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) {l r Y m a b K : ℝ}
    (hlr : l ≤ r) (hab : a ≤ b) (hm : 0 < m) (hp : Continuous p)
    (hdp : ∀ x ∈ Icc l r, HasDerivWithinAt p (p' x) (Icc l r) x)
    (hlp : ∀ x ∈ Icc l r, m ≤ p' x)
    (himage : ∀ x ∈ Icc l r, p x ∈ Icc (1 : ℝ) Y)
    (hV : ∀ w ∈ Icc a b, cumulativeVariance E Y w ≤ K) :
    IntervalIntegrable (fun x => ∫ w in a..b, increment E w (p x) ^ 2) volume l r ∧
    (∫ x in l..r, ∫ w in a..b, increment E w (p x) ^ 2) ≤ (b - a) * (K / m) := by
  have hr : Integrable (fun z : ℝ × ℝ => increment E z.2 (p z.1) ^ 2)
      ((volume.restrict (Ioc l r)).prod (volume.restrict (Ioc a b))) := by
    rw [Measure.prod_restrict]
    have hi := increment_product_comp_integrableOn (μ := volume.prod volume) hE
      (K := Icc l r ×ˢ Icc a b) (isCompact_Icc.prod isCompact_Icc)
      continuous_snd (hp.comp continuous_fst) continuous_snd (hp.comp continuous_fst)
    simpa only [pow_two, IntegrableOn, Function.comp_apply] using
      hi.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlr]
    simpa only [IntegrableOn, intervalIntegral.integral_of_le hab] using hr.integral_prod_left
  · simp_rw [intervalIntegral.integral_of_le hlr, intervalIntegral.integral_of_le hab]
    rw [integral_integral_swap hr]
    calc
      _ ≤ ∫ _w in Ioc a b, K / m := by
        apply setIntegral_mono_on hr.integral_prod_right (integrableOn_const (by simp))
          measurableSet_Ioc
        intro w hw
        rw [← intervalIntegral.integral_of_le hlr]
        exact (moving_shift_integral_le hE hlr hm hp hdp hlp himage w).trans
          (div_le_div_of_nonneg_right (hV w ⟨hw.1.le, hw.2⟩) hm.le)
      _ = _ := by
        rw [setIntegral_const, Measure.real, Real.volume_Ioc,
          ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul]

private lemma averaged_increment_square_le {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) {h L C₀ : ℝ} (hh : 0 < h)
    (hL : L ∈ Icc (0 : ℝ) (C₀ * h)) (x : ℝ) :
    h * increment E L x ^ 2 ≤
      2 * (∫ v in ((C₀ + 1) * h)..((C₀ + 2) * h), increment E v x ^ 2) +
      2 * (∫ w in h..((C₀ + 2) * h), increment E w (x + L) ^ 2) := by
  have hi (a b y : ℝ) : IntervalIntegrable (fun v => increment E v y ^ 2) volume a b := by
    simpa only [pow_two, id_eq] using
      (increment_product_comp_integrableOn hE isCompact_uIcc
        continuous_id continuous_const continuous_id continuous_const).intervalIntegrable
  have hishift : IntervalIntegrable (fun v => increment E (v - L) (x + L) ^ 2)
      volume ((C₀ + 1) * h) ((C₀ + 2) * h) := by
    simpa only [pow_two, Pi.sub_apply, id_eq] using
      (increment_product_comp_integrableOn hE isCompact_uIcc
        (continuous_id.sub continuous_const) continuous_const
        (continuous_id.sub continuous_const) continuous_const).intervalIntegrable
  have hpoint (v : ℝ) : increment E L x ^ 2 ≤
      2 * increment E v x ^ 2 + 2 * increment E (v - L) (x + L) ^ 2 := by
    have hid : increment E L x = increment E v x - increment E (v - L) (x + L) := by
      unfold increment
      rw [show x + L + (v - L) = x + v by ring]
      ring
    rw [hid]
    simpa only [sub_eq_add_neg, neg_sq, mul_add] using
      (add_sq_le (a := increment E v x) (b := -increment E (v - L) (x + L)))
  have hm := intervalIntegral.integral_mono_on (by linarith : (C₀ + 1) * h ≤ (C₀ + 2) * h)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => increment E L x ^ 2)
      volume ((C₀ + 1) * h) ((C₀ + 2) * h))
    (((hi _ _ _).const_mul 2).add (hishift.const_mul 2)) (fun v _ => hpoint v)
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    ((hi _ _ _).const_mul 2) (hishift.const_mul 2)] at hm
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul] at hm
  have htrans : (∫ v in ((C₀ + 1) * h)..((C₀ + 2) * h), increment E (v - L) (x + L) ^ 2) =
      ∫ w in ((C₀ + 1) * h - L)..((C₀ + 2) * h - L), increment E w (x + L) ^ 2 := by
    simpa only [sub_eq_add_neg] using intervalIntegral.integral_comp_add_right
      (fun w : ℝ => increment E w (x + L) ^ 2) (-L)
  have hmono := intervalIntegral.integral_mono_interval (by linarith [hL.2] : h ≤ (C₀ + 1) * h - L)
    (by linarith : (C₀ + 1) * h - L ≤ (C₀ + 2) * h - L)
    (by linarith [hL.1] : (C₀ + 2) * h - L ≤ (C₀ + 2) * h)
    (Eventually.of_forall (fun _ => sq_nonneg _)) (hi h ((C₀ + 2) * h) (x + L))
  rw [htrans] at hm
  nlinarith

/-- A variance bound on comparable lengths controls increments between two moving endpoints. -/
theorem two_endpoint_increment_square_le
    {E p q p' q' : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E)
    {l r Y R C₀ m K : ℝ}
    (hlr : l ≤ r)
    (hR : 0 < R) (hC₀ : 0 ≤ C₀)
    (hm : 0 < m) (hK : 0 ≤ K)
    (hp : ContinuousOn p (Icc l r))
    (hq : ContinuousOn q (Icc l r))
    (hdp : ∀ x ∈ Icc l r,
      HasDerivWithinAt p (p' x) (Icc l r) x)
    (hdq : ∀ x ∈ Icc l r,
      HasDerivWithinAt q (q' x) (Icc l r) x)
    (hlp : ∀ x ∈ Icc l r, m ≤ p' x)
    (hlq : ∀ x ∈ Icc l r, m ≤ q' x)
    (himage : ∀ x ∈ Icc l r,
      p x ∈ Icc (1 : ℝ) Y ∧ q x ∈ Icc (1 : ℝ) Y)
    (hgap : ∀ x ∈ Icc l r,
      q x - p x ∈ Icc (0 : ℝ) (C₀ * R))
    (hV : ∀ u ∈ Icc R ((C₀ + 2) * R),
      cumulativeVariance E Y u ≤ K) :
    (∫ x in l..r, (E (q x) - E (p x)) ^ 2) ≤
      (2 * (C₀ + 2) / m) * K := by
  let P : ℝ → ℝ := fun x => p (projIcc l r hlr x)
  let Q : ℝ → ℝ := fun x => q (projIcc l r hlr x)
  have hP : Continuous P := hp.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun x => (projIcc l r hlr x).property)
  have hQ : Continuous Q := hq.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun x => (projIcc l r hlr x).property)
  have hPeq : EqOn P p (Icc l r) := fun x hx => by simp [P, projIcc_of_mem hlr hx]
  have hQeq : EqOn Q q (Icc l r) := fun x hx => by simp [Q, projIcc_of_mem hlr hx]
  have hdP : ∀ x ∈ Icc l r, HasDerivWithinAt P (p' x) (Icc l r) x :=
    fun x hx => (hdp x hx).congr_of_mem hPeq hx
  have hdQ : ∀ x ∈ Icc l r, HasDerivWithinAt Q (q' x) (Icc l r) x :=
    fun x hx => (hdq x hx).congr_of_mem hQeq hx
  have hPi : ∀ x ∈ Icc l r, P x ∈ Icc (1 : ℝ) Y := by
    intro x hx; rw [hPeq hx]; exact (himage x hx).1
  have hQi : ∀ x ∈ Icc l r, Q x ∈ Icc (1 : ℝ) Y := by
    intro x hx; rw [hQeq hx]; exact (himage x hx).2
  have hgap' : ∀ x ∈ Icc l r, Q x - P x ∈ Icc (0 : ℝ) (C₀ * R) := by
    intro x hx; rw [hPeq hx, hQeq hx]; exact hgap x hx
  have hab : (C₀ + 1) * R ≤ (C₀ + 2) * R := by nlinarith
  have hac : R ≤ (C₀ + 2) * R := by nlinarith
  obtain ⟨hi1, hb1⟩ := averaged_variance_integral_le hE hlr hab hm hP hdP hlp hPi
    (fun w hw => hV w ⟨by nlinarith [hw.1], hw.2⟩)
  obtain ⟨hi2, hb2⟩ := averaged_variance_integral_le hE hlr hac hm hQ hdQ hlq hQi hV
  have hi : IntervalIntegrable (fun x => increment E (Q x - P x) (P x) ^ 2)
      volume l r := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hlr]
    simpa only [pow_two, Pi.sub_apply] using increment_product_comp_integrableOn hE isCompact_Icc
      (hQ.sub hP) hP (hQ.sub hP) hP
  have hav := intervalIntegral.integral_mono_on hlr (hi.const_mul R)
    ((hi1.const_mul 2).add (hi2.const_mul 2)) (by
      intro x hx
      simpa only [show P x + (Q x - P x) = Q x by ring] using
        averaged_increment_square_le hE hR (hgap' x hx) (P x))
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hi1.const_mul 2) (hi2.const_mul 2)] at hav
  simp only [intervalIntegral.integral_const_mul] at hav
  have hbound : (∫ x in l..r, increment E (Q x - P x) (P x) ^ 2) ≤
      (2 * (C₀ + 2) / m) * K := by
    apply le_of_mul_le_mul_left (a := R) _ hR
    calc
      _ ≤ 2 * (((C₀ + 2) * R - (C₀ + 1) * R) * (K / m)) +
          2 * (((C₀ + 2) * R - R) * (K / m)) := by linarith
      _ = _ := by ring
  convert hbound using 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hlr] at hx
  simp only [increment, hPeq hx, hQeq hx, add_sub_cancel]

end
end D5.S3.Arith.Robin.ForwardKernel.MovingEndpointVariance
