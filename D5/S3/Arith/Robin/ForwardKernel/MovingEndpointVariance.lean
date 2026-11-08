/- GID: D5/S3/Arith/Robin/ForwardKernel/MovingEndpointVariance
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MovingEndpointVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local variances control signed increments between increasing endpoints. -/

import D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Topology.Order.ProjIcc

/-! Shared averaging gives cumulative and local square bounds between two moving endpoints. -/

namespace D5.S3.Arith.Robin.ForwardKernel.MovingEndpointVariance

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs VarianceTransfer

noncomputable section

private lemma moving_shift_integral_le {E p p' : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) {l r A B m : ℝ}
    (hlr : l ≤ r) (hm : 0 < m) (hp : Continuous p)
    (hdp : ∀ x ∈ Icc l r, HasDerivWithinAt p (p' x) (Icc l r) x)
    (hlp : ∀ x ∈ Icc l r, m ≤ p' x)
    (himage : ∀ x ∈ Icc l r, p x ∈ Icc A B) (w : ℝ) :
    (∫ x in l..r, increment E w (p x) ^ 2) ≤ (∫ y in A..B, increment E w y ^ 2) / m := by
  have hinj : InjOn p (Icc l r) :=
    (strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc l r) hp.continuousOn
      (fun x hx => (hdp x (interior_subset hx)).mono interior_subset)
      (fun x hx => hm.trans_le (hlp x (interior_subset hx)))).injOn
  have hsub : p '' Icc l r ⊆ Icc A B := by
    rintro _ ⟨x, hx, rfl⟩
    exact himage x hx
  have hAB : A ≤ B := (himage l ⟨le_rfl, hlr⟩).1.trans (himage l ⟨le_rfl, hlr⟩).2
  have hi : IntegrableOn (fun y => increment E w y ^ 2) (Icc A B) := by
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
    _ ≤ ∫ y in Icc A B, increment E w y ^ 2 :=
      setIntegral_mono_set hi (Eventually.of_forall (fun _ => sq_nonneg _))
        (Eventually.of_forall hsub)
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hAB]

private lemma averaged_variance_integral_le {E p p' : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) {l r A B m a b : ℝ} {F : ℝ → ℝ}
    (hlr : l ≤ r) (hab : a ≤ b) (hm : 0 < m) (hp : Continuous p)
    (hdp : ∀ x ∈ Icc l r, HasDerivWithinAt p (p' x) (Icc l r) x)
    (hlp : ∀ x ∈ Icc l r, m ≤ p' x)
    (himage : ∀ x ∈ Icc l r, p x ∈ Icc A B)
    (hF : IntervalIntegrable F volume a b)
    (hV : ∀ w ∈ Icc a b, (∫ y in A..B, increment E w y ^ 2) ≤ F w) :
    IntervalIntegrable (fun x => ∫ w in a..b, increment E w (p x) ^ 2) volume l r ∧
    (∫ x in l..r, ∫ w in a..b, increment E w (p x) ^ 2) ≤ (∫ w in a..b, F w) / m := by
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
      _ ≤ ∫ w in Ioc a b, F w / m := by
        apply setIntegral_mono_on hr.integral_prod_right
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hF.div_const m))
          measurableSet_Ioc
        intro w hw
        rw [← intervalIntegral.integral_of_le hlr]
        exact (moving_shift_integral_le hE hlr hm hp hdp hlp himage w).trans
          (div_le_div_of_nonneg_right (hV w ⟨hw.1.le, hw.2⟩) hm.le)
      _ = _ := by
        rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_div,
          intervalIntegral.integral_of_le hab]

private lemma averaged_increment_square_le {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) {L a b c d : ℝ} (hab : a ≤ b)
    (hleft : c ≤ a - L) (hright : b - L ≤ d) (x : ℝ) :
    (b - a) * increment E L x ^ 2 ≤
      2 * (∫ v in a..b, increment E v x ^ 2) +
      2 * (∫ w in c..d, increment E w (x + L) ^ 2) := by
  have hi (a b y : ℝ) : IntervalIntegrable (fun v => increment E v y ^ 2) volume a b := by
    simpa only [pow_two, id_eq] using
      (increment_product_comp_integrableOn hE isCompact_uIcc
        continuous_id continuous_const continuous_id continuous_const).intervalIntegrable
  have hishift : IntervalIntegrable (fun v => increment E (v - L) (x + L) ^ 2)
      volume a b := by
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
  have hm := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => increment E L x ^ 2)
      volume a b)
    (((hi _ _ _).const_mul 2).add (hishift.const_mul 2)) (fun v _ => hpoint v)
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    ((hi _ _ _).const_mul 2) (hishift.const_mul 2)] at hm
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul] at hm
  have htrans : (∫ v in a..b, increment E (v - L) (x + L) ^ 2) =
      ∫ w in (a - L)..(b - L), increment E w (x + L) ^ 2 := by
    simpa only [sub_eq_add_neg] using intervalIntegral.integral_comp_add_right
      (fun w : ℝ => increment E w (x + L) ^ 2) (-L)
  have hmono := intervalIntegral.integral_mono_interval hleft (sub_le_sub_right hab L) hright
    (Eventually.of_forall (fun _ => sq_nonneg _)) (hi c d (x + L))
  rw [htrans] at hm
  nlinarith

private lemma two_endpoint_integral_average_le
    {E p q p' q' F : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {l r A B m a b c d : ℝ}
    (hlr : l ≤ r) (hab : a ≤ b) (hcd : c ≤ d) (hm : 0 < m)
    (hp : ContinuousOn p (Icc l r)) (hq : ContinuousOn q (Icc l r))
    (hdp : ∀ x ∈ Icc l r, HasDerivWithinAt p (p' x) (Icc l r) x)
    (hdq : ∀ x ∈ Icc l r, HasDerivWithinAt q (q' x) (Icc l r) x)
    (hlp : ∀ x ∈ Icc l r, m ≤ p' x)
    (hlq : ∀ x ∈ Icc l r, m ≤ q' x)
    (himage : ∀ x ∈ Icc l r, p x ∈ Icc A B ∧ q x ∈ Icc A B)
    (hgap : ∀ x ∈ Icc l r, c ≤ a - (q x - p x) ∧ b - (q x - p x) ≤ d)
    (hFab : IntervalIntegrable F volume a b) (hFcd : IntervalIntegrable F volume c d)
    (hVab : ∀ v ∈ Icc a b, (∫ y in A..B, increment E v y ^ 2) ≤ F v)
    (hVcd : ∀ v ∈ Icc c d, (∫ y in A..B, increment E v y ^ 2) ≤ F v) :
    (b - a) * (∫ x in l..r, (E (q x) - E (p x)) ^ 2) ≤
      2 * (∫ v in a..b, F v) / m + 2 * (∫ v in c..d, F v) / m := by
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
  have hPi : ∀ x ∈ Icc l r, P x ∈ Icc A B := by
    intro x hx; rw [hPeq hx]; exact (himage x hx).1
  have hQi : ∀ x ∈ Icc l r, Q x ∈ Icc A B := by
    intro x hx; rw [hQeq hx]; exact (himage x hx).2
  have hgap' : ∀ x ∈ Icc l r, c ≤ a - (Q x - P x) ∧ b - (Q x - P x) ≤ d := by
    intro x hx; rw [hPeq hx, hQeq hx]; exact hgap x hx
  obtain ⟨hi1, hb1⟩ := averaged_variance_integral_le hE hlr hab hm hP hdP hlp hPi hFab hVab
  obtain ⟨hi2, hb2⟩ := averaged_variance_integral_le hE hlr hcd hm hQ hdQ hlq hQi hFcd hVcd
  have hi : IntervalIntegrable (fun x => increment E (Q x - P x) (P x) ^ 2)
      volume l r := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hlr]
    simpa only [pow_two, Pi.sub_apply] using increment_product_comp_integrableOn hE isCompact_Icc
      (hQ.sub hP) hP (hQ.sub hP) hP
  have hav := intervalIntegral.integral_mono_on hlr (hi.const_mul (b - a))
    ((hi1.const_mul 2).add (hi2.const_mul 2)) (by
      intro x hx
      simpa only [show P x + (Q x - P x) = Q x by ring] using
        averaged_increment_square_le hE hab (hgap' x hx).1 (hgap' x hx).2 (P x))
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hi1.const_mul 2) (hi2.const_mul 2)] at hav
  simp only [intervalIntegral.integral_const_mul] at hav
  have hbound : (b - a) * (∫ x in l..r, increment E (Q x - P x) (P x) ^ 2) ≤
      2 * (∫ v in a..b, F v) / m + 2 * (∫ v in c..d, F v) / m := by
    calc
      _ ≤ 2 * ((∫ v in a..b, F v) / m) +
          2 * ((∫ v in c..d, F v) / m) := by linarith
      _ = _ := by ring
  convert hbound using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hlr] at hx
  simp only [increment, hPeq hx, hQeq hx, add_sub_cancel]

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
  have h := two_endpoint_integral_average_le hE hlr
    (a := (C₀ + 1) * R) (b := (C₀ + 2) * R) (c := R) (d := (C₀ + 2) * R)
    (F := fun _ => K) (by nlinarith) (by nlinarith) hm hp hq hdp hdq hlp hlq himage
    (by intro x hx; constructor <;> nlinarith [(hgap x hx).1, (hgap x hx).2])
    intervalIntegrable_const intervalIntegrable_const
    (fun v hv => hV v ⟨by nlinarith [hv.1], hv.2⟩) hV
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h
  apply le_of_mul_le_mul_left (a := R) _ hR
  calc
    _ = ((C₀ + 2) * R - (C₀ + 1) * R) *
        (∫ x in l..r, (E (q x) - E (p x)) ^ 2) := by ring
    _ ≤ _ := h
    _ = _ := by ring

/-- Local variance bounds control two increasing endpoints with a signed gap. -/
theorem local_two_endpoint_increment_square_le
    {E p q p' q' : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {l r A B R C m : ℝ}
    (hlr : l ≤ r) (hAB : A ≤ B) (hR : 0 < R) (hC : 0 ≤ C) (hm : 0 < m)
    (hp : ContinuousOn p (Icc l r)) (hq : ContinuousOn q (Icc l r))
    (hdp : ∀ x ∈ Icc l r, HasDerivWithinAt p (p' x) (Icc l r) x)
    (hdq : ∀ x ∈ Icc l r, HasDerivWithinAt q (q' x) (Icc l r) x)
    (hlower : ∀ x ∈ Icc l r, m ≤ p' x ∧ m ≤ q' x)
    (himage : ∀ x ∈ Icc l r, p x ∈ Icc A B ∧ q x ∈ Icc A B)
    (hgap : ∀ x ∈ Icc l r, |q x - p x| ≤ R)
    (hV : ∀ v ∈ Icc R (4 * R), (∫ y in A..B, increment E v y ^ 2) ≤ C * v) :
    (∫ x in l..r, (E (q x) - E (p x)) ^ 2) ≤ 20 * C * R / m := by
  have h := two_endpoint_integral_average_le hE hlr
    (a := 2 * R) (b := 3 * R) (c := R) (d := 4 * R) (F := fun v => C * v)
    (by linarith) (by linarith) hm hp hq hdp hdq
    (fun x hx => (hlower x hx).1) (fun x hx => (hlower x hx).2) himage
    (by intro x hx; obtain ⟨hg1, hg2⟩ := abs_le.mp (hgap x hx); constructor <;> linarith)
    ((continuous_const.mul continuous_id).intervalIntegrable _ _)
    ((continuous_const.mul continuous_id).intervalIntegrable _ _)
    (fun v hv => hV v ⟨by linarith [hv.1], by linarith [hv.2]⟩) hV
  rw [intervalIntegral.integral_const_mul, integral_id,
    intervalIntegral.integral_const_mul, integral_id] at h
  apply le_of_mul_le_mul_left (a := R) _ hR
  calc
    _ = (3 * R - 2 * R) * (∫ x in l..r, (E (q x) - E (p x)) ^ 2) := by ring
    _ ≤ _ := h
    _ = _ := by ring

end
end D5.S3.Arith.Robin.ForwardKernel.MovingEndpointVariance
