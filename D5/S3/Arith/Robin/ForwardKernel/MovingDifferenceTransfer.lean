/- GID: D5/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MovingDifferenceTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Moving differences transfer to derivative, Jacobian and endpoint-strip bounds. -/

import D5.S3.Arith.Robin.ForwardKernel.CrossExponentDefs
import D5.S3.Arith.Robin.ForwardKernel.MovingEndpointVariance
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Endpoint-strip geometry for the moving change of variables. -/

namespace D5.S3.Arith.Robin.ForwardKernel.MovingDifferenceTransfer

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs CrossExponentDefs VarianceTransfer

noncomputable section

/-- An expanding change of variable contracts the square integral on a containing interval. -/
lemma square_comp_le {u φ dp : ℝ → ℝ} {L R l r : ℝ}
    (hlr : l ≤ r) (hLR : L ≤ R) (hu : Measurable u)
    (hu2 : MemLp u 2 (volume.restrict (Ioc L R)))
    (hp : ContinuousOn φ (Icc l r))
    (hdp : ∀ x ∈ Icc l r, HasDerivWithinAt φ (dp x) (Icc l r) x)
    (hd : ∀ x ∈ Icc l r, 1 ≤ dp x)
    (himage : MapsTo φ (Icc l r) (Icc L R)) :
    IntegrableOn (fun x => u (φ x) ^ 2) (Icc l r) ∧
      (∫ x in l..r, u (φ x) ^ 2) ≤ ∫ y in L..R, u y ^ 2 := by
  have hinj : InjOn φ (Icc l r) :=
    (strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc l r) hp
      (fun x hx => (hdp x (interior_subset hx)).mono interior_subset)
      (fun x hx => lt_of_lt_of_le zero_lt_one (hd x (interior_subset hx)))).injOn
  have hi : IntegrableOn (fun y => u y ^ 2) (Icc L R) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hu2.integrable_sq
  have hisub : φ '' Icc l r ⊆ Icc L R := image_subset_iff.mpr himage
  have hiw := (integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Icc hdp hinj (fun y => u y ^ 2)).mp (hi.mono_set hisub)
  have hmeas : AEStronglyMeasurable (fun x => u (φ x) ^ 2)
      (volume.restrict (Icc l r)) :=
    ((hu.comp_aemeasurable
      (hp.aestronglyMeasurable measurableSet_Icc).aemeasurable).aestronglyMeasurable).pow 2
  have hic : IntegrableOn (fun x => u (φ x) ^ 2) (Icc l r) := by
    apply hiw.mono' hmeas
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), smul_eq_mul,
      abs_of_nonneg (zero_le_one.trans (hd x hx))]
    exact le_mul_of_one_le_left (sq_nonneg _) (hd x hx)
  refine ⟨hic, ?_⟩
  rw [intervalIntegral.integral_of_le hlr, ← integral_Icc_eq_integral_Ioc]
  calc
    _ ≤ ∫ x in Icc l r, |dp x| • u (φ x) ^ 2 := by
      apply setIntegral_mono_on hic hiw measurableSet_Icc
      intro x hx
      rw [smul_eq_mul, abs_of_nonneg (zero_le_one.trans (hd x hx))]
      exact le_mul_of_one_le_left (sq_nonneg _) (hd x hx)
    _ = ∫ y in φ '' Icc l r, u y ^ 2 :=
      (integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hdp hinj
        (fun y => u y ^ 2)).symm
    _ ≤ ∫ y in Icc L R, u y ^ 2 :=
      setIntegral_mono_set hi (Eventually.of_forall (fun _ => sq_nonneg _))
        (Eventually.of_forall hisub)
    _ = _ := by rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hLR]

/-- The two endpoint strips produced by the moving change of variables. -/
def endpointStrips (θ s l r : ℝ) : Set ℝ :=
  Icc l (movingShift θ s l) ∪ Icc r (movingShift θ s r)

lemma moving_shift_nonneg_gap {θ s x : ℝ} (_hθ : 0 < θ)
    (hs : s ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x) :
    0 ≤ movingShift θ s x - x := by
  simp only [movingShift]
  simpa [sub_eq_add_neg, add_comm] using
    (mul_nonneg hs.1 (Real.rpow_nonneg hx θ))

lemma moving_shift_gap_le {θ s x X : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hs : s ∈ Icc (0 : ℝ) 1) (hX : 1 ≤ X) (hx : x ∈ Icc X (2 * X)) :
    movingShift θ s x - x ≤ 2 * X ^ θ := by
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hxpow : x ^ θ ≤ (2 * X) ^ θ :=
    Real.rpow_le_rpow hx0 (by linarith [hx.2]) hθ.le
  have hpow : (2 * X) ^ θ = 2 ^ θ * X ^ θ := by
    rw [Real.mul_rpow (by norm_num) (by linarith : 0 ≤ X)]
  have htwo : 2 ^ θ ≤ (2 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hθ1.le
  calc
    movingShift θ s x - x = s * x ^ θ := by simp [movingShift]
    _ ≤ x ^ θ := mul_le_of_le_one_left (Real.rpow_nonneg hx0 θ) hs.2
    _ ≤ 2 ^ θ * X ^ θ := by rw [← hpow]; exact hxpow
    _ ≤ 2 * X ^ θ := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (by linarith) _)

lemma endpointStrips_subset {θ s X l r : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hs : s ∈ Icc (0 : ℝ) 1) (hX : 1 ≤ X)
    (hl : l ∈ Icc X (2 * X)) (hr : r ∈ Icc l (2 * X)) :
    endpointStrips θ s l r ⊆ Icc (X / 2) (4 * X) := by
  intro y hy
  have hpowX : X ^ θ ≤ X := Real.rpow_le_self_of_one_le hX hθ1.le
  rcases hy with hy | hy
  · have hgap := moving_shift_gap_le hθ hθ1 hs hX hl
    have hmove : movingShift θ s l = l + (movingShift θ s l - l) := by ring
    refine ⟨by nlinarith [hl.1, hy.1, hX], ?_⟩
    nlinarith [hl.2, hy.2, hgap, hpowX, hmove]
  · have hgap := moving_shift_gap_le hθ hθ1 hs hX ⟨hl.1.trans hr.1, hr.2⟩
    have hmove : movingShift θ s r = r + (movingShift θ s r - r) := by ring
    refine ⟨by nlinarith [hr.1, hy.1, hl.1, hX], ?_⟩
    nlinarith [hr.2, hy.2, hgap, hpowX, hmove]

private lemma sliding_primitive_square_le
    {u φ : ℝ → ℝ} {l r H : ℝ}
    (hu : Integrable u) (hu2 : Integrable (fun y => u y ^ 2))
    (humeas : Measurable u) (hφ : Continuous φ)
    (hlr : l ≤ r) (hH : 0 ≤ H)
    (hgap : ∀ x ∈ Icc l r, φ x - x ∈ Icc (0 : ℝ) H) :
    (∫ x in l..r, (∫ y in x..φ x, u y) ^ 2) ≤
      H ^ 2 * ∫ y, u y ^ 2 := by
  let F : ℝ × ℝ → ℝ := fun p =>
    (Icc p.1 (φ p.1)).indicator (fun y => u y ^ 2) p.2
  have hm : Measurable F := by
    have hs : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2 ∧ p.2 ≤ φ p.1} :=
      (measurableSet_le measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd (hφ.measurable.comp measurable_fst))
    exact ((humeas.comp measurable_snd).pow_const 2).indicator hs
  have hF : Integrable F ((volume.restrict (Ioc l r)).prod volume) := by
    apply (hu2.comp_snd (volume.restrict (Ioc l r))).mono' hm.aestronglyMeasurable
    exact Eventually.of_forall (fun p => by
      dsimp [F]
      by_cases hp : p.2 ∈ Icc p.1 (φ p.1) <;>
        simp [hp, abs_of_nonneg (sq_nonneg (u p.2)), sq_nonneg])
  have hn (x y : ℝ) : 0 ≤ F (x,y) := by
    dsimp [F]
    by_cases hy : y ∈ Icc x (φ x) <;> simp [hy, sq_nonneg]
  have hinner (x : ℝ) (hx : x ∈ Icc l r) :
      (∫ y in x..φ x, u y) ^ 2 ≤ H * ∫ y, F (x,y) := by
    have hg := hgap x hx
    have hxf : x ≤ φ x := by linarith [hg.1]
    have he : ∫ y, F (x,y) = ∫ y in x..φ x, u y ^ 2 := by
      dsimp [F]
      rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hxf]
    rw [he]
    by_cases hzero : φ x - x = 0
    · have : φ x = x := by linarith
      simp [this]
    have hp : 0 < φ x - x := lt_of_le_of_ne hg.1 (Ne.symm hzero)
    have hc := interval_cauchy_schwarz hp
      (by simpa only [sub_self] using
        (hu.intervalIntegrable (a := x) (b := φ x)).comp_add_left x)
      (by simpa only [sub_self] using
        (hu2.intervalIntegrable (a := x) (b := φ x)).comp_add_left x)
    have ht := intervalIntegral.integral_comp_add_left (fun y => u y ^ 2) x
      (a := (0 : ℝ)) (b := φ x - x)
    have ht' := intervalIntegral.integral_comp_add_left u x
      (a := (0 : ℝ)) (b := φ x - x)
    simp only [add_zero, add_sub_cancel] at ht ht'
    rw [ht, ht'] at hc
    exact hc.trans (mul_le_mul_of_nonneg_right hg.2
      (intervalIntegral.integral_nonneg_of_forall hxf (fun y => sq_nonneg _)))
  have hgcont : Continuous (fun x => ∫ y in x..φ x, u y) := by
    have hp := hu.continuous_primitive (0 : ℝ)
    convert (hp.comp hφ).sub hp using 1
    funext x
    exact (intervalIntegral.integral_interval_sub_left
      hu.intervalIntegrable hu.intervalIntegrable).symm
  have hGi : IntervalIntegrable (fun x => (∫ y in x..φ x, u y) ^ 2) volume l r :=
    (hgcont.pow 2).intervalIntegrable l r
  have hle := intervalIntegral.integral_mono_on hlr hGi
    (by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlr]
      exact hF.integral_prod_left.const_mul H)
    hinner
  rw [intervalIntegral.integral_const_mul] at hle
  simp_rw [intervalIntegral.integral_of_le hlr] at hle
  rw [integral_integral_swap hF] at hle
  have hbound (y : ℝ) : (∫ x in Ioc l r, F (x,y)) ≤ H * u y ^ 2 := by
    let S : Set ℝ := {x | x ∈ Ioc l r ∧ x ≤ y ∧ y ≤ φ x}
    have hS : MeasurableSet S :=
      measurableSet_Ioc.inter (measurableSet_Iic.inter (hφ.measurable measurableSet_Ici))
    have hsub : S ⊆ Icc (y-H) y := by
      intro x hx
      have hg := hgap x ⟨hx.1.1.le, hx.1.2⟩
      exact ⟨by linarith [hx.2.2, hg.2], hx.2.1⟩
    have he : ∫ x in Ioc l r, F (x,y) = ∫ x in S, u y ^ 2 := by
      rw [← integral_indicator measurableSet_Ioc, ← integral_indicator hS]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        simp only [F, S, Set.indicator, mem_Ioc, mem_Icc, mem_ofPred_eq]
        split_ifs <;> simp_all)
    rw [he]
    calc
      _ ≤ ∫ x in Icc (y-H) y, u y ^ 2 :=
        setIntegral_mono_set (integrableOn_const (by simp))
          (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall hsub)
      _ = H * u y ^ 2 := by
        rw [setIntegral_const, Measure.real, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith : 0 ≤ y - (y-H)), smul_eq_mul]
        ring
  have hb := integral_mono hF.integral_prod_right (hu2.const_mul H) hbound
  calc
    _ ≤ H * ∫ y, ∫ x in Ioc l r, F (x,y) := by
      simpa only [intervalIntegral.integral_of_le hlr] using hle
    _ ≤ H * (H * ∫ y, u y ^ 2) := by
      have hb' : (∫ y, ∫ x in Ioc l r, F (x,y)) ≤ H * ∫ y, u y ^ 2 := by
        simpa only [integral_const_mul] using hb
      exact mul_le_mul_of_nonneg_left hb' hH
    _ = _ := by ring

lemma sliding_primitive_l2_le
    {u φ : ℝ → ℝ} {l r H L R : ℝ}
    (hu : Measurable u) (huLp : MemLp u 2 (volume.restrict (Ioc L R)))
    (hφ : Continuous φ) (hlr : l ≤ r) (hH : 0 ≤ H)
    (hLl : L ≤ l) (hrR : r ≤ R)
    (hgap : ∀ x ∈ Icc l r, φ x - x ∈ Icc (0 : ℝ) H)
    (himage : ∀ x ∈ Icc l r, φ x ≤ R) :
    intervalL2 l r (fun x => ∫ y in x..φ x, u y) ≤ H * intervalL2 L R u := by
  let w := (Icc L R).indicator u
  have hLp : MemLp u 2 (volume.restrict (Icc L R)) := by
    rwa [← restrict_Ioc_eq_restrict_Icc]
  have hwi : Integrable w := IntegrableOn.integrable_indicator
    (hLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)) measurableSet_Icc
  have hw2 : Integrable (fun y => w y ^ 2) := by
    convert IntegrableOn.integrable_indicator hLp.integrable_sq measurableSet_Icc using 1
    funext y
    by_cases hy : y ∈ Icc L R <;> simp [w,hy]
  have hws := sliding_primitive_square_le hwi hw2 (hu.indicator measurableSet_Icc)
    hφ hlr hH hgap
  have he (x : ℝ) (hx : x ∈ Icc l r) :
      (∫ y in x..φ x, w y) = ∫ y in x..φ x, u y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le (by linarith [(hgap x hx).1])] at hy
    dsimp [w]
    exact indicator_of_mem (show y ∈ Icc L R from
      ⟨hLl.trans (hx.1.trans hy.1), hy.2.trans (himage x hx)⟩) _
  have hs2 : ∫ y, w y ^ 2 = ∫ y in L..R, u y ^ 2 := by
    have hew : (fun y => w y ^ 2) = (Icc L R).indicator (fun y => u y ^ 2) := by
      funext y
      by_cases hy : y ∈ Icc L R <;> simp [w,hy]
    rw [hew,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (hLl.trans (hlr.trans hrR))]
  have heint : (∫ x in l..r, (∫ y in x..φ x, w y) ^ 2) =
      ∫ x in l..r, (∫ y in x..φ x, u y) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hlr] at hx
    simpa only [] using congrArg (fun z : ℝ => z ^ 2) (he x hx)
  rw [heint,hs2] at hws
  unfold intervalL2
  calc
    _ ≤ Real.sqrt (H ^ 2 * ∫ y in L..R, u y ^ 2) := Real.sqrt_le_sqrt hws
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,abs_of_nonneg hH]

private lemma sliding_primitive_memLp
    {u φ : ℝ → ℝ} {l r H L R : ℝ}
    (_hu : Measurable u) (huLp : MemLp u 2 (volume.restrict (Ioc L R)))
    (hφ : Continuous φ) (hlr : l ≤ r)
    (hLl : L ≤ l) (_hrR : r ≤ R)
    (hgap : ∀ x ∈ Icc l r, φ x - x ∈ Icc (0 : ℝ) H)
    (himage : ∀ x ∈ Icc l r, φ x ≤ R) :
    MemLp (fun x => ∫ y in x..φ x, u y) 2 (volume.restrict (Ioc l r)) := by
  let w := (Icc L R).indicator u
  have hLp : MemLp u 2 (volume.restrict (Icc L R)) := by
    rwa [← restrict_Ioc_eq_restrict_Icc]
  have hwi : Integrable w := IntegrableOn.integrable_indicator
    (hLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)) measurableSet_Icc
  have hgcont : Continuous (fun x => ∫ y in x..φ x, w y) := by
    have hp := hwi.continuous_primitive (0 : ℝ)
    convert (hp.comp hφ).sub hp using 1
    funext x
    exact (intervalIntegral.integral_interval_sub_left
      hwi.intervalIntegrable hwi.intervalIntegrable).symm
  have hwLp : MemLp (fun x => ∫ y in x..φ x, w y) 2 (volume.restrict (Ioc l r)) :=
    (memLp_two_iff_integrable_sq hgcont.measurable.aestronglyMeasurable).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hlr).mp
        ((hgcont.pow 2).intervalIntegrable l r))
  apply MemLp.ae_eq _ hwLp
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le (by linarith [(hgap x ⟨hx.1.le,hx.2⟩).1])] at hy
  exact indicator_of_mem (show y ∈ Icc L R from
    ⟨hLl.trans (hx.1.le.trans hy.1), hy.2.trans (himage x ⟨hx.1.le,hx.2⟩)⟩) _


private lemma weighted_integral_eq_of_primitive
    {w G v : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r)
    (hw : IntervalIntegrable w volume l r)
    (hv : AbsolutelyContinuousOnInterval v l r)
    (hG : ∀ x ∈ Icc l r, (∫ y in l..x, w y) = G x - G l) :
    (∫ x in l..r, w x * v x) =
      G r * v r - G l * v l - ∫ x in l..r, G x * deriv v x := by
  let F : ℝ → ℝ := fun x => ∫ y in l..x, w y
  have hFac : AbsolutelyContinuousOnInterval F l r :=
    hw.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have heq : (∫ x in l..r, w x * v x) =
      v r * F r - ∫ x in l..r, deriv v x * F x := by
    have he : (∫ x in l..r, w x * v x) =
        ∫ x in l..r, v x * deriv F x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hw.ae_hasDerivAt_integral] with x hx hxu
      rw [(hx (uIoc_subset_uIcc hxu) l (by simp)).deriv]
      exact mul_comm _ _
    rw [he, hv.integral_mul_deriv_eq_deriv_mul hFac]
    simp [F]
  have hGc : ContinuousOn G (uIcc l r) := by
    apply (hFac.continuousOn.add
      (continuousOn_const : ContinuousOn (fun _ : ℝ => G l) (uIcc l r))).congr
    intro x hx
    rw [uIcc_of_le hlr] at hx
    change G x = (∫ y in l..x, w y) + G l
    linarith [hG x hx]
  have hiG := hv.intervalIntegrable_deriv.mul_continuousOn hGc
  have hicon := hv.intervalIntegrable_deriv.mul_const (G l)
  have hsplit : (∫ x in l..r, deriv v x * F x) =
      (∫ x in l..r, G x * deriv v x) - G l * (v r - v l) := by
    calc
      _ = ∫ x in l..r, deriv v x * G x - deriv v x * G l := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hlr] at hx
        dsimp only [F]
        rw [hG x hx]
        ring
      _ = (∫ x in l..r, deriv v x * G x) -
          (∫ x in l..r, deriv v x * G l) :=
        intervalIntegral.integral_sub hiG hicon
      _ = _ := by
        rw [intervalIntegral.integral_mul_const, hv.integral_deriv_eq_sub]
        congr 1
        · apply intervalIntegral.integral_congr
          intro x hx
          ring
        · ring
  rw [heq, hsplit]
  dsimp only [F]
  rw [hG r ⟨hlr, le_rfl⟩]
  ring


private lemma primitive_transfer_bound
    {w e G v : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r)
    (hw : IntervalIntegrable w volume l r)
    (hv : AbsolutelyContinuousOnInterval v l r)
    (hG : ∀ x ∈ Icc l r, (∫ y in l..x, w y) = G x - G l)
    (hGL2 : MemLp G 2 (volume.restrict (Ioc l r)))
    (hvdL2 : MemLp (deriv v) 2 (volume.restrict (Ioc l r)))
    (heL2 : MemLp e 2 (volume.restrict (Ioc l r)))
    (hvL2 : MemLp v 2 (volume.restrict (Ioc l r))) :
    |∫ x in l..r, (w x - e x) * v x| ≤
      |G r * v r| + |G l * v l| +
        intervalL2 l r G * intervalL2 l r (deriv v) +
        intervalL2 l r e * intervalL2 l r v := by
  have hiw := hw.mul_continuousOn hv.continuousOn
  have hie : IntervalIntegrable (fun x => e x * v x) volume l r :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlr).mpr
      (heL2.integrable_mul hvL2)
  have hidentity : (∫ x in l..r, (w x - e x) * v x) =
      G r * v r - G l * v l - (∫ x in l..r, G x * deriv v x) -
        ∫ x in l..r, e x * v x := by
    calc
      _ = (∫ x in l..r, w x * v x) - (∫ x in l..r, e x * v x) := by
        rw [← intervalIntegral.integral_sub hiw hie]
        apply intervalIntegral.integral_congr
        intro x hx
        ring
      _ = _ := by rw [weighted_integral_eq_of_primitive hlr hw hv hG]
  have hpairG : |∫ x in l..r, G x * deriv v x| ≤
      intervalL2 l r G * intervalL2 l r (deriv v) := by
    have hc := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
      (show MemLp G (ENNReal.ofReal 2) _ by simpa using hGL2)
      (show MemLp (deriv v) (ENNReal.ofReal 2) _ by simpa using hvdL2)
    have hn := (norm_integral_le_integral_norm (fun x => G x * deriv v x)).trans
      (by simpa only [norm_mul] using hc)
    simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow,
      intervalIntegral.integral_of_le hlr, intervalL2] using hn
  have hpairE : |∫ x in l..r, e x * v x| ≤
      intervalL2 l r e * intervalL2 l r v := by
    have hc := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
      (show MemLp e (ENNReal.ofReal 2) _ by simpa using heL2)
      (show MemLp v (ENNReal.ofReal 2) _ by simpa using hvL2)
    have hn := (norm_integral_le_integral_norm (fun x => e x * v x)).trans
      (by simpa only [norm_mul] using hc)
    simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow,
      intervalIntegral.integral_of_le hlr, intervalL2] using hn
  rw [hidentity]
  calc
    _ ≤ |G r * v r - G l * v l - (∫ x in l..r, G x * deriv v x)| +
        |∫ x in l..r, e x * v x| := abs_sub _ _
    _ ≤ |G r * v r - G l * v l| + |∫ x in l..r, G x * deriv v x| +
        |∫ x in l..r, e x * v x| := add_le_add (abs_sub _ _) le_rfl
    _ ≤ |G r * v r| + |G l * v l| + |∫ x in l..r, G x * deriv v x| +
        |∫ x in l..r, e x * v x| := by linarith [abs_sub (G r * v r) (G l * v l)]
    _ ≤ _ := by linarith

private lemma primitive_transfer_bound_of_norm_bounds
    {w e G v : ℝ → ℝ} {l r H U D V V₂ Vd : ℝ}
    (hlr : l ≤ r)
    (hw : IntervalIntegrable w volume l r)
    (hv : AbsolutelyContinuousOnInterval v l r)
    (hG : ∀ x ∈ Icc l r, (∫ y in l..x, w y) = G x - G l)
    (hGL2 : MemLp G 2 (volume.restrict (Ioc l r)))
    (hvdL2 : MemLp (deriv v) 2 (volume.restrict (Ioc l r)))
    (heL2 : MemLp e 2 (volume.restrict (Ioc l r)))
    (hvL2 : MemLp v 2 (volume.restrict (Ioc l r)))
    (hGn : intervalL2 l r G ≤ H * U)
    (hen : intervalL2 l r e ≤ D * U)
    (hvn : intervalL2 l r v ≤ V₂)
    (hvdn : intervalL2 l r (deriv v) ≤ Vd)
    (hvv : |v l| ≤ V ∧ |v r| ≤ V)
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hU : 0 ≤ U) :
    |∫ x in l..r, (w x - e x) * v x| ≤
      H * U * Vd + D * U * V₂ + V * (|G r| + |G l|) := by
  have hGn0 : 0 ≤ intervalL2 l r G := Real.sqrt_nonneg _
  have hen0 : 0 ≤ intervalL2 l r e := Real.sqrt_nonneg _
  have hvn0 : 0 ≤ intervalL2 l r v := Real.sqrt_nonneg _
  have hvdn0 : 0 ≤ intervalL2 l r (deriv v) := Real.sqrt_nonneg _
  have hpG := mul_le_mul hGn hvdn hvdn0 (mul_nonneg hH hU)
  have hpE := mul_le_mul hen hvn hvn0 (mul_nonneg hD hU)
  have hBr : |G r * v r| ≤ V * |G r| := by
    rw [abs_mul, mul_comm V]
    exact mul_le_mul_of_nonneg_left hvv.2 (abs_nonneg _)
  have hBl : |G l * v l| ≤ V * |G l| := by
    rw [abs_mul, mul_comm V]
    exact mul_le_mul_of_nonneg_left hvv.1 (abs_nonneg _)
  have hh := primitive_transfer_bound hlr hw hv hG hGL2 hvdL2 heL2 hvL2
  nlinarith

private lemma bounded_multiplier_intervalL2
    {f c : ℝ → ℝ} {l r D : ℝ} (hlr : l ≤ r) (hD : 0 ≤ D)
    (hf : MemLp f 2 (volume.restrict (Ioc l r)))
    (hc : AEStronglyMeasurable c (volume.restrict (Ioc l r)))
    (hcb : ∀ x ∈ Icc l r, 0 ≤ c x ∧ c x ≤ D) :
    MemLp (fun x => c x * f x) 2 (volume.restrict (Ioc l r)) ∧
      intervalL2 l r (fun x => c x * f x) ≤ D * intervalL2 l r f := by
  have hem : MemLp (fun x => c x * f x) 2 (volume.restrict (Ioc l r)) := by
    apply (hf.norm.const_mul D).mono' (hc.mul hf.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hcx := hcb x ⟨hx.1.le, hx.2⟩
    simp only [Pi.mul_apply] at *
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hcx.1]
    exact mul_le_mul_of_nonneg_right hcx.2 (abs_nonneg _)
  refine ⟨hem, ?_⟩
  have hs : (∫ x in l..r, (c x * f x) ^ 2) ≤
      D ^ 2 * ∫ x in l..r, f x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_of_le hlr]
    apply integral_mono_ae hem.integrable_sq (hf.integrable_sq.const_mul (D ^ 2))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hcx := hcb x ⟨hx.1.le, hx.2⟩
    have hs : c x ^ 2 ≤ D ^ 2 := (sq_le_sq₀ hcx.1 hD).mpr hcx.2
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  have hIf := intervalIntegral.integral_nonneg_of_forall (μ := volume) hlr
    (fun x => sq_nonneg (f x))
  have hIe := intervalIntegral.integral_nonneg_of_forall (μ := volume) hlr
    (fun x => sq_nonneg (c x * f x))
  unfold intervalL2
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hD (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hIf, Real.sq_sqrt hIe]
  exact hs

private lemma moving_jacobian_error_bound
    {a s X x : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hs : s ∈ Icc (0 : ℝ) 1) (hX : 1 ≤ X) (hx : X ≤ x) :
    0 ≤ s * (a * x ^ (a - 1)) ∧
      s * (a * x ^ (a - 1)) ≤ X ^ a / X := by
  have hX0 : 0 < X := by linarith
  have hx0 : 0 ≤ x := hX0.le.trans hx
  have hp0 := Real.rpow_nonneg hx0 (a - 1)
  have hp := Real.rpow_le_rpow_of_nonpos hX0 hx (by linarith : a - 1 ≤ 0)
  have hsa : 0 ≤ s * a := mul_nonneg hs.1 ha.le
  have hsa1 : s * a ≤ 1 :=
    (mul_le_of_le_one_left ha.le hs.2).trans ha1.le
  constructor
  · exact mul_nonneg hs.1 (mul_nonneg ha.le hp0)
  · calc
      s * (a * x ^ (a - 1)) = (s * a) * x ^ (a - 1) := by ring
      _ ≤ x ^ (a - 1) := mul_le_of_le_one_left hp0 hsa1
      _ ≤ X ^ (a - 1) := hp
      _ = X ^ a / X := Real.rpow_sub_one hX0.ne' a

private lemma contDiffOn_deriv_memLp {v : ℝ → ℝ} {L R : ℝ} (hLR : L < R)
    (hv : ContDiffOn ℝ 1 v (Icc L R)) :
    MemLp (deriv v) 2 (volume.restrict (Ioc L R)) := by
  let w : ℝ → ℝ := derivWithin v (Icc L R)
  have hw : ContinuousOn w (Icc L R) :=
    hv.continuousOn_derivWithin (uniqueDiffOn_Icc hLR) (by norm_num)
  have hm : MemLp w 2 (volume.restrict (Icc L R)) := by
    apply (memLp_two_iff_integrable_sq (hw.aestronglyMeasurable measurableSet_Icc)).mpr
    exact (hw.pow 2).integrableOn_Icc
  rw [← restrict_Ioo_eq_restrict_Ioc]
  apply MemLp.ae_eq _ (hm.mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl))
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  dsimp [w]
  exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)


private lemma strip_endpoint_integral_le {u : ℝ → ℝ} {a s X l r : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hs : s ∈ Icc (0 : ℝ) 1) (hX : 1 ≤ X)
    (hl : l ∈ Icc X (2 * X)) (hr : r ∈ Icc l (2 * X))
    (hu : MemLp u 2 (volume.restrict (Ioc (X / 2) (4 * X))))
    (hsub : endpointStrips a s l r ⊆ Icc (X / 2) (4 * X)) :
    |∫ y in r..movingShift a s r, u y| +
      |∫ y in l..movingShift a s l, u y| ≤
        2 * ∫ y in endpointStrips a s l r, |u y| := by
  have hi : IntegrableOn (fun y => |u y|) (Icc (X / 2) (4 * X)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (hu.integrable (by norm_num : (1 : ENNReal) ≤ 2)).abs
  have hiS := hi.mono_set hsub
  have hle (x : ℝ) (hx : x ∈ Icc X (2 * X))
      (hsx : Icc x (movingShift a s x) ⊆ endpointStrips a s l r) :
      |∫y in x..movingShift a s x,u y| ≤ ∫y in endpointStrips a s l r,|u y| := by
    calc
      _ ≤ ∫y in x..movingShift a s x,|u y| := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (f := u)
            (by linarith [moving_shift_nonneg_gap ha hs (by linarith [hx.1] : 0 ≤ x)])
      _ = ∫y in Icc x (movingShift a s x),|u y| := by
        rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le
          (by linarith [moving_shift_nonneg_gap ha hs (by linarith [hx.1] : 0 ≤ x)])]
      _ ≤ _ := setIntegral_mono_set hiS (Eventually.of_forall fun _ => abs_nonneg _)
        (Eventually.of_forall hsx)
  have hlb := hle l hl subset_union_left
  have hrb := hle r ⟨hl.1.trans hr.1,hr.2⟩ subset_union_right
  linarith



private lemma concrete_moving_transfer
    {a s X l r : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hX : 2 ≤ X) (hs : s ∈ Icc (0 : ℝ) 1)
    (hl : l ∈ Icc X (2 * X)) (hr : r ∈ Icc l (2 * X))
    {u v : ℝ → ℝ} {V : ℝ} (hu : Measurable u)
    (hu2 : MemLp u 2 (volume.restrict (Ioc (X / 2) (4 * X))))
    (hv : ContDiffOn ℝ 1 v (Icc (X / 2) (4 * X)))
    (hV : 0 ≤ V) (hvb : ∀ y ∈ Icc (X / 2) (4 * X), |v y| ≤ V) :
    |∫ x in l..r, (u (movingShift a s x) - u x) * v x| ≤
      4 * (X ^ a * intervalL2 (X / 2) (4 * X) u *
        intervalL2 (X / 2) (4 * X) (deriv v) +
        (X ^ a / X) * intervalL2 (X / 2) (4 * X) u *
        intervalL2 (X / 2) (4 * X) v +
        V * ∫ y in endpointStrips a s l r, |u y|) := by
  let L := X / 2
  let R := 4 * X
  let φ := movingShift a s
  let c : ℝ → ℝ := fun x => s * (a * x ^ (a - 1))
  let d : ℝ → ℝ := fun x => 1 + c x
  let G : ℝ → ℝ := fun x => ∫ y in x..φ x, u y
  let e : ℝ → ℝ := fun x => c x * u (φ x)
  let w : ℝ → ℝ := fun x => d x * u (φ x) - u x
  have hX0 : 0 < X := by linarith
  have hLR : L < R := by dsimp [L,R]; linarith
  have hcore (x : ℝ) (hx : x ∈ Icc l r) : x ∈ Icc L R := by
    dsimp [L,R]; constructor <;> linarith [hl.1,hr.2,hx.1,hx.2]
  have hxs (x : ℝ) (hx : x ∈ Icc l r) : x ∈ Icc X (2 * X) :=
    ⟨hl.1.trans hx.1, hx.2.trans hr.2⟩
  have hφ : Continuous φ :=
    continuous_id.add (continuous_const.mul (Real.continuous_rpow_const ha.le))
  have hφd (x : ℝ) (hx : x ∈ Icc l r) : HasDerivAt φ (d x) x :=
    (hasDerivAt_id x).add
      ((Real.hasDerivAt_rpow_const (Or.inl (by linarith [(hxs x hx).1] : x ≠ 0))).const_mul s)
  have hc (x : ℝ) (hx : x ∈ Icc l r) : c x ∈ Icc (0 : ℝ) (X ^ a / X) :=
    moving_jacobian_error_bound ha ha1 hs (by linarith) (hxs x hx).1
  have hd (x : ℝ) (hx : x ∈ Icc l r) : 1 ≤ d x := by
    dsimp [d]; linarith [(hc x hx).1]
  have hgap (x : ℝ) (hx : x ∈ Icc l r) : φ x - x ∈ Icc (0 : ℝ) (2 * X ^ a) :=
    ⟨moving_shift_nonneg_gap ha hs (by linarith [(hxs x hx).1]),
      moving_shift_gap_le ha ha1 hs (by linarith) (hxs x hx)⟩
  have himage (x : ℝ) (hx : x ∈ Icc l r) : φ x ∈ Icc L R := by
    have hp := Real.rpow_le_self_of_one_le (by linarith : 1 ≤ X) ha1.le
    have hg := hgap x hx
    constructor <;> dsimp [L,R] <;> linarith [(hxs x hx).1,(hxs x hx).2,hg.1,hg.2]
  have hsub : Ioc l r ⊆ Ioc L R := by
    intro x hx; exact ⟨lt_of_le_of_lt (hcore l ⟨le_rfl,hr.1⟩).1 hx.1,
      hx.2.trans (hcore r ⟨hr.1,le_rfl⟩).2⟩
  have huC := hu2.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hcomp := square_comp_le hr.1 hLR.le hu hu2 hφ.continuousOn
    (fun x hx => (hφd x hx).hasDerivWithinAt) hd himage
  have huφ : MemLp (fun x => u (φ x)) 2 (volume.restrict (Ioc l r)) :=
    (memLp_two_iff_integrable_sq (hu.comp hφ.measurable).aestronglyMeasurable).mpr
      (hcomp.1.mono_set Ioc_subset_Icc_self)
  have hcn : AEStronglyMeasurable c (volume.restrict (Ioc l r)) :=
    (measurable_const.mul
      (measurable_const.mul (measurable_id.pow_const (a - 1)))).aestronglyMeasurable
  have he := bounded_multiplier_intervalL2 hr.1 (by positivity : 0 ≤ X ^ a / X) huφ hcn hc
  have hdLp := bounded_multiplier_intervalL2 (c := d) hr.1 (by positivity : 0 ≤ 1+X ^ a / X)
    huφ ((aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => (1:ℝ)) _).add hcn)
    (fun x hx => ⟨by dsimp [d]; linarith [(hc x hx).1],
      by dsimp [d]; linarith [(hc x hx).2]⟩)
  have hwLp : MemLp w 2 (volume.restrict (Ioc l r)) := hdLp.1.sub huC
  have hw : IntervalIntegrable w volume l r :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.1).mpr
      (hwLp.integrable (by norm_num))
  have hvi : MemLp v 2 (volume.restrict (Ioc L R)) := by
    rw [restrict_Ioc_eq_restrict_Icc]
    exact (memLp_two_iff_integrable_sq
      (hv.continuousOn.aestronglyMeasurable measurableSet_Icc)).mpr
      ((hv.continuousOn.pow 2).integrableOn_Icc)
  have hvdi := contDiffOn_deriv_memLp hLR hv
  have hvC := hvi.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hvdC := hvdi.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hGn := sliding_primitive_l2_le hu hu2 hφ hr.1 (by positivity : 0 ≤ 2 * X ^ a)
    (hcore l ⟨le_rfl,hr.1⟩).1 (hcore r ⟨hr.1,le_rfl⟩).2 hgap
    (fun x hx => (himage x hx).2)
  have hGLp := sliding_primitive_memLp hu hu2 hφ hr.1
    (hcore l ⟨le_rfl,hr.1⟩).1 (hcore r ⟨hr.1,le_rfl⟩).2 hgap
    (fun x hx => (himage x hx).2)
  have hnormmono (f : ℝ → ℝ) (hf : MemLp f 2 (volume.restrict (Ioc L R))) :
      intervalL2 l r f ≤ intervalL2 L R f := by
    unfold intervalL2
    apply Real.sqrt_le_sqrt
    exact intervalIntegral.integral_mono_interval
      (hcore l ⟨le_rfl,hr.1⟩).1 hr.1 (hcore r ⟨hr.1,le_rfl⟩).2
      (Eventually.of_forall fun _ => sq_nonneg _)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hLR.le).mpr hf.integrable_sq)
  have huφn : intervalL2 l r (fun x => u (φ x)) ≤ intervalL2 L R u :=
    Real.sqrt_le_sqrt hcomp.2
  have hen : intervalL2 l r e ≤ (X ^ a / X) * intervalL2 L R u :=
    he.2.trans (mul_le_mul_of_nonneg_left huφn (by positivity))
  have huInt (x : ℝ) (hx : x ∈ Icc L R) (y : ℝ) (hy : y ∈ Icc L R) :
      IntervalIntegrable u volume x y := by
    have hi : IntervalIntegrable u volume L R :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hLR.le).mpr
        (hu2.integrable (by norm_num))
    exact hi.mono_set (by rw [uIcc_of_le hLR.le]; exact uIcc_subset_Icc hx hy)
  have hvac : AbsolutelyContinuousOnInterval v l r :=
    (hv.mono (by rw [uIcc_of_le hr.1]; exact hcore)).absolutelyContinuousOnInterval
  have hGP : ∀ x ∈ Icc l r, (∫ y in l..x, w y) = G x - G l := by
    intro x hx
    have hsubx : uIcc l x ⊆ uIcc l r := by
      rw [uIcc_of_le hx.1,uIcc_of_le hr.1]
      exact Icc_subset_Icc le_rfl hx.2
    have hdi : IntervalIntegrable (fun y => d y * u (φ y)) volume l x :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hr.1).mpr
        (hdLp.1.integrable (by norm_num))).mono_set hsubx
    change (∫ y in l..x,d y*u (φ y)-u y) = G x-G l
    rw [intervalIntegral.integral_sub hdi
      (huInt l (hcore l ⟨le_rfl,hr.1⟩) x (hcore x hx))]
    have heq : (∫ y in l..x,d y*u (φ y)) = ∫y in φ l..φ x,u y := by
      simpa only [smul_eq_mul,Function.comp_apply] using
        (intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
          (g:=u) hφ.continuousOn
          (fun y hy => hφd y (by
            rw [min_eq_left hx.1,max_eq_right hx.1] at hy
            exact ⟨hy.1.le,hy.2.le.trans hx.2⟩))
          (fun y hy => zero_le_one.trans (hd y (by
            rw [min_eq_left hx.1,max_eq_right hx.1] at hy
            exact ⟨hy.1.le,hy.2.le.trans hx.2⟩))))
    rw [heq]
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (huInt l (hcore l ⟨le_rfl,hr.1⟩) (φ l) (himage l ⟨le_rfl,hr.1⟩))
      (huInt (φ l) (himage l ⟨le_rfl,hr.1⟩) (φ x) (himage x hx))
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (huInt l (hcore l ⟨le_rfl,hr.1⟩) x (hcore x hx))
      (huInt x (hcore x hx) (φ x) (himage x hx))
    dsimp [G]
    linarith
  have hb := primitive_transfer_bound_of_norm_bounds hr.1 hw hvac hGP hGLp hvdC he.1 hvC
    hGn hen (hnormmono v hvi) (hnormmono (deriv v) hvdi)
    ⟨hvb l (hcore l ⟨le_rfl,hr.1⟩),hvb r (hcore r ⟨hr.1,le_rfl⟩)⟩
    (by positivity : 0 ≤ 2 * X ^ a) (by positivity : 0 ≤ X ^ a / X) (Real.sqrt_nonneg _)
  have hstrip : endpointStrips a s l r ⊆ Icc L R :=
    endpointStrips_subset ha ha1 hs (by linarith) hl hr
  have hboundary := strip_endpoint_integral_le ha ha1 hs (by linarith) hl hr hu2 hstrip
  have hrewrite : (fun x => (w x-e x)*v x) =
      (fun x => (u (movingShift a s x)-u x)*v x) := by
    funext x; dsimp [w,e,d,φ,c]; ring
  rw [hrewrite] at hb
  dsimp [G,φ,L,R] at hb
  have hnonneg : 0 ≤ ∫y in endpointStrips a s l r, |u y| :=
    integral_nonneg (fun _ => abs_nonneg _)
  have hboundary' := mul_le_mul_of_nonneg_left hboundary hV
  have huN := Real.sqrt_nonneg (∫x in (X / 2)..(4 * X),u x^2)
  have hvN := Real.sqrt_nonneg (∫x in (X / 2)..(4 * X),v x^2)
  have hvdN := Real.sqrt_nonneg (∫x in (X / 2)..(4 * X),deriv v x^2)
  dsimp [intervalL2] at *
  nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ X ^ a / X) huN) hvN,
    mul_nonneg (mul_nonneg (by positivity : 0 ≤ X ^ a) huN) hvdN,
    mul_nonneg hV hnonneg]

/-- Moving differences transfer to a derivative term, a Jacobian error, and endpoint strips. -/
theorem moving_difference_transfer_bound
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ l ∈ Icc X (2 * X),
      ∀ r ∈ Icc l (2 * X),
      ∀ u v : ℝ → ℝ, ∀ V : ℝ,
        Measurable u →
        MemLp u 2 (volume.restrict (Ioc (X / 2) (4 * X))) →
        ContDiffOn ℝ 1 v (Icc (X / 2) (4 * X)) →
        0 ≤ V →
        (∀ y ∈ Icc (X / 2) (4 * X), |v y| ≤ V) →
        |∫ x in l..r,
            (u (movingShift a s x) - u x) * v x| ≤
          C *
            (X ^ a *
                intervalL2 (X / 2) (4 * X) u *
                intervalL2 (X / 2) (4 * X) (deriv v) +
             (X ^ a / X) *
                intervalL2 (X / 2) (4 * X) u *
                intervalL2 (X / 2) (4 * X) v +
             V * ∫ y in endpointStrips a s l r, |u y|) := by
  refine ⟨4, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX s hs l hl r hr u v V hu hu2 hv hV hvb
  exact concrete_moving_transfer ha ha1 hX hs hl hr hu hu2 hv hV hvb

end
end D5.S3.Arith.Robin.ForwardKernel.MovingDifferenceTransfer
