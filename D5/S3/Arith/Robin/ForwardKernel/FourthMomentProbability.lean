/- GID: D5/S3/Arith/Robin/ForwardKernel/FourthMomentProbability
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/FourthMomentProbability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Second and fourth moments with small mean force two-sided positive-proportion tails. -/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-! Moment interpolation and centered tail truncation give explicit probability bounds. -/

namespace D5.S3.Arith.Robin.ForwardKernel.FourthMomentProbability

open MeasureTheory Set Filter

noncomputable section

/-- An upper bound for the centered fourth moment. -/
def fourthMomentK1 (v K : ℝ) : ℝ := 8 * (K + v ^ 2 / 4)

/-- The lower bound for the first absolute centered moment. -/
def fourthMomentLambda (v K : ℝ) : ℝ :=
  (v / 2) ^ (3 / 2 : ℝ) / Real.sqrt (fourthMomentK1 v K)

/-- The two-sided threshold. -/
def fourthMomentThreshold (v K : ℝ) : ℝ := fourthMomentLambda v K / 8

/-- The lower bound for each tail probability. -/
def fourthMomentDensity (v K : ℝ) : ℝ :=
  fourthMomentLambda v K ^ 2 / (16 * Real.sqrt (fourthMomentK1 v K))

private lemma cs_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤
      (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall hf0) (Eventually.of_forall hg0)
    (by simpa using (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hf2)
    (by simpa using (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hg2)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at h
  have h0 : 0 ≤ ∫ x, f x * g x ∂μ := integral_nonneg fun x => mul_nonneg (hf0 x) (hg0 x)
  have h1 := Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (f x) :
    0 ≤ ∫ x, f x ^ 2 ∂μ)
  have h2 := Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (g x) :
    0 ≤ ∫ x, g x ^ 2 ∂μ)
  have hs := pow_le_pow_left₀ h0 h 2
  rw [mul_pow, h1, h2] at hs
  exact hs

private lemma moment_interpolation {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {u : Ω → ℝ} (hu : Measurable u) (hu0 : ∀ x, 0 ≤ u x)
    (h1 : Integrable u μ)
    (h4 : Integrable (fun x => u x ^ 4) μ) :
    (∫ x, u x ^ 2 ∂μ) ^ 3 ≤ (∫ x, u x ∂μ) ^ 2 * ∫ x, u x ^ 4 ∂μ := by
  have hpq : (3 / 2 : ℝ).HolderConjugate 3 := by
    constructor <;> norm_num
  have hf : Measurable (fun x => u x ^ (2 / 3 : ℝ)) := hu.pow_const _
  have hg : Measurable (fun x => u x ^ (4 / 3 : ℝ)) := hu.pow_const _
  have hf0 (x : Ω) : 0 ≤ u x ^ (2 / 3 : ℝ) := Real.rpow_nonneg (hu0 x) _
  have hg0 (x : Ω) : 0 ≤ u x ^ (4 / 3 : ℝ) := Real.rpow_nonneg (hu0 x) _
  have he1 (x : Ω) : (u x ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = u x := by
    rw [← Real.rpow_mul (hu0 x)]
    norm_num
  have he4 (x : Ω) : (u x ^ (4 / 3 : ℝ)) ^ (3 : ℝ) = u x ^ 4 := by
    rw [← Real.rpow_mul (hu0 x)]
    norm_num
  have he2 (x : Ω) : u x ^ (2 / 3 : ℝ) * u x ^ (4 / 3 : ℝ) = u x ^ 2 := by
    rw [← Real.rpow_add' (hu0 x) (by norm_num : (2 / 3 : ℝ) + 4 / 3 ≠ 0)]
    norm_num
  have hflp : MemLp (fun x => u x ^ (2 / 3 : ℝ)) (ENNReal.ofReal (3 / 2)) μ := by
    apply (integrable_norm_rpow_iff hf.aestronglyMeasurable (by norm_num) (by simp)).mp
    simpa only [Real.norm_of_nonneg (hf0 _),
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2), he1] using h1
  have hglp : MemLp (fun x => u x ^ (4 / 3 : ℝ)) (ENNReal.ofReal 3) μ := by
    apply (integrable_norm_rpow_iff hg.aestronglyMeasurable (by norm_num) (by simp)).mp
    simpa only [Real.norm_of_nonneg (hg0 _),
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3), he4] using h4
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall hf0) (Eventually.of_forall hg0) hflp hglp
  simp only [he1, he4, he2] at h
  norm_num only [one_div_div] at h
  have hcube := pow_le_pow_left₀
    (integral_nonneg (fun x => sq_nonneg (u x))) h 3
  rw [mul_pow, ← Real.rpow_mul_natCast (integral_nonneg hu0),
    ← Real.rpow_mul_natCast (integral_nonneg (fun x => pow_nonneg (hu0 x) 4))] at hcube
  norm_num at hcube
  exact hcube

private lemma tail_lower_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} {L R : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hL : 0 ≤ L) (hR : 0 < R)
    (hmean : L / 2 ≤ ∫ x, f x ∂μ) (hsq : (∫ x, f x ^ 2 ∂μ) ≤ R) :
    L ^ 2 / (16 * R) ≤ μ.real {x | L / 4 < f x} := by
  let s := {x | L / 4 < f x}
  have hs : MeasurableSet s := measurableSet_lt measurable_const hf
  have htrunc : (∫ x, f x ∂μ) ≤ L / 4 + ∫ x in s, f x ∂μ := by
    have hp (x : Ω) : f x ≤ L / 4 + s.indicator f x := by
      by_cases hx : x ∈ s
      · rw [indicator_of_mem hx]; linarith
      · rw [indicator_of_notMem hx]
        simpa only [add_zero] using (le_of_not_gt hx : f x ≤ L / 4)
    have hi := integral_mono hf1 ((integrable_const (L / 4)).add (hf1.indicator hs)) hp
    simp only [Pi.add_apply] at hi
    simpa only [integral_add (integrable_const (L / 4)) (hf1.indicator hs),
      integral_const, probReal_univ, smul_eq_mul, one_mul, integral_indicator hs] using hi
  have hc := cs_sq (μ := μ.restrict s) hf measurable_const hf0 (fun _ => zero_le_one)
    hf2.integrableOn (by simpa only [one_pow] using (integrable_const (1 : ℝ) (μ := μ.restrict s)))
  simp only [mul_one, one_pow, integral_const, measureReal_restrict_apply_univ,
    smul_eq_mul, mul_one] at hc
  have hmono : (∫ x in s, f x ^ 2 ∂μ) ≤ ∫ x, f x ^ 2 ∂μ :=
    integral_mono_measure Measure.restrict_le_self (Eventually.of_forall (fun x => sq_nonneg _)) hf2
  have hmass : 0 ≤ μ.real s := ENNReal.toReal_nonneg
  have htail : L / 4 ≤ ∫ x in s, f x ∂μ := by linarith
  have htail2 := pow_le_pow_left₀ (by positivity : 0 ≤ L / 4) htail 2
  have hbound := mul_le_mul_of_nonneg_right (hmono.trans hsq) hmass
  apply (div_le_iff₀ (by positivity : 0 < 16 * R)).2
  nlinarith

private lemma lambda_sq {v K : ℝ} (hv : 0 < v) (hK : 0 < fourthMomentK1 v K) :
    fourthMomentLambda v K ^ 2 * fourthMomentK1 v K = (v / 2) ^ 3 := by
  have hp : ((v / 2) ^ (3 / 2 : ℝ)) ^ 2 = (v / 2) ^ (3 : ℕ) := by
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ v / 2)]
    norm_num
  unfold fourthMomentLambda
  rw [div_pow, Real.sq_sqrt hK.le, div_mul_cancel₀ _ hK.ne', hp]


private lemma centered_positive_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {W : Ω → ℝ} {L R : ℝ}
    (hW : Measurable W) (hW1 : Integrable W μ)
    (hW2 : Integrable (fun x => W x ^ 2) μ)
    (hzero : (∫ x, W x ∂μ) = 0)
    (hL : 0 ≤ L) (hR : 0 < R)
    (habs : L ≤ ∫ x, |W x| ∂μ) (hsq : (∫ x, W x ^ 2 ∂μ) ≤ R) :
    L ^ 2 / (16 * R) ≤ μ.real {x | L / 4 < W x} := by
  have hp2 : Integrable (fun x => max (W x) 0 ^ 2) μ :=
    ((memLp_two_iff_integrable_sq hW.aestronglyMeasurable).2 hW2).pos_part.integrable_sq
  have hpbound (x : Ω) : max (W x) 0 ^ 2 ≤ W x ^ 2 := by
    by_cases hx : 0 ≤ W x
    · rw [max_eq_left hx]
    · rw [max_eq_right (le_of_not_ge hx), zero_pow (by decide : (2 : ℕ) ≠ 0)]; exact sq_nonneg _
  have hpmean : L / 2 ≤ ∫ x, max (W x) 0 ∂μ := by
    have heq := integral_abs_eq_two_mul_integral_posPart_sub_integral hW1
    simp only [hzero, sub_zero, PosPart.posPart] at heq
    linarith
  have htail := tail_lower_bound (hW.max measurable_const) (fun x => le_max_right _ _)
    hW1.pos_part hp2 hL hR hpmean ((integral_mono hp2 hW2 hpbound).trans hsq)
  have heq : {x | L / 4 < max (W x) 0} = {x | L / 4 < W x} := by
    ext x
    simp only [mem_ofPred_eq, lt_max_iff, not_lt.mpr (by positivity : 0 ≤ L / 4), or_false]
  rwa [heq] at htail

/-- A positive second moment, bounded fourth moment and small mean give a uniform
positive lower bound for both strict tails. -/
private theorem two_sided_positive_proportion_of_measurable_moments
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} {v K : ℝ}
    (hZ : Measurable Z)
    (hZ1 : Integrable Z μ)
    (hZ2 : Integrable (fun ω => Z ω ^ 2) μ)
    (hZ4 : Integrable (fun ω => Z ω ^ 4) μ)
    (hv : 0 < v)
    (h₂ : v ≤ ∫ ω, Z ω ^ 2 ∂μ)
    (h₄ : ∫ ω, |Z ω| ^ 4 ∂μ ≤ K)
    (hε : |∫ ω, Z ω ∂μ| ≤
      min (Real.sqrt (v / 2)) (fourthMomentLambda v K / 8)) :
    ENNReal.ofReal (fourthMomentDensity v K) ≤
        μ {ω | Z ω > fourthMomentThreshold v K} ∧
    ENNReal.ofReal (fourthMomentDensity v K) ≤
        μ {ω | Z ω < -fourthMomentThreshold v K} := by
  let m := ∫ ω, Z ω ∂μ
  let W := fun ω => Z ω - m
  let L := fourthMomentLambda v K
  let R := Real.sqrt (fourthMomentK1 v K)
  have h4abs (z : ℝ) : |z| ^ 4 = z ^ 4 := by
    calc
      _ = (|z| ^ 2) ^ 2 := by ring
      _ = (z ^ 2) ^ 2 := by rw [sq_abs]
      _ = _ := by ring
  have hZ4bound : (∫ ω, Z ω ^ 4 ∂μ) ≤ K := by simpa only [h4abs] using h₄
  have hK0 : 0 ≤ K := (integral_nonneg (fun ω => pow_nonneg (sq_nonneg (Z ω)) 2) :
      0 ≤ ∫ ω, (Z ω ^ 2) ^ 2 ∂μ).trans (by simpa only [← pow_mul] using hZ4bound)
  have hK1 : 0 < fourthMomentK1 v K := by unfold fourthMomentK1; positivity
  have hR : 0 < R := Real.sqrt_pos.2 hK1
  have hL : 0 < L := div_pos (Real.rpow_pos_of_pos (by positivity) _) hR
  have hLsq : L ^ 2 * fourthMomentK1 v K = (v / 2) ^ 3 := lambda_sq hv hK1
  have hm1 : |m| ≤ Real.sqrt (v / 2) := hε.trans (min_le_left _ _)
  have hm2 : |m| ≤ L / 8 := hε.trans (min_le_right _ _)
  have hm_sq : m ^ 2 ≤ v / 2 := by
    have hs := pow_le_pow_left₀ (abs_nonneg m) hm1 2
    simpa only [sq_abs, Real.sq_sqrt (by positivity : 0 ≤ v / 2)] using hs
  have hm_fourth : m ^ 4 ≤ v ^ 2 / 4 := by
    have hs := pow_le_pow_left₀ (sq_nonneg m) hm_sq 2
    nlinarith
  have hW : Measurable W := hZ.sub measurable_const
  have hW1 : Integrable W μ := hZ1.sub (integrable_const m)
  have hWlp : MemLp W 2 μ :=
    ((memLp_two_iff_integrable_sq hZ.aestronglyMeasurable).2 hZ2).sub (memLp_const m)
  have hW2 := hWlp.integrable_sq
  have hzero : (∫ ω, W ω ∂μ) = 0 := by
    dsimp only [W]
    rw [integral_sub hZ1 (integrable_const m), integral_const, probReal_univ, one_smul]
    exact sub_self m
  have hW2eq : (∫ ω, W ω ^ 2 ∂μ) = (∫ ω, Z ω ^ 2 ∂μ) - m ^ 2 := by
    rw [← ProbabilityTheory.variance_eq_integral hZ.aemeasurable,
      ProbabilityTheory.variance_eq_sub
        ((memLp_two_iff_integrable_sq hZ.aestronglyMeasurable).2 hZ2)]
    rfl
  have hW2lower : v / 2 ≤ ∫ ω, W ω ^ 2 ∂μ := by rw [hW2eq]; linarith
  have hpoint (ω : Ω) : W ω ^ 4 ≤ 8 * (Z ω ^ 4 + m ^ 4) := by
    have hh := (show Even (4 : ℕ) by decide).add_pow_le (a := Z ω) (b := -m)
    simpa only [W, sub_eq_add_neg, show (-m) ^ 4 = m ^ 4 by ring,
      show (2 : ℝ) ^ (4 - 1 : ℕ) = 8 by norm_num] using hh
  have hW4 : Integrable (fun ω => W ω ^ 4) μ := by
    apply ((hZ4.add (integrable_const (m ^ 4))).const_mul 8).mono'
      (hW.pow_const 4).aestronglyMeasurable
    filter_upwards [] with ω
    simpa only [Pi.add_apply, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ W ω ^ 4)] using hpoint ω
  have hW4bound : (∫ ω, W ω ^ 4 ∂μ) ≤ fourthMomentK1 v K := by
    have hh := integral_mono hW4 ((hZ4.add (integrable_const (m ^ 4))).const_mul 8) hpoint
    simp only [Pi.add_apply] at hh
    rw [integral_const_mul, integral_add hZ4 (integrable_const (m ^ 4)),
      integral_const, probReal_univ, one_smul] at hh
    unfold fourthMomentK1
    linarith
  have hinterp := moment_interpolation
    (show Measurable (fun ω => |W ω|) by fun_prop) (fun ω => abs_nonneg _) hW1.abs
    (by simpa only [h4abs] using hW4)
  simp only [sq_abs, h4abs] at hinterp
  have habs : L ≤ ∫ ω, |W ω| ∂μ := by
    have hb := pow_le_pow_left₀ (by positivity : 0 ≤ v / 2) hW2lower 3
    have hc := mul_le_mul_of_nonneg_left hW4bound (sq_nonneg (∫ ω, |W ω| ∂μ))
    have hs : L ^ 2 ≤ (∫ ω, |W ω| ∂μ) ^ 2 := by
      apply (mul_le_mul_iff_right₀ hK1).mp
      nlinarith
    have ha : 0 ≤ ∫ ω, |W ω| ∂μ := integral_nonneg (fun ω => abs_nonneg _)
    nlinarith
  have hW2upper : (∫ ω, W ω ^ 2 ∂μ) ≤ R := by
    have hc := cs_sq (hW.pow_const 2) measurable_const (fun ω => sq_nonneg _)
      (fun _ => zero_le_one)
      (show Integrable (fun ω => (W ω ^ 2) ^ 2) μ by simpa only [← pow_mul] using hW4)
      (show Integrable (fun _ : Ω => (1 : ℝ) ^ 2) μ by
        simpa only [one_pow] using integrable_const (1 : ℝ))
    simp only [mul_one, one_pow, integral_const, probReal_univ, one_smul,
      show (fun ω => (W ω ^ 2) ^ 2) = (fun ω => W ω ^ 4) by funext ω; ring] at hc
    have hRsq : R ^ 2 = fourthMomentK1 v K := Real.sq_sqrt hK1.le
    nlinarith
  have hpos := centered_positive_tail hW hW1 hW2 hzero hL.le hR habs hW2upper
  have hneg := centered_positive_tail hW.neg hW1.neg
    (show Integrable (fun ω => (-W ω) ^ 2) μ by simpa only [neg_sq] using hW2)
    (show (∫ ω, -W ω ∂μ) = 0 by rw [integral_neg, hzero, neg_zero]) hL.le hR
    (show L ≤ ∫ ω, |-W ω| ∂μ by simpa only [abs_neg] using habs)
    (show (∫ ω, (-W ω) ^ 2 ∂μ) ≤ R by simpa only [neg_sq] using hW2upper)
  have hsubpos : {ω | L / 4 < W ω} ⊆ {ω | Z ω > fourthMomentThreshold v K} := by
    intro ω hω
    have hm := neg_abs_le m
    change L / 4 < Z ω - m at hω
    change L / 8 < Z ω
    linarith
  have hsubneg : {ω | L / 4 < -W ω} ⊆ {ω | Z ω < -fourthMomentThreshold v K} := by
    intro ω hω
    have hm := le_abs_self m
    change L / 4 < -(Z ω - m) at hω
    change Z ω < -(L / 8)
    linarith
  constructor
  · exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).2
      (hpos.trans (measureReal_mono hsubpos))
  · exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).2
      (hneg.trans (measureReal_mono hsubneg))

/-- Almost everywhere measurable moment data suffice for both strict tail bounds. -/
theorem two_sided_positive_proportion_of_moments
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} {v K : ℝ}
    (hZ : AEStronglyMeasurable Z μ)
    (hZ1 : Integrable Z μ)
    (hZ2 : Integrable (fun ω => Z ω ^ 2) μ)
    (hZ4 : Integrable (fun ω => Z ω ^ 4) μ)
    (hv : 0 < v)
    (h₂ : v ≤ ∫ ω, Z ω ^ 2 ∂μ)
    (h₄ : ∫ ω, |Z ω| ^ 4 ∂μ ≤ K)
    (hε : |∫ ω, Z ω ∂μ| ≤
      min (Real.sqrt (v / 2)) (fourthMomentLambda v K / 8)) :
    ENNReal.ofReal (fourthMomentDensity v K) ≤
        μ {ω | Z ω > fourthMomentThreshold v K} ∧
    ENNReal.ofReal (fourthMomentDensity v K) ≤
        μ {ω | Z ω < -fourthMomentThreshold v K} := by
  let Z' := hZ.mk Z
  have he : Z =ᵐ[μ] Z' := hZ.ae_eq_mk
  have he2 : (fun ω => Z ω ^ 2) =ᵐ[μ] (fun ω => Z' ω ^ 2) := he.pow_const 2
  have he4 : (fun ω => Z ω ^ 4) =ᵐ[μ] (fun ω => Z' ω ^ 4) := he.pow_const 4
  have hea4 : (fun ω => |Z ω| ^ 4) =ᵐ[μ] (fun ω => |Z' ω| ^ 4) :=
    (he.fun_comp abs).pow_const 4
  have ht := two_sided_positive_proportion_of_measurable_moments (v := v) (K := K)
    hZ.measurable_mk (hZ1.congr he) (hZ2.congr he2) (hZ4.congr he4) hv
    (by rwa [← integral_congr_ae he2])
    (by rwa [← integral_congr_ae hea4])
    (by rwa [← integral_congr_ae he])
  have hp : μ {ω | Z ω > fourthMomentThreshold v K} =
      μ {ω | Z' ω > fourthMomentThreshold v K} := by
    apply measure_congr
    filter_upwards [he] with ω hω
    simp only [hω]
  have hn : μ {ω | Z ω < -fourthMomentThreshold v K} =
      μ {ω | Z' ω < -fourthMomentThreshold v K} := by
    apply measure_congr
    filter_upwards [he] with ω hω
    simp only [hω]
  rwa [hp, hn]

end
end D5.S3.Arith.Robin.ForwardKernel.FourthMomentProbability
