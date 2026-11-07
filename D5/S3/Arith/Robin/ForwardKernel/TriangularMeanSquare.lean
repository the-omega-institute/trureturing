/- GID: D5/S3/Arith/Robin/ForwardKernel/TriangularMeanSquare
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/TriangularMeanSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-length profile averages converge to the min-kernel quadratic energy. -/

import D5.S3.Arith.Robin.ForwardKernel.VarianceTransferDefs
import D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer
import D5.S3.Arith.Robin.ForwardKernel.FixedLengthCovariance
import D5.S3.Arith.Robin.ForwardKernel.MovingLengthVariance
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Fixed-length profile mean squares from covariance convergence on the full unit square. -/

namespace D5.S3.Arith.Robin.ForwardKernel.TriangularMeanSquare

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs VarianceTransfer FixedLengthCovariance

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The covariance integral is measurable in both increment lengths. -/
private theorem covariance_measurable {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    (h A B : ℝ) : Measurable (fun p : ℝ × ℝ =>
      ∫ x in A..B, increment E (p.1 * h) x * increment E (p.2 * h) x) := by
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      increment E (p.1.1 * h) p.2 * increment E (p.1.2 * h) p.2) := by
    unfold increment
    exact ((hE.1.comp (measurable_snd.add (measurable_fst.fst.mul_const h))).sub
      (hE.1.comp measurable_snd)).mul
      ((hE.1.comp (measurable_snd.add (measurable_fst.snd.mul_const h))).sub
        (hE.1.comp measurable_snd))
  unfold intervalIntegral
  exact (hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc A B))).measurable.sub
    (hm.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc B A))).measurable

/-- A perturbation negligible in normalized squared L2 norm preserves a mean-square limit. -/
theorem interval_square_tendsto_of_l2_negligible
    {A B S : ℝ → ℝ} {f g : ℝ → ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L)
    (hAB : ∀ᶠ X in atTop, A X ≤ B X)
    (hS : ∀ᶠ X in atTop, 0 < S X)
    (hf : ∀ᶠ X in atTop, MemLp (f X) 2 (volume.restrict (Ioc (A X) (B X))))
    (hg : ∀ᶠ X in atTop, MemLp (g X) 2 (volume.restrict (Ioc (A X) (B X))))
    (hgLimit : Tendsto (fun X => (∫ x in (A X)..(B X), g X x ^ 2) / S X)
      atTop (𝓝 L))
    (hfgLimit : Tendsto (fun X => (∫ x in (A X)..(B X), (f X x - g X x) ^ 2) / S X)
      atTop (𝓝 0)) :
    Tendsto (fun X => (∫ x in (A X)..(B X), f X x ^ 2) / S X) atTop (𝓝 L) := by
  have hdiff : Tendsto (fun X =>
      Real.sqrt ((∫ x in (A X)..(B X), f X x ^ 2) / S X) -
        Real.sqrt ((∫ x in (A X)..(B X), g X x ^ 2) / S X)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hd := hfgLimit.sqrt
    simp only [Real.sqrt_zero] at hd
    apply squeeze_zero' (Eventually.of_forall (fun X => norm_nonneg _)) ?_ hd
    filter_upwards [hAB, hS, hf, hg] with X hAB hS hf hg
    have hn (q : ℝ → ℝ) : 0 ≤ ∫ x in (A X)..(B X), q x ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hAB (fun x => sq_nonneg _)
    simp only [Real.norm_eq_abs]
    rw [Real.sqrt_div (hn (f X)), Real.sqrt_div (hn (g X)),
      Real.sqrt_div (hn (fun x => f X x - g X x)), ← sub_div, abs_div,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_div_of_nonneg_right (interval_l2_reverse_triangle hAB hf hg)
      (Real.sqrt_nonneg _)
  have hroot := hdiff.add hgLimit.sqrt
  simp only [zero_add] at hroot
  have hroot' : Tendsto (fun X =>
      Real.sqrt ((∫ x in (A X)..(B X), f X x ^ 2) / S X)) atTop (𝓝 (Real.sqrt L)) := by
    convert hroot using 1
    ext X
    ring
  have hsq := hroot'.pow 2
  rw [Real.sq_sqrt hL] at hsq
  apply hsq.congr'
  filter_upwards [hAB, hS] with X hAB hS
  exact Real.sq_sqrt (div_nonneg
    (intervalIntegral.integral_nonneg_of_forall hAB (fun x => sq_nonneg _)) hS.le)

private theorem profile_square_eq_covariance {E g : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hg : ProfileIntegrable g)
    {A B h : ℝ} (hAB : A ≤ B) (hh : 0 ≤ h) :
    (∫ x in A..B, (∫ s in (0 : ℝ)..1, g s * increment E (s * h) x) ^ 2) =
      ∫ p : ℝ × ℝ, g p.1 * g p.2 *
        (∫ x in A..B, increment E (p.1 * h) x * increment E (p.2 * h) x)
        ∂unitMeasure.prod unitMeasure := by
  let μ := volume.restrict (Ioc A B)
  obtain ⟨M, hM, hMb⟩ := hE.2 A (B + h)
  have hm : Measurable (fun p : ℝ × (ℝ × ℝ) =>
      increment E (p.2.1 * h) p.1 * increment E (p.2.2 * h) p.1) := by
    have hEm : Measurable E := hE.1
    unfold increment
    fun_prop
  have hi : Integrable (fun p : ℝ × (ℝ × ℝ) =>
      g p.2.1 * g p.2.2 *
        (increment E (p.2.1 * h) p.1 * increment E (p.2.2 * h) p.1))
      (μ.prod (unitMeasure.prod unitMeasure)) := by
    apply ((hg.2.mul_prod hg.2).comp_snd (μ := μ)).mul_bdd
      (c := (2 * M) * (2 * M)) hm.aestronglyMeasurable
    have hmem : ∀ᵐ p : ℝ × (ℝ × ℝ) ∂μ.prod (unitMeasure.prod unitMeasure),
        p ∈ Ioc A B ×ˢ (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) := by
      dsimp [μ]
      rw [Measure.prod_restrict, Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioc.prod
        (measurableSet_Ioc.prod measurableSet_Ioc))
    filter_upwards [hmem] with p hp
    have hb (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
        |increment E (s * h) p.1| ≤ 2 * M := by
      apply (abs_sub _ _).trans
      have hsh : 0 ≤ s * h := mul_nonneg hs.1.le hh
      have hsh' : s * h ≤ h := mul_le_of_le_one_left hh hs.2
      exact (add_le_add (hMb _ ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩)
        (hMb _ ⟨hp.1.1.le, by linarith [hp.1.2]⟩)).trans_eq (by ring)
    simpa only [Real.norm_eq_abs, abs_mul] using
      mul_le_mul (hb _ hp.2.1) (hb _ hp.2.2) (abs_nonneg _) (by positivity : 0 ≤ 2 * M)
  simp_rw [intervalIntegral.integral_of_le hAB,
    intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  calc
    _ = ∫ x, ∫ p : ℝ × ℝ, g p.1 * g p.2 *
        (increment E (p.1 * h) x * increment E (p.2 * h) x)
        ∂unitMeasure.prod unitMeasure ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [pow_two, ← integral_prod_mul]
      congr 1
      funext p
      ring
    _ = ∫ p : ℝ × ℝ, ∫ x, g p.1 * g p.2 *
        (increment E (p.1 * h) x * increment E (p.2 * h) x)
        ∂μ ∂unitMeasure.prod unitMeasure := integral_integral_swap hi
    _ = _ := by simp_rw [integral_const_mul]; rfl

private theorem covariance_bound {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β)
    {a b c : ℝ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ 2) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        |(∫ x in (a * X)..(b * X),
          increment E (s * fixedLength θ c X) x *
            increment E (t * fixedLength θ c X) x) /
          (X * fixedLength θ c X * lengthLog θ c X)| ≤ C := by
  obtain ⟨C, hC, hCv⟩ := MovingLengthVariance.shorter_increment_square_bound hE hB hV hc
  refine ⟨C, hC, ?_⟩
  filter_upwards [hCv, eventually_gt_atTop (0 : ℝ),
    (length_log_tendsto (hB.2.2.1.trans hB.2.2.2) hc).eventually
      (eventually_gt_atTop (0 : ℝ))] with X hCv hX hL
  have hh : 0 < fixedLength θ c X := by unfold fixedLength; positivity
  have hN : 0 < X * fixedLength θ c X * lengthLog θ c X := by positivity
  have hAB := mul_le_mul_of_nonneg_right hab.le hX.le
  have hi (u v A B : ℝ) : IntervalIntegrable
      (fun x => increment E u x * increment E v x) volume A B :=
    (increment_product_comp_integrableOn hE isCompact_uIcc
      continuous_const continuous_id continuous_const continuous_id).intervalIntegrable
  have hsquare (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (fixedLength θ c X)) :
      (∫ x in (a * X)..(b * X), increment E u x ^ 2) ≤
        C * (X * fixedLength θ c X * lengthLog θ c X) := by
    have hmono := intervalIntegral.integral_mono_interval
      (show X ≤ a * X by nlinarith) hAB (show b * X ≤ 2 * X by nlinarith)
      (Eventually.of_forall fun x => sq_nonneg (increment E u x))
      (show IntervalIntegrable (fun x => increment E u x ^ 2) volume X (2 * X) by
        simpa only [pow_two] using hi u u X (2 * X))
    exact (hmono.trans (hCv u hu)).trans_eq (by ring)
  intro s hs t ht
  have hs' : s * fixedLength θ c X ∈ Icc (0 : ℝ) (fixedLength θ c X) :=
    ⟨mul_nonneg hs.1 hh.le, mul_le_of_le_one_left hh.le hs.2⟩
  have ht' : t * fixedLength θ c X ∈ Icc (0 : ℝ) (fixedLength θ c X) :=
    ⟨mul_nonneg ht.1 hh.le, mul_le_of_le_one_left hh.le ht.2⟩
  rw [abs_div, abs_of_pos hN]
  apply (div_le_iff₀ hN).mpr
  apply (intervalIntegral.abs_integral_le_integral_abs hAB).trans
  calc
    _ ≤ ∫ x in (a * X)..(b * X),
        (increment E (s * fixedLength θ c X) x ^ 2 +
          increment E (t * fixedLength θ c X) x ^ 2) / 2 := by
      apply intervalIntegral.integral_mono_on hAB (hi _ _ _ _).abs
        (by simpa only [pow_two] using ((hi _ _ _ _).add (hi _ _ _ _)).div_const 2)
      intro x hx
      rw [abs_mul]
      nlinarith [sq_nonneg (|increment E (s * fixedLength θ c X) x| -
        |increment E (t * fixedLength θ c X) x|),
        sq_abs (increment E (s * fixedLength θ c X) x),
        sq_abs (increment E (t * fixedLength θ c X) x)]
    _ ≤ _ := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_add
        (by simpa only [pow_two] using
          hi (s * fixedLength θ c X) (s * fixedLength θ c X) _ _)
        (by simpa only [pow_two] using
          hi (t * fixedLength θ c X) (t * fixedLength θ c X) _ _)]
      linarith [hsquare _ hs', hsquare _ ht']

/-- Fixed-length profile averages have the min-kernel energy as their normalized mean-square limit. -/
theorem fixed_length_profile_mean_square_tendsto
    {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β)
    {g : ℝ → ℝ} (hg : ProfileIntegrable g)
    {a b c : ℝ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ 2) (hc : 0 < c) :
    Tendsto (fun X =>
      (∫ x in (a * X)..(b * X), profileAverage E g (fixedLength θ c X) x ^ 2) /
        (X / fixedLength θ c X * lengthLog θ c X))
      atTop (𝓝 ((b - a) * Q g)) := by
  let μ := unitMeasure.prod unitMeasure
  let K (X : ℝ) (p : ℝ × ℝ) :=
    (∫ x in (a * X)..(b * X), increment E (p.1 * fixedLength θ c X) x *
      increment E (p.2 * fixedLength θ c X) x) /
        (X * fixedLength θ c X * lengthLog θ c X)
  have hmem : ∀ᵐ p : ℝ × ℝ ∂μ, p ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
    dsimp [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
  obtain ⟨C, hC, hCv⟩ := covariance_bound hE hB hV ha hab hb hc
  have hmeas : ∀ᶠ X : ℝ in atTop,
      AEStronglyMeasurable (fun p => g p.1 * g p.2 * K X p) μ := by
    apply Eventually.of_forall
    intro X
    exact (((hg.1.comp measurable_fst).mul (hg.1.comp measurable_snd)).mul
      ((covariance_measurable hE _ _ _).div_const _)).aestronglyMeasurable
  have hbound : ∀ᶠ X : ℝ in atTop, ∀ᵐ p : ℝ × ℝ ∂μ,
      ‖g p.1 * g p.2 * K X p‖ ≤ C * |g p.1 * g p.2| := by
    filter_upwards [hCv] with X hCv
    filter_upwards [hmem] with p hp
    rw [Real.norm_eq_abs, abs_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left
      (hCv _ ⟨hp.1.1.le, hp.1.2⟩ _ ⟨hp.2.1.le, hp.2.2⟩) (abs_nonneg _)
  have hlim : ∀ᵐ p : ℝ × ℝ ∂μ, Tendsto (fun X => g p.1 * g p.2 * K X p)
      atTop (𝓝 (g p.1 * g p.2 * ((b - a) * min p.1 p.2))) := by
    filter_upwards [hmem] with p hp
    exact (fixed_length_covariance_tendsto hE hB hV ha hab hb hc
      ⟨hp.1.1.le, hp.1.2⟩ ⟨hp.2.1.le, hp.2.2⟩).const_mul _
  have hmajor : Integrable (fun p : ℝ × ℝ => C * |g p.1 * g p.2|) μ :=
    (hg.2.mul_prod hg.2).abs.const_mul C
  have henergy : Integrable (fun p : ℝ × ℝ => g p.1 * g p.2 * min p.1 p.2) μ := by
    apply (hg.2.mul_prod hg.2).mul_bdd (c := 1)
      ((measurable_fst.min measurable_snd).aestronglyMeasurable)
    filter_upwards [hmem] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hp.1.1.le hp.2.1.le)]
    exact (min_le_left _ _).trans hp.1.2
  have he : (∫ p : ℝ × ℝ, g p.1 * g p.2 * ((b - a) * min p.1 p.2) ∂μ) =
      (b - a) * Q g := by
    simp_rw [show ∀ p : ℝ × ℝ, g p.1 * g p.2 * ((b - a) * min p.1 p.2) =
      (b - a) * (g p.1 * g p.2 * min p.1 p.2) by intro p; ring]
    rw [integral_const_mul, integral_prod _ henergy]
    simp only [Q, intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun p : ℝ × ℝ => C * |g p.1 * g p.2|) hmeas hbound hmajor hlim
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  have hh : 0 < fixedLength θ c X := by unfold fixedLength; positivity
  dsimp only [K]
  simp_rw [← mul_div_assoc]
  rw [integral_div]
  simp_rw [profileAverage_eq_unit_integral, div_pow]
  rw [intervalIntegral.integral_div,
    ← profile_square_eq_covariance hE hg (mul_le_mul_of_nonneg_right hab.le hX.le) hh.le]
  field_simp
  simp only [mul_comm]

end
end D5.S3.Arith.Robin.ForwardKernel.TriangularMeanSquare
