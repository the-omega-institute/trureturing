/- GID: D5/S3/Arith/Robin/ForwardKernel/ProfileCrossIntegral
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/ProfileCrossIntegral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform covariance bounds transfer to cross integrals of price-weighted profiles. -/

import D5.S3.Arith.Robin.ForwardKernel.ProfileKernelDefs
import D5.S3.Arith.Robin.ForwardKernel.WeightControl
import D5.S3.Arith.Robin.ForwardKernel.WeightRemoval
import D5.S3.Arith.Robin.ForwardKernel.CrossExponentDefs
import D5.S3.Arith.Robin.ForwardKernel.WeightedPrimitiveBound

/-! Uniform covariance bounds transfer to price-weighted profile responses. -/

namespace D5.S3.Arith.Robin.ForwardKernel.ProfileCrossIntegral

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs ProfileKernelDefs CrossExponentDefs

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def crossWeight (a b s t x : ℝ) : ℝ :=
  x ^ (-a - b) * priceRatio x (s * x ^ a) * priceRatio x (t * x ^ b)

private lemma ratio_contDiffAt {θ s x : ℝ} (hx : 1 < x) (hs : 0 ≤ s) :
    ContDiffAt ℝ 1 (fun y => priceRatio y (s * y ^ θ)) x := by
  have hx0 : 0 < x := by linarith
  have hy : 1 < x + s * x ^ θ := by
    have := mul_nonneg hs (Real.rpow_nonneg hx0.le θ)
    linarith
  have hw (z : ℝ) (hz : 1 < z) :
      ContDiffAt ℝ 1 MellinWeightedVariation.weight z := by
    have hz0 : z ≠ 0 := ne_of_gt (by linarith)
    have hl := (Real.contDiffAt_log.mpr hz0 : ContDiffAt ℝ 1 Real.log z)
    exact (hl.add contDiffAt_const).div
      ((contDiffAt_id.pow 2).mul (hl.pow 2))
      (mul_ne_zero (pow_ne_zero _ hz0) (pow_ne_zero _ (Real.log_pos hz).ne'))
  exact ((hw _ hy).comp x
    (contDiffAt_id.add (contDiffAt_const.mul
      (Real.contDiffAt_rpow_const_of_ne hx0.ne')))).div (hw _ hx)
        (OriginalMovingWindowMoment.weight_pos hx).ne'

lemma crossWeight_contDiffOn {a b s t X : ℝ} (hX : 4 ≤ X)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ContDiffOn ℝ 1 (crossWeight a b s t) (uIcc X (2 * X)) := by
  rw [uIcc_of_le (by linarith : X ≤ 2 * X)]
  intro x hx
  have hx1 : 1 < x := by linarith [hx.1]
  exact (((Real.contDiffAt_rpow_const_of_ne (by linarith : x ≠ 0)).mul
    (ratio_contDiffAt hx1 hs)).mul (ratio_contDiffAt hx1 ht)).contDiffWithinAt

private lemma ratio_deriv_bound {θ s x : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hx : 4 ≤ x) (hs : s ∈ Icc (0 : ℝ) 1) :
    |deriv (fun y => priceRatio y (s * y ^ θ)) x| ≤ 13 * x ^ (-1 : ℝ) := by
  obtain ⟨_, _, hd, hb⟩ := WeightControl.priceRatio_control hθ hx hs.1
  rw [hd.deriv]
  apply hb.trans
  have hp := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x)
    (by linarith : θ - 2 ≤ (-1 : ℝ))
  have hc : (8 + 5 * θ) * s ≤ 13 := by nlinarith [hs.1, hs.2]
  exact mul_le_mul hc hp (Real.rpow_nonneg (by linarith) _) (by norm_num)

private lemma crossWeight_deriv_bound {a b s t x : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    (hx : 4 ≤ x) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    |deriv (crossWeight a b s t) x| ≤
      (a + b + 26) * x ^ (-a - b - 1) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨hra0, hra1, hda, _⟩ := WeightControl.priceRatio_control ha hx hs.1
  obtain ⟨hrb0, hrb1, hdb, _⟩ := WeightControl.priceRatio_control hb hx ht.1
  have hd := ((Real.hasDerivAt_rpow_const (p := -a - b) (Or.inl hx0.ne')).mul hda).mul hdb
  change HasDerivAt (crossWeight a b s t) _ x at hd
  rw [hd.deriv, ← hda.deriv, ← hdb.deriv]
  simp only [Pi.mul_apply]
  have hda' := ratio_deriv_bound ha ha1 hx hs
  have hdb' := ratio_deriv_bound hb hb1 hx ht
  have hp : x ^ (-a - b) * x ^ (-1 : ℝ) = x ^ (-a - b - 1) := by
    rw [← Real.rpow_add hx0]; congr 1
  have h0 : 0 ≤ x ^ (-a - b) := Real.rpow_nonneg hx0.le _
  have h1 : 0 ≤ x ^ (-a - b - 1) := Real.rpow_nonneg hx0.le _
  have hpow : |(-a - b) * x ^ (-a - b - 1)| = (a + b) * x ^ (-a - b - 1) := by
    rw [abs_mul, abs_of_nonpos (by linarith : -a - b ≤ 0), abs_of_nonneg h1]
    ring
  calc
    _ ≤ (|(-a - b) * x ^ (-a - b - 1)| * |priceRatio x (s * x ^ a)| +
        x ^ (-a - b) * |deriv (fun y => priceRatio y (s * y ^ a)) x|) *
        |priceRatio x (t * x ^ b)| +
        x ^ (-a - b) * |priceRatio x (s * x ^ a)| *
          |deriv (fun y => priceRatio y (t * y ^ b)) x| := by
      calc
        _ ≤ |(-a - b) * x ^ (-a - b - 1) * priceRatio x (s * x ^ a) +
            x ^ (-a - b) * deriv (fun y => priceRatio y (s * y ^ a)) x| *
            |priceRatio x (t * x ^ b)| +
            |x ^ (-a - b) * priceRatio x (s * x ^ a) *
              deriv (fun y => priceRatio y (t * y ^ b)) x| := by
          simpa only [abs_mul] using abs_add_le
            (((-a - b) * x ^ (-a - b - 1) * priceRatio x (s * x ^ a) +
              x ^ (-a - b) * deriv (fun y => priceRatio y (s * y ^ a)) x) *
              priceRatio x (t * x ^ b))
            (x ^ (-a - b) * priceRatio x (s * x ^ a) * deriv (fun y => priceRatio y (t * y ^ b)) x)
        _ ≤ _ := by
          simp only [abs_mul, abs_of_nonneg h0]
          gcongr
          simpa only [abs_mul, abs_of_nonneg h0] using abs_add_le
            ((-a - b) * x ^ (-a - b - 1) * priceRatio x (s * x ^ a))
            (x ^ (-a - b) * deriv (fun y => priceRatio y (s * y ^ a)) x)
    _ ≤ ((a + b) * x ^ (-a - b - 1) * 1 + x ^ (-a - b) * (13 * x ^ (-1 : ℝ))) * 1 +
        x ^ (-a - b) * 1 * (13 * x ^ (-1 : ℝ)) := by
      rw [hpow, abs_of_nonneg hra0, abs_of_nonneg hrb0]
      gcongr
    _ = _ := by nlinarith [hp]

lemma crossWeight_variation {a b s t X : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    (hX : 4 ≤ X) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    |crossWeight a b s t (2 * X)| + (∫ x in X..(2 * X), |deriv (crossWeight a b s t) x|) ≤
      (27 + a + b) * X ^ (-a - b) := by
  have hX0 : 0 < X := by linarith
  have hXX : X ≤ 2 * X := by linarith
  have hW := crossWeight_contDiffOn (a := a) (b := b) hX hs.1 ht.1
  have hi := hW.absolutelyContinuousOnInterval.intervalIntegrable_deriv.abs
  have hend : |crossWeight a b s t (2 * X)| ≤ X ^ (-a - b) := by
    obtain ⟨ha0', ha1', _, _⟩ := WeightControl.priceRatio_control ha
      (by linarith : 4 ≤ 2 * X) hs.1
    obtain ⟨hb0', hb1', _, _⟩ := WeightControl.priceRatio_control hb
      (by linarith : 4 ≤ 2 * X) ht.1
    rw [crossWeight, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
      abs_of_nonneg ha0', abs_of_nonneg hb0']
    calc
      _ ≤ (2 * X) ^ (-a - b) * 1 * 1 := by gcongr
      _ ≤ X ^ (-a - b) := by
        simpa using Real.rpow_le_rpow_of_nonpos hX0 hXX (by linarith : -a - b ≤ 0)
  have hint : (∫ x in X..(2 * X), |deriv (crossWeight a b s t) x|) ≤
      (a + b + 26) * X ^ (-a - b) := by
    calc
      _ ≤ ∫ _x in X..(2 * X), (a + b + 26) * X ^ (-a - b - 1) := by
        apply intervalIntegral.integral_mono_on hXX hi (intervalIntegrable_const)
        intro x hx
        exact (crossWeight_deriv_bound ha ha1 hb hb1 (hX.trans hx.1) hs ht).trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hX0 hx.1 (by linarith : -a - b - 1 ≤ 0))
            (by linarith))
      _ = (a + b + 26) * X ^ (-a - b) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        have hp : X * X ^ (-a - b - 1) = X ^ (-a - b) := by
          calc
            _ = X ^ (1 : ℝ) * X ^ (-a - b - 1) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add hX0]; congr 1; ring
        nlinarith [hp]
  nlinarith

private def crossKernel (E : ℝ → ℝ) (a b x : ℝ) (p : ℝ × ℝ) : ℝ :=
  crossWeight a b p.1 p.2 x * movingIncrement E a p.1 x * movingIncrement E b p.2 x

private lemma crossKernel_measurable {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (a b : ℝ) :
    Measurable (fun q : ℝ × (ℝ × ℝ) => crossKernel E a b q.1 q.2) := by
  have hr (θ : ℝ) (h : ℝ × (ℝ × ℝ) → ℝ) (hh : Measurable h) :
      Measurable (fun q : ℝ × (ℝ × ℝ) => priceRatio q.1 (h q * q.1 ^ θ)) :=
    WeightRemoval.price_measurable.comp
      (measurable_fst.prodMk (hh.mul (measurable_fst.pow_const θ)))
  exact ((((measurable_fst.pow_const (-a - b)).mul
    (hr a _ measurable_snd.fst)).mul (hr b _ measurable_snd.snd)).mul
    ((WeightRemoval.increment_measurable hE a).comp
      (measurable_fst.prodMk measurable_snd.fst))).mul
    ((WeightRemoval.increment_measurable hE b).comp
      (measurable_fst.prodMk measurable_snd.snd))

private lemma crossKernel_bound {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {a b X : ℝ} (ha : 0 < a) (hb : 0 < b) (hX : 4 ≤ X) :
    ∃ K : ℝ, ∀ x ∈ Icc X (2 * X), ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      |crossKernel E a b x p| ≤ K := by
  have hX0 : 0 < X := by linarith
  have hXX : X ≤ 2 * X := by linarith
  obtain ⟨M, hM, hMb⟩ := WeightRemoval.local_increment_bound hE a hX0 hXX
  obtain ⟨N, hN, hNb⟩ := WeightRemoval.local_increment_bound hE b hX0 hXX
  refine ⟨X ^ (-a - b) * M * N, ?_⟩
  intro x hx p hp
  have hx0 := hX0.trans_le hx.1
  have hra := WeightControl.price_bounds (by linarith [hx.1] : 3 ≤ x)
    (mul_nonneg hp.1.1 (Real.rpow_nonneg hx0.le a))
  have hrb := WeightControl.price_bounds (by linarith [hx.1] : 3 ≤ x)
    (mul_nonneg hp.2.1 (Real.rpow_nonneg hx0.le b))
  simp only [crossKernel, crossWeight, movingIncrement, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hx0.le (-a - b)), abs_of_nonneg hra.1,
    abs_of_nonneg hrb.1]
  have hxp := Real.rpow_le_rpow_of_nonpos hX0 hx.1 (by linarith : -a - b ≤ 0)
  have hw : x ^ (-a - b) * priceRatio x (p.1 * x ^ a) * priceRatio x (p.2 * x ^ b) ≤
      X ^ (-a - b) * 1 * 1 :=
    mul_le_mul (mul_le_mul hxp hra.2 hra.1 (Real.rpow_nonneg hX0.le _))
      hrb.2 hrb.1 (by positivity)
  simpa only [mul_one] using
    mul_le_mul (mul_le_mul hw (hMb x hx p.1 hp.1) (abs_nonneg _) (by positivity))
      (hNb x hx p.2 hp.2) (abs_nonneg _) (by positivity)

private lemma crossKernel_integrable {E g₁ g₂ : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hg₁ : ProfileIntegrable g₁)
    (hg₂ : ProfileIntegrable g₂) {a b X : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hX : 4 ≤ X) :
    Integrable (fun q : ℝ × (ℝ × ℝ) =>
      (g₁ q.2.1 * g₂ q.2.2) * crossKernel E a b q.1 q.2)
      ((volume.restrict (Ioc X (2 * X))).prod (unitMeasure.prod unitMeasure)) := by
  obtain ⟨K, hK⟩ := crossKernel_bound hE ha hb hX
  have hg := (integrable_const (1 : ℝ) :
    Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc X (2 * X)))).mul_prod
      (hg₁.2.mul_prod hg₂.2)
  simp only [one_mul] at hg
  apply hg.mul_bdd (c := K) (crossKernel_measurable hE a b).aestronglyMeasurable
  have hrect : ∀ᵐ q ∂((volume.restrict (Ioc X (2 * X))).prod
      (unitMeasure.prod unitMeasure)),
      q ∈ Ioc X (2 * X) ×ˢ (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) := by
    simp only [unitMeasure, Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod
      (measurableSet_Ioc.prod measurableSet_Ioc))
  filter_upwards [hrect] with q hq
  rw [Real.norm_eq_abs]
  exact hK q.1 ⟨hq.1.1.le, hq.1.2⟩ q.2
    ⟨⟨hq.2.1.1.le, hq.2.1.2⟩, ⟨hq.2.2.1.le, hq.2.2.2⟩⟩

private lemma response_product_eq {E g₁ g₂ : ℝ → ℝ} {a b x : ℝ} (hx : 0 < x) :
    profileResponse E a g₁ x * profileResponse E b g₂ x / x =
      ∫ p, (g₁ p.1 * g₂ p.2) * crossKernel E a b x p
        ∂(unitMeasure.prod unitMeasure) := by
  have he : (fun p : ℝ × ℝ => (g₁ p.1 * g₂ p.2) * crossKernel E a b x p) =
      (fun p : ℝ × ℝ => x ^ (-a - b) *
        ((g₁ p.1 * increment E (p.1 * x ^ a) x * priceRatio x (p.1 * x ^ a)) *
         (g₂ p.2 * increment E (p.2 * x ^ b) x * priceRatio x (p.2 * x ^ b)))) := by
    funext p; unfold crossKernel crossWeight movingIncrement; ring
  rw [he, integral_const_mul, integral_prod_mul
    (fun s => g₁ s * increment E (s * x ^ a) x * priceRatio x (s * x ^ a))
    (fun t => g₂ t * increment E (t * x ^ b) x * priceRatio x (t * x ^ b))]
  have hs := Real.sq_sqrt hx.le
  have hn₁ := WeightRemoval.normalized_eq (E := E) (g := g₁) (θ := a) hx
  have hn₂ := WeightRemoval.normalized_eq (E := E) (g := g₂) (θ := b) hx
  have hp : x ^ (-a - b) = (x ^ a * x ^ b)⁻¹ := by
    rw [← Real.rpow_add hx, ← Real.rpow_neg hx.le]; congr 1; ring
  rw [hp]
  calc
    _ = (profileResponse E a g₁ x / Real.sqrt x) * (profileResponse E b g₂ x / Real.sqrt x) := by
      rw [div_mul_div_comm, ← pow_two, hs]
    _ = _ := by rw [hn₁, hn₂]; ring

private lemma cross_integral_eq {E g₁ g₂ : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hg₁ : ProfileIntegrable g₁)
    (hg₂ : ProfileIntegrable g₂) {a b X : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hX : 4 ≤ X) :
    (∫ x in X..(2 * X), profileResponse E a g₁ x * profileResponse E b g₂ x / x) =
      ∫ p, (g₁ p.1 * g₂ p.2) *
        (∫ x in X..(2 * X), crossKernel E a b x p) ∂(unitMeasure.prod unitMeasure) := by
  have hXX : X ≤ 2 * X := by linarith
  have hi := crossKernel_integrable hE hg₁ hg₂ ha hb hX
  simp_rw [intervalIntegral.integral_of_le hXX]
  calc
    _ = ∫ x in Ioc X (2 * X), ∫ p, (g₁ p.1 * g₂ p.2) * crossKernel E a b x p
        ∂(unitMeasure.prod unitMeasure) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      exact response_product_eq (by linarith [hx.1] : 0 < x)
    _ = _ := by
      rw [integral_integral_swap hi]
      simp_rw [integral_const_mul]

private lemma profile_cross_integral_le {E g₁ g₂ : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hg₁ : ProfileIntegrable g₁)
    (hg₂ : ProfileIntegrable g₂) {a b X K : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    (hX : 4 ≤ X) (hK : 0 ≤ K)
    (hF : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc X (2 * X),
      |∫ x in X..y, movingIncrement E a s x * movingIncrement E b t x| ≤ K) :
    |∫ x in X..(2 * X), profileResponse E a g₁ x * profileResponse E b g₂ x / x| ≤
      (profileL1 g₁ * profileL1 g₂) * (K * ((27 + a + b) * X ^ (-a - b))) := by
  rw [cross_integral_eq hE hg₁ hg₂ ha hb hX]
  have hbound : ∀ᵐ p ∂(unitMeasure.prod unitMeasure),
      ‖(g₁ p.1 * g₂ p.2) * (∫ x in X..(2 * X), crossKernel E a b x p)‖ ≤
        (|g₁ p.1| * |g₂ p.2|) * (K * ((27 + a + b) * X ^ (-a - b))) := by
    have hrect : ∀ᵐ p ∂(unitMeasure.prod unitMeasure),
        p ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
      rw [unitMeasure, Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
    filter_upwards [hrect] with p hp
    have hs : p.1 ∈ Icc (0 : ℝ) 1 := ⟨hp.1.1.le, hp.1.2⟩
    have ht : p.2 ∈ Icc (0 : ℝ) 1 := ⟨hp.2.1.le, hp.2.2⟩
    have hf : IntervalIntegrable
        (fun x => movingIncrement E a p.1 x * movingIncrement E b p.2 x)
        volume X (2 * X) :=
      (VarianceTransfer.increment_product_comp_integrableOn hE isCompact_uIcc
        (continuous_const.mul (continuous_id.rpow_const (fun _ => Or.inr ha.le)))
        continuous_id
        (continuous_const.mul (continuous_id.rpow_const (fun _ => Or.inr hb.le)))
        continuous_id).intervalIntegrable
    have h := WeightedPrimitiveBound.weighted_integral_le_of_primitive_bound
      (by linarith : X ≤ 2 * X) hf
      (crossWeight_contDiffOn (a := a) (b := b) hX hs.1 ht.1) hK (hF p.1 hs p.2 ht)
    have he : (fun x => crossWeight a b p.1 p.2 x *
        (movingIncrement E a p.1 x * movingIncrement E b p.2 x)) =
        (fun x => crossKernel E a b x p) := by
      funext x; unfold crossKernel; ring
    rw [he] at h
    have hw := crossWeight_variation ha ha1 hb hb1 hX hs ht
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (h.trans (mul_le_mul_of_nonneg_left hw hK)) (by positivity)
  have hn := norm_integral_le_of_norm_le
    ((hg₁.2.abs.mul_prod hg₂.2.abs).mul_const (K * ((27 + a + b) * X ^ (-a - b)))) hbound
  simpa only [Real.norm_eq_abs, integral_mul_const,
    integral_prod_mul (fun s => |g₁ s|) (fun t => |g₂ t|), profileL1] using hn

/-- A uniform moving-increment primitive bound controls every pair of integrable profiles. -/
theorem profile_cross_integral_of_covariance_bound
    {E B : ℝ → ℝ} {a b : ℝ}
    (hE : LocallyBoundedMeasurable E)
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    (hB : ∀ X, 0 ≤ B X)
    (hCov : ∃ C₀ : ℝ, ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc X (2 * X),
        |∫ x in X..y, movingIncrement E a s x * movingIncrement E b t x| ≤ C₀ * B X) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ g₁ g₂ : ℝ → ℝ, ProfileIntegrable g₁ → ProfileIntegrable g₂ →
        |∫ x in X..(2 * X), profileResponse E a g₁ x * profileResponse E b g₂ x / x| ≤
          C * profileL1 g₁ * profileL1 g₂ * X ^ (-a - b) * B X := by
  obtain ⟨C₀, hCov⟩ := hCov
  refine ⟨(|C₀| + 1) * (27 + a + b), by positivity, ?_⟩
  filter_upwards [hCov, eventually_ge_atTop (4 : ℝ)] with X hF hX
  intro g₁ g₂ hg₁ hg₂
  have hK : 0 ≤ (|C₀| + 1) * B X := mul_nonneg (by positivity) (hB X)
  have hF' : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc X (2 * X),
      |∫ x in X..y, movingIncrement E a s x * movingIncrement E b t x| ≤
        (|C₀| + 1) * B X := by
    intro s hs t ht y hy
    exact (hF s hs t ht y hy).trans
      (mul_le_mul_of_nonneg_right (by linarith [le_abs_self C₀]) (hB X))
  convert profile_cross_integral_le hE hg₁ hg₂ ha ha1 hb hb1 hX hK hF' using 1; ring

end
end D5.S3.Arith.Robin.ForwardKernel.ProfileCrossIntegral
