/- GID: D5/S3/Arith/Robin/ForwardKernel/FourthMomentMovingBounds
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/FourthMomentMovingBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourth moments control moving increments and price-weighted profiles. -/

import D5.S3.Arith.Robin.ForwardKernel.FourthMomentBandDefs
import D5.S3.Arith.Robin.ForwardKernel.WeightRemoval
import D5.S3.Arith.Robin.ForwardKernel.MovingDifferenceTransfer

/-! Fourth-moment transfer from fixed increments to moving integrable profiles. -/

namespace D5.S3.Arith.Robin.ForwardKernel.FourthMomentMovingBounds

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs VarianceTransfer ProfileKernelDefs FourthMomentBandDefs

noncomputable section

private lemma comparable_fourth_bound {α θ β : ℝ}
    (hB : ValidBand α θ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ {E : ℝ → ℝ} {C₄ : ℝ},
      FourthMomentBandBoundFor E α β C₄ → ∀ᶠ X : ℝ in atTop,
      ∀ u ∈ Icc (X ^ θ) (4 * X ^ θ),
        (∫ x in (1 : ℝ)..(3 * X), |increment E u x| ^ 4) ≤
          C * C₄ * X * (X ^ θ) ^ 2 * (Real.log X) ^ 2 := by
  have hθ1 : θ < 1 := hB.2.2.1.trans hB.2.2.2
  have hY : Tendsto (fun X : ℝ => 3 * X) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have hlo := FixedLengthCovariance.shifted_band hB.2.1 hB.2.2.1 hθ1
    (c := 1) (d := 3) (q := 1) (r := 0) zero_lt_one (by norm_num) zero_lt_one le_rfl
  have hhi := FixedLengthCovariance.shifted_band hB.2.1 hB.2.2.1 hθ1
    (c := 4) (d := 3) (q := 1) (r := 0) (by norm_num) (by norm_num) zero_lt_one le_rfl
  refine ⟨48 * (1 + |Real.log 3|) ^ 2, by positivity, ?_⟩
  intro E C₄ h₄
  filter_upwards [hY.eventually h₄.2, hlo, hhi,
    eventually_ge_atTop (Real.exp 1)] with X h₄X hlo hhi hX
  simp only [fixedLength, one_mul, zero_mul, add_zero] at hlo hhi
  have hX0 : 0 < X := (Real.exp_pos _).trans_le hX
  have hlogX : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hX1 : 1 < X := (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hX
  intro u hu
  have hband := And.intro (hlo.1.trans hu.1) (hu.2.trans hhi.2)
  have hu1 : 1 ≤ u := (Real.one_le_rpow (by linarith : 1 ≤ 3 * X) hB.1.le).trans hband.1
  have hu0 : 0 < u := zero_lt_one.trans_le hu1
  have huY : u < 3 * X := by
    calc
      u ≤ (3 * X) ^ β := hband.2
      _ < (3 * X) ^ (1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by linarith) hB.2.2.2
      _ = _ := Real.rpow_one _
  have hl0 : 0 ≤ Real.log (3 * X / u) :=
    (Real.log_pos ((one_lt_div hu0).mpr huY)).le
  have hl : Real.log (3 * X / u) ≤ (1 + |Real.log 3|) * Real.log X := by
    calc
      _ ≤ Real.log (3 * X) := Real.log_le_log (by positivity)
        (div_le_self (by positivity) hu1)
      _ = Real.log 3 + Real.log X := Real.log_mul (by norm_num) hX0.ne'
      _ ≤ _ := by nlinarith [le_abs_self (Real.log 3), abs_nonneg (Real.log 3)]
  calc
    _ ≤ C₄ * (3 * X) * u ^ 2 * (Real.log (3 * X / u)) ^ 2 := h₄X u hband.1 hband.2
    _ ≤ C₄ * (3 * X) * (4 * X ^ θ) ^ 2 *
        ((1 + |Real.log 3|) * Real.log X) ^ 2 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu0.le hu.2 2)
          (mul_nonneg h₄.1 (by positivity)))
        (pow_le_pow_left₀ hl0 hl 2) (sq_nonneg _) (by positivity [h₄.1])
    _ = _ := by ring

/-- A fixed-length fourth-moment bound controls every moving increment with parameter in `[0,1]`. -/
theorem moving_increment_fourth_moment_bound
    {α θ β : ℝ} (hB : ValidBand α θ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ {E : ℝ → ℝ} {C₄ : ℝ},
      LocallyBoundedMeasurable E → FourthMomentBandBoundFor E α β C₄ →
      ∀ᶠ X : ℝ in atTop, ∀ s ∈ Icc (0 : ℝ) 1,
      (∫ x in X..(2 * X), |increment E (s * x ^ θ) x| ^ 4) ≤
        C * C₄ * X * (X ^ θ) ^ 2 * (Real.log X) ^ 2 := by
  have hθ0 : 0 < θ := hB.1.trans hB.2.1
  have hθ1 : θ < 1 := hB.2.2.1.trans hB.2.2.2
  have hpow : Continuous (fun x : ℝ => x ^ θ) := Real.continuous_rpow_const hθ0.le
  obtain ⟨K, hK, hKv⟩ := comparable_fourth_bound hB
  have hband := FixedLengthCovariance.shifted_band hB.2.1 hB.2.2.1 hθ1
    (c := 1) (d := 1) (q := 2) (r := 0) zero_lt_one zero_lt_one (by norm_num) le_rfl
  refine ⟨32 * K, by positivity, ?_⟩
  intro E C₄ hE h₄
  filter_upwards [hKv h₄, hband, eventually_ge_atTop (1 : ℝ)] with X hKv hband hX
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hXX : X ≤ 2 * X := by linarith
  let h := X ^ θ
  let V := K * C₄ * X * h ^ 2 * (Real.log X) ^ 2
  have hh : 0 < h := Real.rpow_pos_of_pos hX0 θ
  have h2h : 2 * h ≤ X := by
    simp only [fixedLength, one_mul, zero_mul, add_zero] at hband
    exact hband.2.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX hB.2.2.2.le)
  have hV : ∀ w ∈ Icc h (4 * h),
      (∫ y in (1 : ℝ)..(3 * X), increment E w y ^ 4) ≤ V := by
    intro w hw
    simpa only [Even.pow_abs (by decide : Even (4 : ℕ))] using hKv w hw
  intro s hs
  let φ : ℝ → ℝ := fun x => x + s * x ^ θ
  have hφ : Continuous φ := continuous_id.add (continuous_const.mul hpow)
  have hL : ∀ x ∈ Icc X (2 * X), s * x ^ θ ∈ Icc (0 : ℝ) (2 * h) := by
    intro x hx
    have hx0 : 0 < x := hX0.trans_le hx.1
    refine ⟨mul_nonneg hs.1 (Real.rpow_pos_of_pos hx0 θ).le, ?_⟩
    calc
      s * x ^ θ ≤ x ^ θ := mul_le_of_le_one_left (Real.rpow_pos_of_pos hx0 θ).le hs.2
      _ ≤ (2 * X) ^ θ := Real.rpow_le_rpow hx0.le hx.2 hθ0.le
      _ = (2 : ℝ) ^ θ * h := Real.mul_rpow (by norm_num) hX0.le
      _ ≤ 2 * h := by
        gcongr
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hθ1.le
  have hφder : ∀ x ∈ Icc X (2 * X),
      HasDerivWithinAt φ (1 + s * (θ * x ^ (θ - 1))) (Icc X (2 * X)) x := by
    intro x hx
    exact ((hasDerivAt_id x).add
      ((Real.hasDerivAt_rpow_const
        (Or.inl (by linarith [hx.1] : x ≠ 0))).const_mul s)).hasDerivWithinAt
  have hav := MovingEndpointVariance.two_endpoint_integral_average_pow_le
    (by decide : Even 4) (by decide) hE hXX
    (a := 3 * h) (b := 4 * h) (c := h) (d := 4 * h)
    (m := 1) (A := 1) (B := 3 * X) (p := id) (q := φ) (F := fun _ => V)
    (by linarith) (by linarith) zero_lt_one continuous_id.continuousOn hφ.continuousOn
    (fun x _ => (hasDerivAt_id x).hasDerivWithinAt) hφder
    (fun _ _ => le_rfl)
    (by
      intro x hx
      have hx0 : 0 < x := hX0.trans_le hx.1
      have : 0 ≤ s * (θ * x ^ (θ - 1)) :=
        mul_nonneg hs.1 (mul_nonneg hθ0.le (Real.rpow_nonneg hx0.le _))
      linarith)
    (by
      intro x hx
      exact ⟨⟨hX.trans hx.1, by dsimp; linarith [hx.2]⟩,
        ⟨by dsimp [φ]; linarith [(hL x hx).1, hx.1],
         by dsimp [φ]; linarith [(hL x hx).2, hx.2]⟩⟩)
    (by
      intro x hx
      dsimp [φ]
      constructor <;> linarith [(hL x hx).1, (hL x hx).2])
    intervalIntegrable_const intervalIntegrable_const
    (fun w hw => hV w ⟨by linarith [hw.1], hw.2⟩) hV
  norm_num only [Nat.reduceSub, Nat.reducePow, div_one,
    intervalIntegral.integral_const, smul_eq_mul] at hav
  have hb : (∫ x in X..(2 * X), increment E (s * x ^ θ) x ^ 4) ≤ 32 * V := by
    apply le_of_mul_le_mul_left (a := h) _ hh
    calc
      _ = (4 * h - 3 * h) *
          (∫ x in X..(2 * X), (E (φ x) - E (id x)) ^ 4) := by
        simp only [φ, id_eq, increment]
        ring
      _ ≤ _ := hav
      _ = _ := by ring
  simpa only [Even.pow_abs (by decide : Even (4 : ℕ)), V, h, mul_assoc] using hb

private lemma profile_fourth_pointwise {E g : ℝ → ℝ} {θ x : ℝ}
    (hE : LocallyBoundedMeasurable E) (hg : ProfileIntegrable g) (hx : 3 ≤ x) :
    |∫ s, g s * increment E (s * x ^ θ) x * priceRatio x (s * x ^ θ)
        ∂unitMeasure| ^ 4 ≤
      profileL1 g ^ 3 * ∫ s, |g s| * increment E (s * x ^ θ) x ^ 4 ∂unitMeasure := by
  have hx0 : 0 < x := by linarith
  obtain ⟨M, hM, hMb⟩ := WeightRemoval.local_increment_bound hE θ hx0 le_rfl
  let k := fun s => increment E (s * x ^ θ) x * priceRatio x (s * x ^ θ)
  have hk : Measurable k := by
    exact ((WeightRemoval.increment_measurable hE θ).comp
      (measurable_const.prodMk measurable_id)).mul
      (WeightRemoval.price_measurable.comp
        (measurable_const.prodMk (measurable_id.mul_const _)))
  have hkinc : ∀ᵐ s ∂unitMeasure, |k s| ≤ |increment E (s * x ^ θ) x| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    obtain ⟨h0, h1⟩ := WeightControl.price_bounds hx
      (mul_nonneg hs.1.le (Real.rpow_nonneg hx0.le θ))
    dsimp [k]
    rw [abs_mul, abs_of_nonneg h0]
    exact mul_le_of_le_one_right (abs_nonneg _) h1
  have hinc : ∀ᵐ s ∂unitMeasure, |increment E (s * x ^ θ) x| ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hMb x ⟨le_rfl, le_rfl⟩ s ⟨hs.1.le, hs.2⟩
  have hb : ∀ᵐ s ∂unitMeasure, |k s| ≤ M := by
    filter_upwards [hkinc, hinc] with s hs ht
    exact hs.trans ht
  have hc1 := profile_cauchy_schwarz hg.2 hk.aestronglyMeasurable hM hb
  have hc2 := profile_cauchy_schwarz hg.2.abs (hk.pow_const 2).aestronglyMeasurable
    (sq_nonneg M) (by
      filter_upwards [hb] with s hs
      simpa only [abs_pow, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hs 2)
  simp only [profileL1, abs_abs, ← pow_mul, Nat.reduceMul] at hc2
  have hi : Integrable (fun s => |g s| * increment E (s * x ^ θ) x ^ 4)
      unitMeasure := by
    apply hg.2.abs.mul_bdd
      ((((WeightRemoval.increment_measurable hE θ).comp
        (measurable_const.prodMk measurable_id)).pow_const 4).aestronglyMeasurable)
    filter_upwards [hinc] with s hs
    simpa only [Real.norm_eq_abs, abs_pow, Function.comp_apply, id_eq] using
      pow_le_pow_left₀ (abs_nonneg _) hs 4
  have hki : Integrable (fun s => |g s| * k s ^ 4) unitMeasure := by
    apply hg.2.abs.mul_bdd (hk.pow_const 4).aestronglyMeasurable
    filter_upwards [hb] with s hs
    simpa only [Real.norm_eq_abs, abs_pow, Function.comp_apply, id_eq] using
      pow_le_pow_left₀ (abs_nonneg _) hs 4
  have hm : (∫ s, |g s| * k s ^ 4 ∂unitMeasure) ≤
      ∫ s, |g s| * increment E (s * x ^ θ) x ^ 4 ∂unitMeasure := by
    apply integral_mono_ae hki hi
    filter_upwards [hkinc] with s hs
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    simpa only [Even.pow_abs (by decide : Even (4 : ℕ))] using
      pow_le_pow_left₀ (abs_nonneg _) hs 4
  have hG : 0 ≤ profileL1 g := integral_nonneg (fun s => abs_nonneg _)
  calc
    _ = ((∫ s, g s * k s ∂unitMeasure) ^ 2) ^ 2 := by
      simp only [← pow_mul, Nat.reduceMul, Even.pow_abs (by decide : Even (4 : ℕ))]
      congr 2
      funext s
      dsimp [k]
      ring
    _ ≤ (profileL1 g * ∫ s, |g s| * k s ^ 2 ∂unitMeasure) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) hc1 2
    _ = profileL1 g ^ 2 * (∫ s, |g s| * k s ^ 2 ∂unitMeasure) ^ 2 := mul_pow _ _ _
    _ ≤ profileL1 g ^ 2 * (profileL1 g * ∫ s, |g s| * k s ^ 4 ∂unitMeasure) :=
      mul_le_mul_of_nonneg_left hc2 (sq_nonneg _)
    _ ≤ profileL1 g ^ 2 * (profileL1 g *
        ∫ s, |g s| * increment E (s * x ^ θ) x ^ 4 ∂unitMeasure) := by
      gcongr
    _ = _ := by ring

private lemma profile_fourth_integral_le {E g : ℝ → ℝ} {θ X V : ℝ}
    (hE : LocallyBoundedMeasurable E) (hg : ProfileIntegrable g)
    (hθ : 0 < θ) (hX : 3 ≤ X)
    (hV : ∀ s ∈ Icc (0 : ℝ) 1,
      (∫ x in X..(2 * X), increment E (s * x ^ θ) x ^ 4) ≤ V) :
    (∫ x in X..(2 * X), |profileResponse E θ g x| ^ 4 / x) ≤
      (2 * X / (X ^ θ) ^ 4) * profileL1 g ^ 4 * V := by
  have hX0 : 0 < X := by linarith
  have hXX : X ≤ 2 * X := by linarith
  let μ := volume.restrict (Ioc X (2 * X))
  let F := fun x => ∫ s, g s * increment E (s * x ^ θ) x * priceRatio x (s * x ^ θ)
    ∂unitMeasure
  let G := fun x => ∫ s, |g s| * increment E (s * x ^ θ) x ^ 4 ∂unitMeasure
  have hL : 0 ≤ profileL1 g := integral_nonneg (fun s => abs_nonneg _)
  obtain ⟨M, hM, hMb⟩ := WeightRemoval.local_increment_bound hE θ hX0 hXX
  have hi : Integrable (fun p : ℝ × ℝ =>
      |g p.2| * increment E (p.2 * p.1 ^ θ) p.1 ^ 4) (μ.prod unitMeasure) := by
    have hgprod : Integrable (fun p : ℝ × ℝ => |g p.2|) (μ.prod unitMeasure) := by
      simpa only [one_mul] using
        (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) μ).mul_prod hg.2.abs
    apply hgprod.mul_bdd
      ((WeightRemoval.increment_measurable hE θ).pow_const 4).aestronglyMeasurable
    have hrect : ∀ᵐ p ∂(μ.prod unitMeasure),
        p.1 ∈ Ioc X (2 * X) ∧ p.2 ∈ Ioc (0 : ℝ) 1 := by
      dsimp [μ, unitMeasure]
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
    filter_upwards [hrect] with p hp
    simpa only [Real.norm_eq_abs, abs_pow] using
      pow_le_pow_left₀ (abs_nonneg _)
        (hMb p.1 ⟨hp.1.1.le, hp.1.2⟩ p.2 ⟨hp.2.1.le, hp.2.2⟩) 4
  have hG : Integrable G μ := hi.integral_prod_left
  have hGbound : (∫ x, G x ∂μ) ≤ profileL1 g * V := by
    dsimp [G]
    rw [integral_integral_swap hi]
    simp_rw [integral_const_mul]
    change _ ≤ (∫ s, |g s| ∂unitMeasure) * V
    rw [← integral_mul_const]
    apply integral_mono_ae
    · simpa only [integral_const_mul] using hi.integral_prod_right
    · exact hg.2.abs.mul_const V
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact mul_le_mul_of_nonneg_left
        (by simpa only [intervalIntegral.integral_of_le hXX] using hV s ⟨hs.1.le, hs.2⟩)
        (abs_nonneg _)
  have hFm : Measurable F := by
    have hm : Measurable (fun p : ℝ × ℝ =>
        g p.2 * increment E (p.2 * p.1 ^ θ) p.1 * priceRatio p.1 (p.2 * p.1 ^ θ)) :=
      ((hg.1.comp measurable_snd).mul (WeightRemoval.increment_measurable hE θ)).mul
        (WeightRemoval.price_measurable.comp (measurable_fst.prodMk
          (measurable_snd.mul (measurable_fst.pow_const θ))))
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  have he (x : ℝ) (hx : X ≤ x) :
      |profileResponse E θ g x| ^ 4 / x = x / (x ^ θ) ^ 4 * F x ^ 4 := by
    have hx0 := hX0.trans_le hx
    have hs := Real.sq_sqrt hx0.le
    have hn := WeightRemoval.normalized_eq (E := E) (g := g) (θ := θ) hx0
    have hr : profileResponse E θ g x = Real.sqrt x / x ^ θ * F x := by
      calc
        _ = (profileResponse E θ g x / Real.sqrt x) * Real.sqrt x :=
          (div_mul_cancel₀ _ (Real.sqrt_pos.mpr hx0).ne').symm
        _ = _ := by rw [hn]; dsimp [F]; ring
    rw [hr, Even.pow_abs (by decide : Even (4 : ℕ)), mul_pow, div_pow]
    have hs4 : Real.sqrt x ^ 4 = x ^ 2 := by nlinarith [sq_nonneg (Real.sqrt x ^ 2 - x)]
    rw [hs4]
    field_simp
  have hpoint (x : ℝ) (hx : x ∈ Icc X (2 * X)) :
      x / (x ^ θ) ^ 4 * F x ^ 4 ≤
        (2 * X / (X ^ θ) ^ 4) * profileL1 g ^ 3 * G x := by
    have hx0 := hX0.trans_le hx.1
    have hxpow : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 θ
    have hXpow : 0 < X ^ θ := Real.rpow_pos_of_pos hX0 θ
    have hcoeff : x / (x ^ θ) ^ 4 ≤ 2 * X / (X ^ θ) ^ 4 := by
      calc
        _ ≤ 2 * X / (x ^ θ) ^ 4 := div_le_div_of_nonneg_right hx.2 (by positivity)
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity)
          (by positivity) (pow_le_pow_left₀ (Real.rpow_nonneg hX0.le _)
            (Real.rpow_le_rpow hX0.le hx.1 hθ.le) 4)
    calc
      _ ≤ (2 * X / (X ^ θ) ^ 4) * F x ^ 4 :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ ≤ (2 * X / (X ^ θ) ^ 4) * (profileL1 g ^ 3 * G x) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [Even.pow_abs (by decide : Even (4 : ℕ))] using
          profile_fourth_pointwise hE hg (hX.trans hx.1)
      _ = _ := by ring
  have hf : Integrable (fun x => x / (x ^ θ) ^ 4 * F x ^ 4) μ := by
    apply (hG.const_mul ((2 * X / (X ^ θ) ^ 4) * profileL1 g ^ 3)).mono'
      ((measurable_id.div ((measurable_id.pow_const θ).pow_const 4)).mul
        (hFm.pow_const 4)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 := hX0.trans_le hx.1.le
    have hraw0 : 0 ≤ x / (x ^ θ) ^ 4 * F x ^ 4 :=
      mul_nonneg (div_nonneg hx0.le (by positivity)) (by positivity)
    change ‖x / (x ^ θ) ^ 4 * F x ^ 4‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg hraw0]
    exact hpoint x ⟨hx.1.le, hx.2⟩
  calc
    _ = ∫ x, x / (x ^ θ) ^ 4 * F x ^ 4 ∂μ := by
      rw [intervalIntegral.integral_of_le hXX]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      exact he x hx.1.le
    _ ≤ ∫ x, (2 * X / (X ^ θ) ^ 4) * profileL1 g ^ 3 * G x ∂μ := by
      apply integral_mono_ae hf (hG.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact hpoint x ⟨hx.1.le, hx.2⟩
    _ = (2 * X / (X ^ θ) ^ 4) * profileL1 g ^ 3 * ∫ x, G x ∂μ :=
      integral_const_mul _ _
    _ ≤ (2 * X / (X ^ θ) ^ 4) * profileL1 g ^ 3 * (profileL1 g * V) :=
      mul_le_mul_of_nonneg_left hGbound (by positivity)
    _ = _ := by ring

/-- The price-weighted response to an integrable profile has a fourth moment at the dyadic scale. -/
theorem profile_response_fourth_moment_bound
    {α θ β : ℝ} (hB : ValidBand α θ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ {E : ℝ → ℝ} {C₄ : ℝ} {g : ℝ → ℝ},
      LocallyBoundedMeasurable E → FourthMomentBandBoundFor E α β C₄ →
      ProfileIntegrable g → ∀ᶠ X : ℝ in atTop,
      (∫ x in X..(2 * X), |profileResponse E θ g x| ^ 4 / x) ≤
        C * C₄ * profileL1 g ^ 4 * (meanSquareScale θ X) ^ 2 := by
  obtain ⟨C, hC, hinc⟩ := moving_increment_fourth_moment_bound hB
  refine ⟨2 * C, by positivity, ?_⟩
  intro E C₄ g hE h₄ hg
  filter_upwards [hinc hE h₄, eventually_ge_atTop (3 : ℝ)] with X hinc hX
  have hX0 : 0 < X := by linarith
  have hh := Real.rpow_pos_of_pos hX0 θ
  have hb := profile_fourth_integral_le hE hg (hB.1.trans hB.2.1) hX (by
    simpa only [Even.pow_abs (by decide : Even (4 : ℕ))] using hinc)
  apply hb.trans_eq
  have he : X ^ (1 - θ) = X / X ^ θ := by
    rw [Real.rpow_sub hX0, Real.rpow_one]
  dsimp [meanSquareScale]
  rw [he]
  field_simp

end
end D5.S3.Arith.Robin.ForwardKernel.FourthMomentMovingBounds
