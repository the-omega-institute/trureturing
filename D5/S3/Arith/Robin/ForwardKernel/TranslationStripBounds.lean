/- GID: D5/S3/Arith/Robin/ForwardKernel/TranslationStripBounds
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/TranslationStripBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Comparable variance bounds control translations and short strips of moving increments. -/

import D5.S3.Arith.Robin.ForwardKernel.CrossExponentDefs
import D5.S3.Arith.Robin.ForwardKernel.MovingLengthVariance
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Uniform translation and short-strip estimates for moving increments. -/

namespace D5.S3.Arith.Robin.ForwardKernel.TranslationStripBounds

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs VarianceTransfer CrossExponentDefs

noncomputable section

/-- An interior power scale inherits the comparable-length variance upper bound. -/
theorem comparableLengthVarianceUpper_of_band
    {E : ℝ → ℝ} {α ρ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α ρ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ComparableLengthVarianceUpperFor E (fun X => X ^ ρ) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    exact Real.rpow_pos_of_pos hX _
  · intro A B d hA hAB hd
    exact MovingLengthVariance.comparable_length_variance_bound hE hB hV hA hAB hd

private lemma shift_continuous {b t : ℝ} (hb : 0 < b) :
    Continuous (movingShift b t) :=
  continuous_id.add (continuous_const.mul (Real.continuous_rpow_const hb.le))

private lemma shift_hasDerivAt {b t x : ℝ} (hx : 0 < x) :
    HasDerivAt (movingShift b t) (1 + t * (b * x ^ (b - 1))) x := by
  exact (hasDerivAt_id x).add
    ((Real.hasDerivAt_rpow_const (Or.inl hx.ne')).const_mul t)

private lemma shift_deriv_bounds {b t x : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (ht : t ∈ Icc (0 : ℝ) 1) (hx : 1 ≤ x) :
    1 ≤ 1 + t * (b * x ^ (b - 1)) ∧
      1 + t * (b * x ^ (b - 1)) ≤ 2 := by
  have hp0 : 0 ≤ x ^ (b - 1) := Real.rpow_nonneg (by linarith) _
  have hp1 : x ^ (b - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
  have htb : 0 ≤ t * b := mul_nonneg ht.1 hb.le
  have htb1 : t * b ≤ 1 := (mul_le_of_le_one_left hb.le ht.2).trans hb1.le
  constructor
  · have : 0 ≤ t * (b * x ^ (b - 1)) := mul_nonneg ht.1 (mul_nonneg hb.le hp0)
    linarith
  · nlinarith [mul_le_mul_of_nonneg_left hp1 htb]

private lemma shift_gap {b t x r : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hx : 1 ≤ x) (hr : 0 ≤ r) :
    movingShift b t (x + r) - movingShift b t x ∈ Icc (0 : ℝ) (2 * r) := by
  have hx0 : 0 < x := by linarith
  have hmono : x ^ b ≤ (x + r) ^ b :=
    Real.rpow_le_rpow hx0.le (by linarith) hb.le
  have hn := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := movingShift b t) (f' := fun y => 1 + t * (b * y ^ (b - 1)))
    (a := x) (b := x + r) (C := 2)
    (fun y hy => (shift_hasDerivAt (by linarith [hy.1])).hasDerivWithinAt)
    (by
      intro y hy
      have hd := shift_deriv_bounds hb hb1 ht (hx.trans hy.1)
      simpa only [Real.norm_eq_abs, abs_of_nonneg (by linarith [hd.1] :
        0 ≤ 1 + t * (b * y ^ (b - 1)))] using hd.2)
    (x + r) ⟨by linarith, le_rfl⟩
  refine ⟨?_, ?_⟩
  · dsimp [movingShift]
    nlinarith [mul_le_mul_of_nonneg_left hmono ht.1]
  · have := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, add_sub_cancel_left] using hn)
    exact this

private lemma scale_le_id {R : ℝ → ℝ} {b : ℝ}
    (hb : b < 1) (hR : Asymptotics.IsBigO atTop R (fun X : ℝ => X ^ b)) :
    ∀ᶠ X : ℝ in atTop, R X ≤ X := by
  obtain ⟨c, hc, hbound⟩ := hR.exists_pos
  have hp : Tendsto (fun X : ℝ => X ^ (b - 1)) atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (by linarith : 0 < 1 - b)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hbound.bound,
    hp.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / c))] with X hX hbd hp
  simp only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hX b)] at hbd
  have hpow : X ^ b = X ^ (b - 1) * X := by
    calc
      _ = X ^ ((b - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hX, Real.rpow_one]
  have hsmall : c * X ^ (b - 1) ≤ 1 := by
    have := (lt_div_iff₀ hc).mp hp
    nlinarith
  exact (le_abs_self _).trans (hbd.trans (by rw [hpow]; nlinarith))

private lemma difference_sq_integrableOn {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [T2Space α]
    {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    {K : Set α} (hK : IsCompact K) {u x v y : α → ℝ}
    (hu : Continuous u) (hx : Continuous x) (hv : Continuous v) (hy : Continuous y) :
    IntegrableOn (fun p => (increment E (u p) (x p) - increment E (v p) (y p)) ^ 2)
      K μ := by
  have h11 := increment_product_comp_integrableOn (μ := μ) hE hK hu hx hu hx
  have h22 := increment_product_comp_integrableOn (μ := μ) hE hK hv hy hv hy
  have h12 := increment_product_comp_integrableOn (μ := μ) hE hK hu hx hv hy
  convert (h11.add h22).sub (h12.const_mul 2) using 1
  ext p
  dsimp
  ring

lemma moving_sq_integrable {E : ℝ → ℝ} {b t : ℝ}
    (hE : LocallyBoundedMeasurable E) (hb : 0 < b) (l r : ℝ) :
    IntervalIntegrable (fun x => movingIncrement E b t x ^ 2) volume l r := by
  simpa only [movingIncrement, pow_two, Pi.mul_apply, id_eq] using
    (increment_product_comp_integrableOn hE isCompact_uIcc
      (continuous_const.mul (Real.continuous_rpow_const hb.le)) continuous_id
      (continuous_const.mul (Real.continuous_rpow_const hb.le)) continuous_id).intervalIntegrable

/-- Translations shorter than the comparison scale have uniformly bounded square integrals. -/
theorem moving_increment_translation_square_bound
    {E R : ℝ → ℝ} {b A B : ℝ}
    (hE : LocallyBoundedMeasurable E) (hb : 0 < b) (hb1 : b < 1)
    (hA : 0 < A) (hAB : A ≤ B)
    (hR : ComparableLengthVarianceUpperFor E R)
    (hRk : Asymptotics.IsBigO atTop R (fun X : ℝ => X ^ b)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) (R X),
      ∀ l ∈ Icc (A * X) (B * X), ∀ r ∈ Icc l (B * X),
        (∫ x in l..r,
          (movingIncrement E b t (x + v) - movingIncrement E b t x) ^ 2) ≤
            C * X * R X * Real.log X := by
  have hB : 0 < B := hA.trans_le hAB
  obtain ⟨K, hK, hKv⟩ := hR.2 1 4 (2 * B + 2)
    zero_lt_one (by norm_num) (by positivity)
  refine ⟨32 * K, by positivity, ?_⟩
  filter_upwards [hR.1, hKv, scale_le_id hb1 hRk,
    eventually_ge_atTop (max 1 (1 / A))] with X hRX hKv hRXle hX
  have hX1 : 1 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := by linarith
  have hAX : 1 ≤ A * X := by
    have := (div_le_iff₀ hA).mp ((le_max_right 1 (1 / A)).trans hX)
    nlinarith
  have hKX : 0 ≤ K * X * R X * Real.log X := by positivity [Real.log_nonneg hX1]
  have hV : ∀ w ∈ Icc (R X) (4 * R X),
      cumulativeVariance E ((2 * B + 2) * X) w ≤ K * X * R X * Real.log X := by
    simpa only [one_mul] using hKv
  intro t ht v hv l hl r hr
  have hlr : l ≤ r := hr.1
  have hx1 (x : ℝ) (hx : x ∈ Icc l r) : 1 ≤ x := hAX.trans (hl.1.trans hx.1)
  have hxB (x : ℝ) (hx : x ∈ Icc l r) : x ≤ B * X := hx.2.trans hr.2
  have hψ := shift_continuous (t := t) hb
  have hψv : Continuous (fun x => movingShift b t (x + v)) :=
    hψ.comp (continuous_id.add continuous_const)
  have hbound (y : ℝ) (hy : 1 ≤ y) :
      y ≤ movingShift b t y ∧ movingShift b t y ≤ 2 * y := by
    have hy0 : 0 < y := by linarith
    have hp := Real.rpow_le_self_of_one_le hy hb1.le
    have htp : 0 ≤ t * y ^ b := by positivity [ht.1]
    have htp' : t * y ^ b ≤ y :=
      (mul_le_of_le_one_left (Real.rpow_nonneg hy0.le _) ht.2).trans hp
    dsimp [movingShift]
    constructor <;> linarith
  have hfirst := MovingEndpointVariance.two_endpoint_increment_square_le
    (p := movingShift b t) (q := fun x => movingShift b t (x + v))
    (p' := fun x => 1 + t * (b * x ^ (b - 1)))
    (q' := fun x => 1 + t * (b * (x + v) ^ (b - 1)))
    (Y := (2 * B + 2) * X) (R := R X) (C₀ := 2) (m := 1)
    hE hlr hRX (by norm_num) zero_lt_one hKX hψ.continuousOn hψv.continuousOn
    (fun x hx => (shift_hasDerivAt (by linarith [hx1 x hx])).hasDerivWithinAt)
    (by
      intro x hx
      simpa only [Function.comp_def, mul_one, id_eq] using
        (((shift_hasDerivAt (b := b) (t := t)
          (by linarith [hx1 x hx, hv.1] : 0 < x + v)).comp x
            ((hasDerivAt_id x).add_const v)).hasDerivWithinAt (s := Icc l r)))
    (fun x hx => (shift_deriv_bounds hb hb1 ht (hx1 x hx)).1)
    (fun x hx => (shift_deriv_bounds hb hb1 ht (by linarith [hx1 x hx, hv.1])).1)
    (by
      intro x hx
      have hi := hbound x (hx1 x hx)
      have hj := hbound (x + v) (by linarith [hx1 x hx, hv.1])
      exact ⟨⟨by linarith [hx1 x hx], by nlinarith [hxB x hx]⟩,
        ⟨by linarith [hx1 x hx, hv.1], by nlinarith [hxB x hx, hv.2]⟩⟩)
    (by
      intro x hx
      have hg := shift_gap hb hb1 ht (hx1 x hx) hv.1
      exact ⟨hg.1, hg.2.trans (by linarith [hv.2])⟩)
    (by simpa only [show (2 + 2 : ℝ) = 4 by norm_num] using hV)
  have hsecond := MovingEndpointVariance.two_endpoint_increment_square_le
    (p := fun x : ℝ => x) (q := fun x => x + v)
    (p' := fun _ => 1) (q' := fun _ => 1)
    (Y := (2 * B + 2) * X) (R := R X) (C₀ := 2) (m := 1)
    hE hlr hRX (by norm_num) zero_lt_one hKX
    continuous_id.continuousOn (continuous_id.add continuous_const).continuousOn
    (fun x _ => (hasDerivAt_id x).hasDerivWithinAt)
    (fun x _ => ((hasDerivAt_id x).add_const v).hasDerivWithinAt)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (by
      intro x hx
      exact ⟨⟨hx1 x hx, by nlinarith [hxB x hx]⟩,
        ⟨by linarith [hx1 x hx, hv.1], by nlinarith [hxB x hx, hv.2]⟩⟩)
    (by
      intro x _
      simp only [add_sub_cancel_left]
      exact ⟨hv.1, by linarith [hv.2]⟩)
    (by simpa only [show (2 + 2 : ℝ) = 4 by norm_num] using hV)
  let f : ℝ → ℝ := fun x => E (movingShift b t (x + v)) - E (movingShift b t x)
  let g : ℝ → ℝ := fun x => E (x + v) - E x
  have hf : IntervalIntegrable (fun x => f x ^ 2) volume l r := by
    have := increment_product_comp_integrableOn (μ := volume) (K := uIcc l r)
      hE isCompact_uIcc
      (hψv.sub hψ) hψ (hψv.sub hψ) hψ
    simpa only [increment, add_sub_cancel, pow_two, f, Pi.sub_apply] using
      this.intervalIntegrable
  have hg : IntervalIntegrable (fun x => g x ^ 2) volume l r := by
    simpa only [increment, pow_two, g, id_eq] using
      (increment_product_comp_integrableOn hE isCompact_uIcc
        continuous_const continuous_id continuous_const continuous_id).intervalIntegrable
  have hd : IntervalIntegrable (fun x => (f x - g x) ^ 2) volume l r := by
    have := difference_sq_integrableOn (μ := volume) (K := uIcc l r) hE isCompact_uIcc
      (hψv.sub hψ) hψ (continuous_const (y := v)) continuous_id
    simpa only [increment, add_sub_cancel, f, g, Pi.sub_apply, id_eq] using
      this.intervalIntegrable
  have heq (x : ℝ) : movingIncrement E b t (x + v) - movingIncrement E b t x =
      f x - g x := by dsimp [movingIncrement, increment, movingShift, f, g]; ring
  simp_rw [heq]
  have hsum := intervalIntegral.integral_mono_on hlr hd
    ((hf.const_mul 2).add (hg.const_mul 2))
    (fun x _ => by nlinarith [sq_nonneg (f x + g x)])
  rw [intervalIntegral.integral_add (hf.const_mul 2) (hg.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hsum
  norm_num at hfirst hsecond
  change (∫ x in l..r, f x ^ 2) ≤ 8 * (K * X * R X * Real.log X) at hfirst
  change (∫ x in l..r, g x ^ 2) ≤ 8 * (K * X * R X * Real.log X) at hsecond
  nlinarith

/-- The translation square bound gives the corresponding interval square-root norm bound. -/
theorem moving_increment_translation_l2_bound
    {E R : ℝ → ℝ} {b A B : ℝ}
    (hE : LocallyBoundedMeasurable E) (hb : 0 < b) (hb1 : b < 1)
    (hA : 0 < A) (hAB : A ≤ B)
    (hR : ComparableLengthVarianceUpperFor E R)
    (hRk : Asymptotics.IsBigO atTop R (fun X : ℝ => X ^ b)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) (R X),
      ∀ l ∈ Icc (A * X) (B * X), ∀ r ∈ Icc l (B * X),
        intervalL2 l r
          (fun x => movingIncrement E b t (x + v) - movingIncrement E b t x) ≤
            C * Real.sqrt (X * Real.log X) * Real.sqrt (R X) := by
  obtain ⟨C, hC, hbound⟩ :=
    moving_increment_translation_square_bound hE hb hb1 hA hAB hR hRk
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, ?_⟩
  filter_upwards [hbound, hR.1, eventually_ge_atTop (1 : ℝ)] with X hbound hRX hX
  intro t ht v hv l hl r hr
  calc
    _ ≤ Real.sqrt (C * X * R X * Real.log X) :=
      Real.sqrt_le_sqrt (hbound t ht v hv l hl r hr)
    _ = _ := by
      rw [show C * X * R X * Real.log X = C * (X * Real.log X) * R X by ring,
        Real.sqrt_mul (mul_nonneg hC.le (mul_nonneg (by linarith) (Real.log_nonneg hX))),
        Real.sqrt_mul hC.le]

lemma moving_square_bound_of_comparable
    {E : ℝ → ℝ} {b A B : ℝ}
    (hE : LocallyBoundedMeasurable E) (hb : 0 < b) (hb1 : b < 1)
    (hA : 0 < A) (hAB : A ≤ B)
    (hk : ComparableLengthVarianceUpperFor E (fun X : ℝ => X ^ b)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ t ∈ Icc (0 : ℝ) 1,
        (∫ x in (A * X)..(B * X), movingIncrement E b t x ^ 2) ≤
          C * X * X ^ b * Real.log X := by
  have hB : 0 < B := hA.trans_le hAB
  obtain ⟨K, hK, hKv⟩ := hk.2 1 (B + 3) (2 * B + 2)
    zero_lt_one (by linarith) (by positivity)
  refine ⟨2 * (B + 3) * K, by positivity, ?_⟩
  filter_upwards [hKv, eventually_ge_atTop (max 1 (1 / A))] with X hKv hX
  have hX1 : 1 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := by linarith
  have hAX : 1 ≤ A * X := by
    have := (div_le_iff₀ hA).mp ((le_max_right 1 (1 / A)).trans hX)
    nlinarith
  intro t ht
  have hpow (x : ℝ) (hx : x ∈ Icc (A * X) (B * X)) :
      t * x ^ b ∈ Icc (0 : ℝ) ((B + 1) * X ^ b) := by
    have hx0 : 0 < x := by linarith [hx.1]
    refine ⟨mul_nonneg ht.1 (Real.rpow_nonneg hx0.le _), ?_⟩
    calc
      _ ≤ x ^ b := mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) ht.2
      _ ≤ ((B + 1) * X) ^ b := Real.rpow_le_rpow hx0.le (by nlinarith [hx.2]) hb.le
      _ = (B + 1) ^ b * X ^ b := Real.mul_rpow (by linarith) hX0.le
      _ ≤ (B + 1) * X ^ b := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by linarith) hb1.le) (Real.rpow_nonneg hX0.le _)
  have hbnd := MovingEndpointVariance.two_endpoint_increment_square_le
    (p := fun x : ℝ => x) (q := movingShift b t)
    (p' := fun _ => 1) (q' := fun x => 1 + t * (b * x ^ (b - 1)))
    (Y := (2 * B + 2) * X) (R := X ^ b) (C₀ := B + 1) (m := 1)
    (K := K * X * X ^ b * Real.log X)
    hE (mul_le_mul_of_nonneg_right hAB hX0.le) (Real.rpow_pos_of_pos hX0 _)
    (by linarith) zero_lt_one (by positivity [Real.log_nonneg hX1])
    continuous_id.continuousOn (shift_continuous hb).continuousOn
    (fun x _ => (hasDerivAt_id x).hasDerivWithinAt)
    (fun x hx => (shift_hasDerivAt (by linarith [hx.1])).hasDerivWithinAt)
    (fun _ _ => le_rfl)
    (fun x hx => (shift_deriv_bounds hb hb1 ht (hAX.trans hx.1)).1)
    (by
      intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hs : t * x ^ b ≤ x :=
        (mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) ht.2).trans
          (Real.rpow_le_self_of_one_le (hAX.trans hx.1) hb1.le)
      refine ⟨⟨hAX.trans hx.1, by nlinarith [hx.2]⟩, ?_⟩
      dsimp [movingShift]
      exact ⟨by linarith [(hpow x hx).1, hx.1], by nlinarith [hx.2]⟩)
    (by intro x hx; simpa only [movingShift, add_sub_cancel_left] using hpow x hx)
    (by
      intro u hu
      apply hKv u
      simpa only [one_mul, show B + 1 + 2 = B + 3 by ring] using hu)
  simpa only [movingIncrement, increment, movingShift, div_one, mul_assoc,
    show B + 1 + 2 = B + 3 by ring] using hbnd

/-- A short interval captures only its averaged share of the long-increment square mass,
up to the translation error at the averaging scale. -/
theorem moving_increment_short_strip_square_bound
    {E T : ℝ → ℝ} {b A B : ℝ}
    (hE : LocallyBoundedMeasurable E) (hb : 0 < b) (hb1 : b < 1)
    (hA : 0 < A) (hAB : A ≤ B)
    (hT : ComparableLengthVarianceUpperFor E T)
    (hk : ComparableLengthVarianceUpperFor E (fun X : ℝ => X ^ b))
    (hTk : Asymptotics.IsBigO atTop T (fun X : ℝ => X ^ b)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ M : ℝ, 0 ≤ M →
      ∀ l ∈ Icc (A * X) (B * X), ∀ r ∈ Icc l (B * X), r - l ≤ M →
        (∫ x in l..r, movingIncrement E b t x ^ 2) ≤
          C * (X * Real.log X) * (M * X ^ b / T X + T X) := by
  obtain ⟨K, hK, hKv⟩ :=
    moving_square_bound_of_comparable hE hb hb1 hA (by linarith : A ≤ B + 1) hk
  obtain ⟨L, hL, hLv⟩ :=
    moving_increment_translation_square_bound hE hb hb1 hA hAB hT hTk
  refine ⟨2 * K + 2 * L, by positivity, ?_⟩
  filter_upwards [hKv, hLv, hT.1, scale_le_id hb1 hTk,
    eventually_ge_atTop (1 : ℝ)] with X hKv hLv hTX hTXle hX
  have hX0 : 0 < X := by linarith
  have hQ : 0 ≤ X * Real.log X := mul_nonneg hX0.le (Real.log_nonneg hX)
  intro t ht M hM l hl r hr hlen
  have hlr : l ≤ r := hr.1
  have hz := moving_sq_integrable hE hb l r (t := t)
  have hpow : Continuous (fun y : ℝ => y ^ b) := Real.continuous_rpow_const hb.le
  have hu : Continuous (fun p : ℝ × ℝ => t * (p.1 + p.2) ^ b) :=
    continuous_const.mul (hpow.comp (continuous_fst.add continuous_snd))
  have hv : Continuous (fun p : ℝ × ℝ => t * p.1 ^ b) :=
    continuous_const.mul (hpow.comp continuous_fst)
  have hF : Integrable
      (fun p : ℝ × ℝ => movingIncrement E b t (p.1 + p.2) ^ 2)
      ((volume.restrict (Ioc l r)).prod (volume.restrict (Ioc (0 : ℝ) (T X)))) := by
    rw [Measure.prod_restrict]
    have hi := increment_product_comp_integrableOn (μ := volume.prod volume)
      (K := Icc l r ×ˢ Icc (0 : ℝ) (T X)) hE
      (isCompact_Icc.prod isCompact_Icc) hu (continuous_fst.add continuous_snd)
      hu (continuous_fst.add continuous_snd)
    simpa only [movingIncrement, pow_two, IntegrableOn, Pi.add_apply] using
      hi.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hD : Integrable
      (fun p : ℝ × ℝ =>
        (movingIncrement E b t (p.1 + p.2) - movingIncrement E b t p.1) ^ 2)
      ((volume.restrict (Ioc l r)).prod (volume.restrict (Ioc (0 : ℝ) (T X)))) := by
    rw [Measure.prod_restrict]
    have hi := difference_sq_integrableOn (μ := volume.prod volume)
      (K := Icc l r ×ˢ Icc (0 : ℝ) (T X)) hE
      (isCompact_Icc.prod isCompact_Icc) hu (continuous_fst.add continuous_snd)
      hv continuous_fst
    simpa only [movingIncrement, IntegrableOn, Pi.add_apply] using
      hi.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hFi : IntervalIntegrable
      (fun v => ∫ x in l..r, movingIncrement E b t (x + v) ^ 2) volume 0 (T X) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hTX.le]
    simpa only [IntegrableOn, intervalIntegral.integral_of_le hlr] using
      hF.integral_prod_right
  have hDi : IntervalIntegrable
      (fun v => ∫ x in l..r,
        (movingIncrement E b t (x + v) - movingIncrement E b t x) ^ 2)
      volume 0 (T X) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hTX.le]
    simpa only [IntegrableOn, intervalIntegral.integral_of_le hlr] using
      hD.integral_prod_right
  have hpoint (v : ℝ) : (∫ x in l..r, movingIncrement E b t x ^ 2) ≤
      2 * (∫ x in l..r, movingIncrement E b t (x + v) ^ 2) +
      2 * (∫ x in l..r,
        (movingIncrement E b t (x + v) - movingIncrement E b t x) ^ 2) := by
    have hzv : IntervalIntegrable (fun x => movingIncrement E b t (x + v) ^ 2)
        volume l r := by
      simpa using (moving_sq_integrable (t := t) hE hb (l + v) (r + v)).comp_add_right v
    have hdiff : IntervalIntegrable
        (fun x => (movingIncrement E b t (x + v) - movingIncrement E b t x) ^ 2)
        volume l r := by
      have hi := difference_sq_integrableOn (μ := volume) (K := uIcc l r)
        (u := fun x : ℝ => t * (x + v) ^ b) (v := fun x : ℝ => t * x ^ b)
        (x := fun x : ℝ => x + v) (y := fun x : ℝ => x)
        hE isCompact_uIcc
        (continuous_const.mul (hpow.comp (continuous_id.add continuous_const)))
        (continuous_id.add (continuous_const (y := v)))
        (continuous_const.mul hpow) continuous_id
      simpa only [movingIncrement, Pi.add_apply, Pi.mul_apply, id_eq, Function.comp_apply]
        using hi.intervalIntegrable
    have hh := intervalIntegral.integral_mono_on hlr hz
      ((hzv.const_mul 2).add (hdiff.const_mul 2)) (by
        intro x _
        nlinarith [sq_nonneg (2 * movingIncrement E b t (x + v) - movingIncrement E b t x)])
    simpa only [intervalIntegral.integral_add (hzv.const_mul 2) (hdiff.const_mul 2),
      intervalIntegral.integral_const_mul] using hh
  have havg := intervalIntegral.integral_mono_on hTX.le
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => ∫ x in l..r, movingIncrement E b t x ^ 2) volume 0 (T X))
    ((hFi.const_mul 2).add (hDi.const_mul 2)) (fun v _ => hpoint v)
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    intervalIntegral.integral_add (hFi.const_mul 2) (hDi.const_mul 2),
    intervalIntegral.integral_const_mul] at havg
  have hglobal := hKv t ht
  have hgi := moving_sq_integrable (t := t) hE hb (A * X) ((B + 1) * X)
  have hshift :
      (∫ v in (0 : ℝ)..T X, ∫ x in l..r, movingIncrement E b t (x + v) ^ 2) ≤
        M * (K * X * X ^ b * Real.log X) := by
    have hswap :
        (∫ v in (0 : ℝ)..T X, ∫ x in l..r, movingIncrement E b t (x + v) ^ 2) =
        ∫ x in l..r, ∫ v in (0 : ℝ)..T X, movingIncrement E b t (x + v) ^ 2 := by
      simp_rw [intervalIntegral.integral_of_le hlr, intervalIntegral.integral_of_le hTX.le]
      exact (integral_integral_swap hF).symm
    rw [hswap]
    have hinner : IntervalIntegrable
        (fun x => ∫ v in (0 : ℝ)..T X, movingIncrement E b t (x + v) ^ 2)
        volume l r := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlr]
      simpa only [IntegrableOn, intervalIntegral.integral_of_le hTX.le] using
        hF.integral_prod_left
    calc
      _ ≤ ∫ _x in l..r, K * X * X ^ b * Real.log X := by
        apply intervalIntegral.integral_mono_on hlr hinner intervalIntegrable_const
        intro x hx
        rw [intervalIntegral.integral_comp_add_left
          (fun y => movingIncrement E b t y ^ 2) x]
        simp only [add_zero]
        exact (intervalIntegral.integral_mono_interval
          (hl.1.trans hx.1) (by linarith : x ≤ x + T X)
          (by nlinarith [hx.2, hr.2])
          (Eventually.of_forall (fun _ => sq_nonneg _)) hgi).trans hglobal
      _ = (r - l) * (K * X * X ^ b * Real.log X) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hlen (by positivity [Real.log_nonneg hX])
  have hdiff :
      (∫ v in (0 : ℝ)..T X, ∫ x in l..r,
        (movingIncrement E b t (x + v) - movingIncrement E b t x) ^ 2) ≤
        T X * (L * X * T X * Real.log X) := by
    calc
      _ ≤ ∫ _v in (0 : ℝ)..T X, L * X * T X * Real.log X := by
        apply intervalIntegral.integral_mono_on hTX.le hDi intervalIntegrable_const
        intro v hv
        exact hLv t ht v hv l hl r hr
      _ = _ := by rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hmain : T X * (∫ x in l..r, movingIncrement E b t x ^ 2) ≤
      2 * (M * (K * X * X ^ b * Real.log X)) +
        2 * (T X * (L * X * T X * Real.log X)) := by linarith
  apply (le_of_mul_le_mul_left (a := T X) · hTX)
  calc
    _ ≤ 2 * (M * (K * X * X ^ b * Real.log X)) +
        2 * (T X * (L * X * T X * Real.log X)) := hmain
    _ ≤ T X * ((2 * K + 2 * L) * (X * Real.log X) *
        (M * X ^ b / T X + T X)) := by
      have hMk : 0 ≤ M * X ^ b := mul_nonneg hM (Real.rpow_nonneg hX0.le _)
      field_simp
      nlinarith [mul_nonneg (mul_nonneg hK.le hQ) (sq_nonneg (T X)),
        mul_nonneg (mul_nonneg hL.le hQ) hMk]

end
end D5.S3.Arith.Robin.ForwardKernel.TranslationStripBounds
