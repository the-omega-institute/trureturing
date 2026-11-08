/- GID: D5/S3/Arith/Robin/ForwardKernel/FirstOrderInterface
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/FirstOrderInterface
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Variance bands give uniform continuously weighted first-moment cancellation. -/

import D5.S3.Arith.Robin.ForwardKernel.FourthMomentMean
import D5.S3.Arith.Robin.ForwardKernel.MacroscopicWeightApproximation
import D5.S3.Arith.Robin.ForwardKernel.MacroscopicVarianceDefs
import D5.S3.Arith.Robin.ForwardKernel.MomentInterfaceBounds
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Uniform first moments on dyadic subintervals and with continuous macroscopic weights. -/

namespace D5.S3.Arith.Robin.ForwardKernel.FirstOrderInterface

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs VarianceTransfer MomentTransferDefs DyadicProbability
open MacroscopicVarianceDefs CrossExponentDefs

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- A decreasing nonnegative smooth weight transfers interval primitive bounds with
at most twice its value at the left endpoint. -/
private lemma weighted_interval_le {f W : ℝ → ℝ} {X A B K : ℝ}
    (hX : 1 < X) (hA : X ≤ A) (hAB : A ≤ B)
    (hf : IntervalIntegrable f volume A B)
    (hW : ContDiffOn ℝ 1 W (Ioi 1))
    (hmono : AntitoneOn W (Ioi 1)) (hpos : ∀ x ∈ Ioi (1 : ℝ), 0 ≤ W x)
    (hK : 0 ≤ K) (hF : ∀ y ∈ Icc A B, |∫ x in A..y, f x| ≤ K) :
    |∫ x in A..B, W x * f x| ≤ 2 * K * W X := by
  have hsub : uIcc A B ⊆ Ioi (1 : ℝ) := by
    rw [uIcc_of_le hAB]
    intro x hx
    exact hX.trans_le (hA.trans hx.1)
  have hc := hW.mono hsub
  have hd : ∀ x ∈ Icc A B, deriv W x ≤ 0 := by
    intro x hx
    have hxi : x ∈ Ioi (1 : ℝ) := hsub (by simpa [uIcc_of_le hAB] using hx)
    rw [← derivWithin_of_isOpen isOpen_Ioi hxi]
    exact hmono.derivWithin_nonpos
  have he : (∫ x in A..B, |deriv W x|) = W A - W B := by
    calc
      _ = ∫ x in A..B, -deriv W x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact abs_of_nonpos (hd x (by simpa [uIcc_of_le hAB] using hx))
      _ = -(W B - W A) := by
        rw [intervalIntegral.integral_neg,
          hc.absolutelyContinuousOnInterval.integral_deriv_eq_sub]
      _ = _ := by ring
  have hb := WeightedPrimitiveBound.weighted_integral_le_of_primitive_bound
    hAB hf hc hK hF
  rw [abs_of_nonneg (hpos B (hX.trans_le (hA.trans hAB))), he] at hb
  have hm := hmono (show X ∈ Ioi (1 : ℝ) from hX)
    (show A ∈ Ioi (1 : ℝ) from hX.trans_le hA) hA
  nlinarith [hpos X hX]

/-- Positive powers of the position and its logarithm give a smooth decreasing reciprocal weight. -/
lemma logarithmic_weight_regular {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ContDiffOn ℝ 1 (fun x : ℝ => 1 / (x ^ p * (Real.log x) ^ q)) (Ioi 1) ∧
    AntitoneOn (fun x : ℝ => 1 / (x ^ p * (Real.log x) ^ q)) (Ioi 1) ∧
    (∀ x ∈ Ioi (1 : ℝ), 0 ≤ 1 / (x ^ p * (Real.log x) ^ q)) := by
  have hx0 : ∀ x ∈ Ioi (1 : ℝ), 0 < x := fun x hx => zero_lt_one.trans hx
  have hl : ∀ x ∈ Ioi (1 : ℝ), 0 < Real.log x := fun x hx => Real.log_pos hx
  refine ⟨?_, ?_, fun x hx => one_div_nonneg.mpr
    (mul_nonneg (Real.rpow_nonneg (hx0 x hx).le _)
      (Real.rpow_nonneg (hl x hx).le _))⟩
  · exact contDiffOn_const.div
      ((contDiffOn_id.rpow_const_of_ne (fun x hx' => (hx0 x hx').ne')).mul
        ((contDiffOn_id.log (fun x hx' => (hx0 x hx').ne')).rpow_const_of_ne
          (fun x hx' => (hl x hx').ne')))
      (fun x hx' => mul_ne_zero (Real.rpow_pos_of_pos (hx0 x hx') p).ne'
        (Real.rpow_pos_of_pos (hl x hx') q).ne')
  · intro x hx' y hy' hxy
    apply one_div_le_one_div_of_le (mul_pos
      (Real.rpow_pos_of_pos (hx0 x hx') p) (Real.rpow_pos_of_pos (hl x hx') q))
    exact mul_le_mul (Real.rpow_le_rpow (hx0 x hx').le hxy hp)
      (Real.rpow_le_rpow (hl x hx').le (Real.log_le_log (hx0 x hx') hxy) hq)
      (Real.rpow_nonneg (hl x hx').le _) (Real.rpow_nonneg (hx0 y hy').le _)

/-- Every primitive is negligible compared with the first-moment scale, uniformly
in the moving-length parameter and in both endpoints. -/
theorem first_interval_cancellation {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ A ∈ Icc X (2 * X), ∀ B ∈ Icc A (2 * X),
        |∫ x in A..B, movingIncrement E θ s x| <
          ε * (X * Real.sqrt (X ^ θ * Real.log X)) := by
  obtain ⟨ν, hθν, hνβ⟩ := exists_between hB.2.2.1
  obtain ⟨C, hC, hp⟩ := FourthMomentMean.moving_primitive_bound hE hB hV hθν hνβ
  have hν1 : ν < 1 := hνβ.trans hB.2.2.2
  have ht : Tendsto (fun X : ℝ => 2 * C *
      (X ^ (-(ν - θ) / 2) + X ^ (-(1 - ν) / 2))) atTop (𝓝 0) := by
    simpa only [neg_div, mul_zero, add_zero] using (tendsto_const_nhds (x := 2 * C)).mul
      ((tendsto_rpow_neg_atTop (half_pos (sub_pos.mpr hθν))).add
        (tendsto_rpow_neg_atTop (half_pos (sub_pos.mpr hν1))))
  intro ε hε
  filter_upwards [hp, ht.eventually (gt_mem_nhds hε), eventually_gt_atTop (1 : ℝ)]
    with X hp ht hX
  have hX0 : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hsqrt : Real.sqrt (X ^ θ * Real.log X) =
      X ^ (θ / 2) * Real.sqrt (Real.log X) := by
    rw [Real.sqrt_mul (Real.rpow_nonneg hX0.le _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hX0.le]
    congr 2
    ring
  have he : 2 * (C * Real.sqrt (Real.log X) *
      (X ^ (1 + θ - ν / 2) + X ^ ((1 + θ + ν) / 2))) =
      (2 * C * (X ^ (-(ν - θ) / 2) + X ^ (-(1 - ν) / 2))) *
        (X * Real.sqrt (X ^ θ * Real.log X)) := by
    rw [hsqrt]
    have h₁ : X ^ (-(ν - θ) / 2) * X * X ^ (θ / 2) = X ^ (1 + θ - ν / 2) := by
      conv_lhs => arg 1; arg 2; rw [← Real.rpow_one X]
      rw [ ← Real.rpow_add hX0, ← Real.rpow_add hX0]
      congr 1
      ring
    have h₂ : X ^ (-(1 - ν) / 2) * X * X ^ (θ / 2) = X ^ ((1 + θ + ν) / 2) := by
      conv_lhs => arg 1; arg 2; rw [← Real.rpow_one X]
      rw [ ← Real.rpow_add hX0, ← Real.rpow_add hX0]
      congr 1
      ring
    calc
      _ = 2 * C * (X ^ (1 + θ - ν / 2) + X ^ ((1 + θ + ν) / 2)) *
          Real.sqrt (Real.log X) := by ring
      _ = _ := by rw [← h₁, ← h₂]; ring
  intro s hs A hA B hB'
  have hi (a b : ℝ) : IntervalIntegrable (movingIncrement E θ s) volume a b :=
    (increment_comp_integrableOn hE isCompact_uIcc
    (continuous_const.mul (Real.continuous_rpow_const (hB.1.trans hB.2.1).le))
    continuous_id).intervalIntegrable
  have hie : (∫ x in A..B, movingIncrement E θ s x) =
      (∫ x in X..B, movingIncrement E θ s x) -
      ∫ x in X..A, movingIncrement E θ s x := by
    exact (intervalIntegral.integral_interval_sub_left (hi X B) (hi X A)).symm
  rw [hie]
  apply lt_of_le_of_lt ((abs_sub _ _).trans (add_le_add
    (hp s hs B ⟨hA.1.trans hB'.1, hB'.2⟩) (hp s hs A hA)))
  rw [← two_mul, he]
  exact mul_lt_mul_of_pos_right ht (by positivity)

/-- The normalized moving increment divided by position has a decreasing logarithmic weight. -/
private lemma dyadicB_div_eq {E : ℝ → ℝ} {θ s x : ℝ} (hx : 1 < x) :
    dyadicB E θ s x / x =
      (1 / (x ^ (1 + θ / 2) * (Real.log x) ^ (1 / 2 : ℝ))) *
        movingIncrement E θ s x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have he : x * Real.sqrt (x ^ θ * Real.log x) =
      x ^ (1 + θ / 2) * (Real.log x) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_mul (Real.rpow_nonneg hx0.le _), Real.sqrt_eq_rpow,
      Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le, Real.rpow_add hx0,
      Real.rpow_one]
    simp only [div_eq_mul_inv]
    ring
  simp only [dyadicB, movingIncrement]
  rw [div_div, mul_comm (Real.sqrt _) x, he]
  ring

/-- Uniform interval cancellation survives decreasing reciprocal power-logarithmic weights. -/
lemma logarithmic_weight_cancellation {ι : Type} {f : ℝ → ι → ℝ → ℝ} {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hi : ∀ X > (1 : ℝ), ∀ i, ∀ A B : ℝ, IntervalIntegrable (f X i) volume A B)
    (hraw : ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop, ∀ i,
      ∀ A ∈ Icc X (2 * X), ∀ B ∈ Icc A (2 * X),
        |∫ x in A..B, f X i x| < ε * (X ^ p * (Real.log X) ^ q)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop, ∀ i,
      ∀ A ∈ Icc X (2 * X), ∀ B ∈ Icc A (2 * X),
        |∫ x in A..B, (1 / (x ^ p * (Real.log x) ^ q)) * f X i x| < ε := by
  obtain ⟨hc, hm, hn⟩ := logarithmic_weight_regular hp hq
  intro ε hε
  filter_upwards [hraw (ε / 4) (by positivity), eventually_gt_atTop (1 : ℝ)]
    with X hr hX
  intro i A hA B hB
  have hscale : 0 < X ^ p * (Real.log X) ^ q :=
    mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hX) _)
      (Real.rpow_pos_of_pos (Real.log_pos hX) _)
  have hb := weighted_interval_le hX hA.1 hB.1 (hi X hX i A B) hc hm hn
    (show 0 ≤ (ε / 4) * (X ^ p * (Real.log X) ^ q) by positivity)
    (fun y hy => (hr i A hA y ⟨hy.1, hy.2.trans hB.2⟩).le)
  apply hb.trans_lt
  have he : 2 * ((ε / 4) * (X ^ p * (Real.log X) ^ q)) *
      (1 / (X ^ p * (Real.log X) ^ q)) = ε / 2 := by
    calc
      _ = (ε / 2) * ((X ^ p * (Real.log X) ^ q) * (1 / (X ^ p * (Real.log X) ^ q))) := by ring
      _ = ε / 2 := by rw [mul_one_div_cancel hscale.ne', mul_one]
  rw [he]
  linarith

/-- First moments cancel uniformly on all subintervals of the dyadic interval. -/
theorem first_weighted_interval_cancellation {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ A ∈ Icc X (2 * X), ∀ B ∈ Icc A (2 * X),
        |∫ x in A..B, dyadicB E θ s x / x| < ε := by
  have hθ : 0 < θ := hB.1.trans hB.2.1
  have hh := logarithmic_weight_cancellation
    (f := fun _ (s : Icc (0 : ℝ) 1) => movingIncrement E θ s)
    (p := 1 + θ / 2) (q := 1 / 2) (by positivity) (by norm_num)
    (by
      intro X hX s A B
      exact (increment_comp_integrableOn hE isCompact_uIcc
        (continuous_const.mul (Real.continuous_rpow_const hθ.le))
        continuous_id).intervalIntegrable)
    (by
      intro ε hε
      filter_upwards [first_interval_cancellation hE hB hV ε hε,
        eventually_gt_atTop (1 : ℝ)] with X hx hX
      intro s A hA B hB'
      have he : X * Real.sqrt (X ^ θ * Real.log X) =
          X ^ (1 + θ / 2) * (Real.log X) ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_mul (Real.rpow_nonneg (by linarith : 0 ≤ X) _),
          Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith : 0 ≤ X),
          Real.rpow_add (by linarith : 0 < X), Real.rpow_one]
        simp only [div_eq_mul_inv]
        ring
      simpa only [he] using hx s s.property A hA B hB')
  intro ε hε
  filter_upwards [hh ε hε, eventually_gt_atTop (1 : ℝ)] with X hh hX
  intro s hs A hA B hB'
  have he : (∫ x in A..B, dyadicB E θ s x / x) =
      ∫ x in A..B, (1 / (x ^ (1 + θ / 2) * (Real.log x) ^ (1 / 2 : ℝ))) *
        movingIncrement E θ s x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hB'.1] at hx
    exact dyadicB_div_eq (hX.trans_le (hA.1.trans hx.1))
  rw [he]
  exact hh ⟨s, hs⟩ A hA B hB'

/-- Powers of normalized moving increments are integrable for logarithmic dyadic sampling. -/
lemma dyadicB_power_integrable {E : ℝ → ℝ} {θ s X : ℝ}
    (hE : LocallyBoundedMeasurable E) (hθ : 0 ≤ θ) (hX : 1 < X) (n : ℕ) :
    IntervalIntegrable (fun x => dyadicB E θ s x ^ n / x) volume X (2 * X) ∧
      Integrable (fun x => dyadicB E θ s x ^ n) (dyadicProbabilityMeasure X) := by
  have hc : ContinuousOn (fun x : ℝ => 1 / (Real.sqrt (x ^ θ * Real.log x) ^ n * x))
      (uIcc X (2 * X)) := by
    apply continuousOn_const.div
      (((continuousOn_id.rpow_const (fun x hx => Or.inr hθ)).mul
        (continuousOn_id.log (by
          intro x hx
          rw [uIcc_of_le (by linarith : X ≤ 2 * X)] at hx
          simpa only [id_eq] using
            (ne_of_gt (zero_lt_one.trans (hX.trans_le hx.1)))))).sqrt.pow n |>.mul
              continuousOn_id)
    intro x hx
    rw [uIcc_of_le (by linarith : X ≤ 2 * X)] at hx
    have hx1 : 1 < x := hX.trans_le hx.1
    exact mul_ne_zero (pow_ne_zero _ (Real.sqrt_pos.mpr
      (mul_pos (Real.rpow_pos_of_pos (show 0 < id x from zero_lt_one.trans hx1) _)
        (Real.log_pos hx1))).ne')
      (show id x ≠ 0 from (zero_lt_one.trans hx1).ne')
  have hi := (FourthMomentMovingBounds.increment_pow_integrableOn
    (μ := volume) hE (K := uIcc X (2 * X))
    (u := fun x => s * x ^ θ) isCompact_uIcc
    (continuous_const.mul (Real.continuous_rpow_const hθ)) continuous_id n).intervalIntegrable
  have hh : IntervalIntegrable (fun x => dyadicB E θ s x ^ n / x) volume X (2 * X) := by
    convert hi.continuousOn_mul hc using 1
    ext x
    simp only [dyadicB, div_pow, id_eq]
    ring
  exact ⟨hh, dyadicProbabilityMeasure_integrable (by linarith) hh⟩

/-- Interval cancellation with bounded absolute logarithmic mass extends to continuous
dyadic weights. -/
lemma continuous_dyadic_weight_lifting {ι : Type} {g : ℝ → ι → ℝ → ℝ}
    (hi : ∀ᶠ X : ℝ in atTop, ∀ i,
      IntervalIntegrable (fun x => g X i x / x) volume X (2 * X))
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℝ in atTop, ∀ i,
      (∫ x in X..(2 * X), |g X i x / x|) ≤ C)
    (hc : ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop, ∀ i,
      ∀ A ∈ Icc X (2 * X), ∀ B ∈ Icc A (2 * X),
        |∫ x in A..B, g X i x / x| < ε)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc (1 : ℝ) 2)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop, ∀ i,
      |∫ x, φ (dyadicU X x) * g X i x ∂dyadicProbabilityMeasure X| < ε := by
  let f : ℝ → ι → ℝ → ℝ := fun X i u => X * (g X i (u * X) / (u * X))
  have he (X A B : ℝ) (i : ι) :
      (∫ u in A..B, f X i u) = ∫ x in (A * X)..(B * X), g X i x / x := by
    simp only [f, intervalIntegral.integral_const_mul]
    simpa only [smul_eq_mul] using intervalIntegral.smul_integral_comp_mul_right
      (fun x => g X i x / x) X
  obtain ⟨C, hC, hb⟩ := hb
  have hi' : ∀ᶠ X : ℝ in atTop, ∀ i, IntervalIntegrable (f X i) volume 1 2 := by
    filter_upwards [hi, eventually_gt_atTop (0 : ℝ)] with X hi hX i
    simpa only [div_self hX.ne', mul_div_cancel_right₀ _ hX.ne', f] using
      ((hi i).comp_mul_right (c := X)).const_mul X
  have hb' : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℝ in atTop, ∀ i,
      (∫ u in (1 : ℝ)..2, |f X i u|) ≤ C := by
    refine ⟨C, hC, ?_⟩
    filter_upwards [hb, eventually_gt_atTop (0 : ℝ)] with X hb hX i
    calc
      _ = ∫ u in (1 : ℝ)..2, X * |g X i (u * X) / (u * X)| := by
        simp only [f, abs_mul, abs_of_pos hX]
      _ = ∫ x in X..(2 * X), |g X i x / x| := by
        rw [intervalIntegral.integral_const_mul]
        simpa only [one_mul, smul_eq_mul] using intervalIntegral.smul_integral_comp_mul_right
          (fun x => |g X i x / x|) (a := 1) (b := 2) X
      _ ≤ C := hb i
  have hc' : ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop, ∀ i,
      ∀ A ∈ Icc (1 : ℝ) 2, ∀ B ∈ Icc A 2, |∫ u in A..B, f X i u| < ε := by
    intro ε hε
    filter_upwards [hc ε hε, eventually_gt_atTop (0 : ℝ)] with X hc hX i A hA B hB
    rw [he]
    exact hc i (A * X) ⟨by nlinarith [hA.1], by nlinarith [hA.2]⟩
      (B * X) ⟨by nlinarith [hB.1], by nlinarith [hB.2]⟩
  have hw := MacroscopicWeightApproximation.continuous_weight_lifting hi' hb' hc' hφ
  intro ε hε
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [hw (ε * Real.log 2) (by positivity), eventually_gt_atTop (0 : ℝ)]
    with X hw hX i
  rw [dyadicProbabilityMeasure_integral hX, abs_div, abs_of_pos hl]
  apply (div_lt_iff₀ hl).mpr
  have hew : (∫ u in (1 : ℝ)..2, φ u * f X i u) =
      ∫ x in X..(2 * X), φ (dyadicU X x) * g X i x / x := by
    calc
      _ = X * ∫ u in (1 : ℝ)..2,
          φ (dyadicU X (u * X)) * g X i (u * X) / (u * X) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro u _
        simp only [f, dyadicU, mul_div_cancel_right₀ _ hX.ne']
        ring
      _ = _ := by
        simpa only [one_mul, smul_eq_mul] using intervalIntegral.smul_integral_comp_mul_right
          (fun x => φ (dyadicU X x) * g X i x / x) (a := 1) (b := 2) X
  rw [← hew]
  exact hw i

/-- Continuous macroscopic weights have uniformly vanishing first normalized moments. -/
theorem first_moment_uniform {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc (1 : ℝ) 2)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, |weightedDyadicFirstMoment E φ θ X s| < ε := by
  have hθ : 0 ≤ θ := (hB.1.trans hB.2.1).le
  obtain ⟨C, hC, hb⟩ := MomentInterfaceBounds.second_moment_bound_interface hE hB hV
  have hh := continuous_dyadic_weight_lifting
    (g := fun _ (s : Icc (0 : ℝ) 1) x => dyadicB E θ s x)
    (by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX s
      simpa only [pow_one] using (dyadicB_power_integrable (s := s) hE hθ hX 1).1)
    (by
      refine ⟨(1 + C) * Real.log 2,
        mul_nonneg (by positivity) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le, ?_⟩
      filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with X hb hX s
      have hX0 : 0 < X := by linarith
      let := dyadicProbabilityMeasure_isProbabilityMeasure hX0
      have hi₂ := (dyadicB_power_integrable (s := s) hE hθ hX 2).2
      have hm : (∫ x, |dyadicB E θ s x| ∂dyadicProbabilityMeasure X) ≤ 1 + C := by
        have hh := integral_mono_of_nonneg (Eventually.of_forall (fun _ => abs_nonneg _))
          ((integrable_const (1 : ℝ)).add hi₂)
          (Eventually.of_forall (fun x => show |dyadicB E θ s x| ≤ 1 + dyadicB E θ s x ^ 2 by
            nlinarith [sq_nonneg (|dyadicB E θ s x| - 1), sq_abs (dyadicB E θ s x)]))
        simp only [Pi.add_apply] at hh
        have hh' : (∫ x, |dyadicB E θ s x| ∂dyadicProbabilityMeasure X) ≤
            1 + ∫ x, dyadicB E θ s x ^ 2 ∂dyadicProbabilityMeasure X := by
          simpa only [integral_add (integrable_const (1 : ℝ)) hi₂, integral_const,
            probReal_univ, one_smul] using hh
        apply hh'.trans
        apply add_le_add le_rfl
        simpa only [sq_abs] using hb s s.property
      rw [dyadicProbabilityMeasure_integral hX0] at hm
      have he : (∫ x in X..(2 * X), |dyadicB E θ s x / x|) =
          ∫ x in X..(2 * X), |dyadicB E θ s x| / x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by linarith : X ≤ 2 * X)] at hx
        change |dyadicB E θ s x / x| = |dyadicB E θ s x| / x
        rw [abs_div, abs_of_pos (hX0.trans_le hx.1)]
      rw [he]
      exact (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp hm)
    (by
      intro ε hε
      filter_upwards [first_weighted_interval_cancellation hE hB hV ε hε] with X hX s
      exact hX s s.property) hφ
  intro ε hε
  filter_upwards [hh ε hε] with X hh s hs
  exact hh ⟨s, hs⟩

/-- The variance band supplies the first absolute-moment bound and the zero first-moment kernel. -/
theorem first_moment_interface {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    MomentInterface E θ 1 (fun _ => 0) := by
  obtain ⟨C, hC, hb⟩ := MomentInterfaceBounds.second_moment_bound_interface hE hB hV
  refine ⟨⟨Real.sqrt C, Real.sqrt_nonneg C, ?_⟩, measurable_const, ?_⟩
  · filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with X hb hX s hs
    let := dyadicProbabilityMeasure_isProbabilityMeasure (zero_lt_one.trans hX)
    have hi := (dyadicB_power_integrable (s := s) hE (hB.1.trans hB.2.1).le hX 2).2
    have hmeas : Measurable (fun x => dyadicB E θ s x) :=
      (dyadicB_measurable hE θ).comp (measurable_const.prodMk measurable_id)
    have hm : MemLp (fun x => |dyadicB E θ s x|) 2 (dyadicProbabilityMeasure X) := by
      apply (memLp_two_iff_integrable_sq (by
        simpa only [Real.norm_eq_abs] using hmeas.norm.aestronglyMeasurable)).2
      simpa only [sq_abs] using hi
    have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (Eventually.of_forall (fun x => abs_nonneg (dyadicB E θ s x)))
      (Eventually.of_forall (fun _ : ℝ => zero_le_one))
      (by simpa using hm) (memLp_const (1 : ℝ))
    simp only [mul_one, Real.rpow_two, one_pow, integral_const, probReal_univ,
      one_smul, ← Real.sqrt_eq_rpow, Real.sqrt_one] at hcs
    simpa only [pow_one] using hcs.trans (Real.sqrt_le_sqrt (hb s hs))
  · intro s hs
    have hw := first_moment_uniform hE hB hV
      (φ := fun u : ℝ => u ^ dyadicR θ)
      (continuousOn_id.rpow_const (fun u hu => Or.inl (by
        change u ≠ 0
        linarith [hu.1])))
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hw ε hε] with X hX
    simpa only [Real.dist_eq, sub_zero, dyadicMixedMoment, weightedDyadicFirstMoment,
      Fin.prod_univ_one, Nat.cast_one, one_mul] using hX (s 0) (hs 0)

end
end D5.S3.Arith.Robin.ForwardKernel.FirstOrderInterface
