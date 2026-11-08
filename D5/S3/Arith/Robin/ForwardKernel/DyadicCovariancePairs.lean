/- GID: D5/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/DyadicCovariancePairs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Moving differences pair uniformly across ordered smoothing scales and small residuals. -/

import D5.S3.Arith.Robin.ForwardKernel.SmoothMovingDifference
import D5.S3.Arith.Robin.ForwardKernel.DyadicDecomposition

namespace D5.S3.Arith.Robin.ForwardKernel.DyadicCovariancePairs

open Set MeasureTheory Filter
open scoped Topology BigOperators
open VarianceTransferDefs CrossExponentDefs MovingDifferenceTransfer SmoothMovingDifference

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma intervalL2_three {f : ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hf : IntervalIntegrable (fun x => f x ^ 2) volume a d) :
    intervalL2 a d f ≤ intervalL2 a b f + intervalL2 b c f + intervalL2 c d f := by
  have hi₁ := hf.mono_set (show uIcc a b ⊆ uIcc a d by
    rw [uIcc_of_le hab, uIcc_of_le (hab.trans (hbc.trans hcd))]
    exact Icc_subset_Icc_right (hbc.trans hcd))
  have hi₂ := hf.mono_set (show uIcc b c ⊆ uIcc a d by
    rw [uIcc_of_le hbc, uIcc_of_le (hab.trans (hbc.trans hcd))]
    exact Icc_subset_Icc hab hcd)
  have hi₃ := hf.mono_set (show uIcc c d ⊆ uIcc a d by
    rw [uIcc_of_le hcd, uIcc_of_le (hab.trans (hbc.trans hcd))]
    exact Icc_subset_Icc_left (hab.trans hbc))
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hi₁.trans hi₂) hi₃
  rw [← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂] at he
  have h₀ := Real.sq_sqrt (intervalIntegral.integral_nonneg_of_forall
    (μ := volume) (hab.trans (hbc.trans hcd)) (fun x => sq_nonneg (f x)))
  have h₁ := Real.sq_sqrt (intervalIntegral.integral_nonneg_of_forall
    (μ := volume) hab (fun x => sq_nonneg (f x)))
  have h₂ := Real.sq_sqrt (intervalIntegral.integral_nonneg_of_forall
    (μ := volume) hbc (fun x => sq_nonneg (f x)))
  have h₃ := Real.sq_sqrt (intervalIntegral.integral_nonneg_of_forall
    (μ := volume) hcd (fun x => sq_nonneg (f x)))
  unfold intervalL2
  nlinarith [Real.sqrt_nonneg (∫ x in a..d, f x ^ 2),
    Real.sqrt_nonneg (∫ x in a..b, f x ^ 2),
    Real.sqrt_nonneg (∫ x in b..c, f x ^ 2),
    Real.sqrt_nonneg (∫ x in c..d, f x ^ 2)]

/-- Three adjacent dyadic estimates control a moving difference on the working interval. -/
theorem smooth_moving_difference_outer_bounds {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ u : ℝ → ℝ, ContDiff ℝ 1 u →
        intervalL2 (X / 2) (4 * X) (fun x => u (movingShift θ s x) - u x) ≤
          C * X ^ θ * intervalL2 (X / 4) (8 * X) (deriv u) ∧
        intervalL2 (X / 2) (4 * X) (fun x => u (movingShift θ s x) - u x) ≤
          C * intervalL2 (X / 4) (8 * X) u ∧
        intervalL2 (X / 2) (4 * X) (deriv (fun x => u (movingShift θ s x) - u x)) ≤
          C * intervalL2 (X / 4) (8 * X) (deriv u) := by
  obtain ⟨C, hC, hb⟩ := smooth_moving_difference_bounds hθ hθ1
  have ht₁ : Tendsto (fun X : ℝ => X / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have ht₂ : Tendsto (fun X : ℝ => 2 * X) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  refine ⟨6 * C, by positivity, ?_⟩
  filter_upwards [ht₁.eventually hb, hb, ht₂.eventually hb,
    eventually_ge_atTop (4 : ℝ)] with X hb₁ hb₂ hb₃ hX
  intro s hs u hu
  have hX0 : 0 < X := by linarith
  let v := fun x => u (movingShift θ s x) - u x
  have hv : ContDiffOn ℝ 1 v (Ioi (0 : ℝ)) := by
    apply ContDiffOn.sub _ hu.contDiffOn
    apply hu.contDiffOn.comp
      (contDiffOn_id.add (contDiffOn_const.mul
        (contDiffOn_id.rpow_const_of_ne (fun x hx => ne_of_gt hx))))
    intro x hx
    exact mem_univ _
  have hv₀ : ContinuousOn v (Icc (X / 2) (4 * X)) :=
    hv.continuousOn.mono (fun x hx => by change 0 < x; linarith [hx.1])
  have hv₁ : ContinuousOn (deriv v) (Icc (X / 2) (4 * X)) :=
    (hv.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono
      (fun x hx => by change 0 < x; linarith [hx.1])
  have hijoin (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (X / 2) (4 * X))) :=
    intervalL2_three (f := f) (show X / 2 ≤ X by linarith)
      (show X ≤ 2 * X by linarith) (show 2 * X ≤ 4 * X by linarith)
      ((hf.pow 2).intervalIntegrable_of_Icc (by linarith))
  have hdu : Continuous (deriv u) := (contDiff_one_iff_deriv.mp hu).2
  have hm (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ)
      (ha : X / 4 ≤ a) (hab : a ≤ b) (hb : b ≤ 8 * X) :
      intervalL2 a b f ≤ intervalL2 (X / 4) (8 * X) f :=
    Real.sqrt_le_sqrt (intervalIntegral.integral_mono_interval ha hab hb
      (Eventually.of_forall fun _ => sq_nonneg _) ((hf.pow 2).intervalIntegrable _ _))
  have h₁ := hb₁ s hs u hu.contDiffOn
  have h₂ := hb₂ s hs u hu.contDiffOn
  have h₃ := hb₃ s hs u hu.contDiffOn
  have he₁ : 2 * (X / 2) = X := by ring
  have he₂ : X / 2 / 2 = X / 4 := by ring
  have he₃ : 4 * (X / 2) = 2 * X := by ring
  have he₄ : 2 * (2 * X) = 4 * X := by ring
  have he₅ : 2 * X / 2 = X := by ring
  have he₆ : 4 * (2 * X) = 8 * X := by ring
  rw [he₁, he₂, he₃] at h₁
  rw [he₄, he₅, he₆] at h₃
  have hm₁ := hm u hu.continuous (X / 4) (2 * X) le_rfl (by linarith) (by linarith)
  have hm₂ := hm u hu.continuous (X / 2) (4 * X) (by linarith) (by linarith) (by linarith)
  have hm₃ := hm u hu.continuous X (8 * X) (by linarith) (by linarith) le_rfl
  have hd₁ := hm (deriv u) hdu (X / 4) (2 * X) le_rfl (by linarith) (by linarith)
  have hd₂ := hm (deriv u) hdu (X / 2) (4 * X) (by linarith) (by linarith) (by linarith)
  have hd₃ := hm (deriv u) hdu X (8 * X) (by linarith) (by linarith) le_rfl
  have hp₁ : (X / 2) ^ θ ≤ X ^ θ := Real.rpow_le_rpow (by positivity) (by linarith) hθ.le
  have hp₃ : (2 * X) ^ θ ≤ 2 * X ^ θ := by
    rw [Real.mul_rpow (by norm_num) hX0.le]
    exact mul_le_mul_of_nonneg_right
      (by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hθ1.le)
      (Real.rpow_nonneg hX0.le θ)
  refine ⟨?_, ?_, ?_⟩
  · have h := hijoin v hv₀
    have h₁' := h₁.1.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hp₁ hC.le) hd₁ (Real.sqrt_nonneg _) (by positivity))
    have h₂' := h₂.1.trans (mul_le_mul_of_nonneg_left hd₂ (by positivity : 0 ≤ C * X ^ θ))
    have h₃' := h₃.1.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hp₃ hC.le) hd₃ (Real.sqrt_nonneg _) (by positivity))
    dsimp [v] at h
    have hn : 0 ≤ C * X ^ θ * intervalL2 (X / 4) (8 * X) (deriv u) := by
      exact mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hX0.le θ)) (Real.sqrt_nonneg _)
    nlinarith only [h, h₁', h₂', h₃', hn]
  · have h := hijoin v hv₀
    have h₁' := h₁.2.1.trans (mul_le_mul_of_nonneg_left hm₁ hC.le)
    have h₂' := h₂.2.1.trans (mul_le_mul_of_nonneg_left hm₂ hC.le)
    have h₃' := h₃.2.1.trans (mul_le_mul_of_nonneg_left hm₃ hC.le)
    dsimp [v] at h
    nlinarith [show 0 ≤ C * intervalL2 (X / 4) (8 * X) u from mul_nonneg hC.le (Real.sqrt_nonneg _)]
  · have h := hijoin (deriv v) hv₁
    have h₁' := h₁.2.2.trans (mul_le_mul_of_nonneg_left hd₁ hC.le)
    have h₂' := h₂.2.2.trans (mul_le_mul_of_nonneg_left hd₂ hC.le)
    have h₃' := h₃.2.2.trans (mul_le_mul_of_nonneg_left hd₃ hC.le)
    dsimp [v] at h
    nlinarith [show 0 ≤ C * intervalL2 (X / 4) (8 * X) (deriv u) from mul_nonneg hC.le (Real.sqrt_nonneg _)]

/-- Ordered block scales give a bound independent of their separation. -/
theorem dyadic_transfer_pair_bound {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ l ∈ Icc X (2 * X), ∀ r ∈ Icc l (2 * X),
      ∀ u v : ℝ → ℝ, ∀ A R S : ℝ,
        0 ≤ A → 0 < R → R ≤ S → S ≤ X →
        Measurable u → MemLp u 2 (volume.restrict (Ioc (X / 2) (4 * X))) →
        ContDiffOn ℝ 1 v (Icc (X / 2) (4 * X)) →
        intervalL2 (X / 2) (4 * X) u ≤ A * Real.sqrt R →
        intervalL2 (X / 2) (4 * X) v ≤ A * Real.sqrt S →
        intervalL2 (X / 2) (4 * X) (deriv v) ≤ A / Real.sqrt S →
        (∀ y ∈ Icc (X / 2) (4 * X), |u y| ≤ A) →
        (∀ y ∈ Icc (X / 2) (4 * X), |v y| ≤ A) →
        |∫ x in l..r, (u (movingShift a s x) - u x) * v x| ≤ C * A ^ 2 * X ^ a := by
  obtain ⟨C, hC, hT⟩ := moving_difference_transfer_bound ha ha1
  refine ⟨6 * C, by positivity, ?_⟩
  filter_upwards [hT, eventually_ge_atTop (1 : ℝ)] with X hT hX
  intro s hs l hl r hr u v A R S hA hR hRS hSX hum hu hv hUn hVn hDn hUs hVs
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hS : 0 < S := hR.trans_le hRS
  have hsS : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
  have hroot : Real.sqrt R ≤ Real.sqrt S := Real.sqrt_le_sqrt hRS
  have hprod : Real.sqrt R * Real.sqrt S ≤ X := by
    rw [← Real.sqrt_mul hR.le]
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hX0.le, (mul_le_mul (hRS.trans hSX) hSX hS.le hX0.le).trans_eq (by ring)⟩
  have hUV : intervalL2 (X / 2) (4 * X) u * intervalL2 (X / 2) (4 * X) v ≤ A ^ 2 * X := by
    calc
      _ ≤ (A * Real.sqrt R) * (A * Real.sqrt S) :=
        mul_le_mul hUn hVn (Real.sqrt_nonneg _) (by positivity)
      _ = A ^ 2 * (Real.sqrt R * Real.sqrt S) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (sq_nonneg A)
  have hUD : intervalL2 (X / 2) (4 * X) u *
      intervalL2 (X / 2) (4 * X) (deriv v) ≤ A ^ 2 := by
    calc
      _ ≤ (A * Real.sqrt R) * (A / Real.sqrt S) :=
        mul_le_mul hUn hDn (Real.sqrt_nonneg _) (by positivity)
      _ = A ^ 2 * (Real.sqrt R / Real.sqrt S) := by ring
      _ ≤ A ^ 2 * 1 := mul_le_mul_of_nonneg_left ((div_le_one hsS).mpr hroot) (sq_nonneg A)
      _ = _ := mul_one _
  have hstrip := (endpoint_strips_integral_bounds ha ha1 hs hX hl hr hu).2 A hA hUs
  have ht := hT s hs l hl r hr u v A hum hu hv hA hVs
  apply ht.trans
  have h₁ := mul_le_mul_of_nonneg_left hUD (Real.rpow_nonneg hX0.le a)
  have h₂ := mul_le_mul_of_nonneg_left hUV (div_nonneg (Real.rpow_nonneg hX0.le a) hX0.le)
  have h₃ := mul_le_mul_of_nonneg_left hstrip hA
  rw [show X ^ a / X * (A ^ 2 * X) = X ^ a * A ^ 2 by field_simp] at h₂
  have hsum : X ^ a * intervalL2 (X / 2) (4 * X) u *
      intervalL2 (X / 2) (4 * X) (deriv v) +
      (X ^ a / X) * intervalL2 (X / 2) (4 * X) u * intervalL2 (X / 2) (4 * X) v +
      A * (∫ y in endpointStrips a s l r, |u y|) ≤ 6 * A ^ 2 * X ^ a := by
    nlinarith only [h₁, h₂, h₃]
  exact (mul_le_mul_of_nonneg_left hsum hC.le).trans_eq (by ring)

/-- A small residual pairs with a smooth long difference at a linear logarithmic cost. -/
theorem residual_transfer_pair_bound {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ l ∈ Icc X (2 * X), ∀ r ∈ Icc l (2 * X),
      ∀ u v : ℝ → ℝ, ∀ A k n : ℝ,
        0 ≤ A → 0 < k → Real.sqrt (X ^ a) * Real.sqrt k ≤ X → 1 ≤ n →
        Measurable u → MemLp u 2 (volume.restrict (Ioc (X / 2) (4 * X))) →
        ContDiffOn ℝ 1 v (Icc (X / 2) (4 * X)) →
        intervalL2 (X / 2) (4 * X) u ≤ A * Real.sqrt (X ^ a) →
        intervalL2 (X / 2) (4 * X) v ≤ A * Real.sqrt k →
        intervalL2 (X / 2) (4 * X) (deriv v) ≤ A / Real.sqrt (X ^ a) →
        (∀ y ∈ Icc (X / 2) (4 * X), |v y| ≤ A * n) →
        |∫ x in l..r, (u (movingShift a s x) - u x) * v x| ≤
          C * A ^ 2 * X ^ a * n := by
  obtain ⟨C, hC, hT⟩ := moving_difference_transfer_bound ha ha1
  refine ⟨4 * C, by positivity, ?_⟩
  filter_upwards [hT, eventually_ge_atTop (1 : ℝ)] with X hT hX
  intro s hs l hl r hr u v A k n hA hk hprod hn hum hu hv hUn hVn hDn hVs
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hh : 0 < X ^ a := Real.rpow_pos_of_pos hX0 a
  have hroot : 0 < Real.sqrt (X ^ a) := Real.sqrt_pos.mpr hh
  have hUV : intervalL2 (X / 2) (4 * X) u * intervalL2 (X / 2) (4 * X) v ≤ A ^ 2 * X := by
    calc
      _ ≤ (A * Real.sqrt (X ^ a)) * (A * Real.sqrt k) :=
        mul_le_mul hUn hVn (Real.sqrt_nonneg _) (by positivity)
      _ = A ^ 2 * (Real.sqrt (X ^ a) * Real.sqrt k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (sq_nonneg A)
  have hUD : intervalL2 (X / 2) (4 * X) u *
      intervalL2 (X / 2) (4 * X) (deriv v) ≤ A ^ 2 := by
    calc
      _ ≤ (A * Real.sqrt (X ^ a)) * (A / Real.sqrt (X ^ a)) :=
        mul_le_mul hUn hDn (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hstrip := (endpoint_strips_integral_bounds ha ha1 hs hX hl hr hu).1
  have hstrip' : (∫ y in endpointStrips a s l r, |u y|) ≤ 2 * A * X ^ a := by
    apply hstrip.trans
    calc
      _ ≤ 2 * Real.sqrt (X ^ a) * (A * Real.sqrt (X ^ a)) :=
        mul_le_mul_of_nonneg_left hUn (by positivity)
      _ = 2 * A * (Real.sqrt (X ^ a)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hh.le]
  have ht := hT s hs l hl r hr u v (A * n) hum hu hv (by positivity) hVs
  apply ht.trans
  have h₁ := mul_le_mul_of_nonneg_left hUD hh.le
  have h₂ := mul_le_mul_of_nonneg_left hUV (div_nonneg hh.le hX0.le)
  have h₃ := mul_le_mul_of_nonneg_left hstrip' (show 0 ≤ A * n by positivity)
  rw [show X ^ a / X * (A ^ 2 * X) = X ^ a * A ^ 2 by field_simp] at h₂
  have hn' := mul_le_mul_of_nonneg_left hn (mul_nonneg (sq_nonneg A) hh.le)
  have hsum : X ^ a * intervalL2 (X / 2) (4 * X) u *
      intervalL2 (X / 2) (4 * X) (deriv v) +
      (X ^ a / X) * intervalL2 (X / 2) (4 * X) u * intervalL2 (X / 2) (4 * X) v +
      (A * n) * (∫ y in endpointStrips a s l r, |u y|) ≤ 4 * A ^ 2 * X ^ a * n := by
    nlinarith only [h₁, h₂, h₃, hn']
  exact (mul_le_mul_of_nonneg_left hsum hC.le).trans_eq (by ring)

/-- Two smooth blocks with their scale bounds have a uniform moving covariance bound. -/
theorem dyadic_block_covariance_bound {a b : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ l ∈ Icc X (2 * X), ∀ r ∈ Icc l (2 * X),
      ∀ u w : ℝ → ℝ, ∀ A R S : ℝ,
        0 ≤ A → 0 < R → 0 < S → R ≤ X → S ≤ X →
        ContDiff ℝ 1 u → ContDiff ℝ 1 w →
        intervalL2 (X / 2) (4 * X) u ≤ A * Real.sqrt R →
        intervalL2 (X / 2) (4 * X) (deriv u) ≤ A / Real.sqrt R →
        (∀ y ∈ Icc (X / 2) (4 * X), |u y| ≤ A) →
        intervalL2 (X / 4) (8 * X) w ≤ A * Real.sqrt S →
        intervalL2 (X / 4) (8 * X) (deriv w) ≤ A / Real.sqrt S →
        (∀ y ∈ Icc (X / 4) (8 * X), |w y| ≤ A) →
        |∫ x in l..r,
          (u (movingShift a s x) - u x) * (w (movingShift b t x) - w x)| ≤
          C * A ^ 2 * X ^ a := by
  obtain ⟨Ca, hCa, hsa⟩ := smooth_moving_difference_bounds ha ha1
  obtain ⟨Cb, hCb, hsb⟩ := smooth_moving_difference_outer_bounds hb hb1
  obtain ⟨Ct, hCt, htr⟩ := dyadic_transfer_pair_bound ha ha1
  let D := Cb + 2
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨Ca * Cb + Ct * D ^ 2, by positivity, ?_⟩
  filter_upwards [hsa, hsb, htr, eventually_ge_atTop (4 : ℝ)] with X hsa hsb htr hX
  intro s hs t ht l hl r hr u w A R S hA hR hS hRX hSX hu hw hUn hUd hUs hWn hWd hWs
  have hX0 : 0 < X := by linarith
  have hXX : X ≤ 2 * X := by linarith
  have hlr : l ≤ r := hr.1
  let f := fun x => u (movingShift a s x) - u x
  let v := fun x => w (movingShift b t x) - w x
  have hf : Continuous f := hu.continuous.comp
    (continuous_id.add (continuous_const.mul (Real.continuous_rpow_const ha.le))) |>.sub hu.continuous
  have hv : Continuous v := hw.continuous.comp
    (continuous_id.add (continuous_const.mul (Real.continuous_rpow_const hb.le))) |>.sub hw.continuous
  have hvd : ContDiffOn ℝ 1 v (Icc (X / 2) (4 * X)) := by
    apply ContDiffOn.sub _ hw.contDiffOn
    apply hw.contDiffOn.comp
      (contDiffOn_id.add (contDiffOn_const.mul
        (contDiffOn_id.rpow_const_of_ne (fun x hx => by
          have : 0 < x := by linarith [hx.1]
          exact this.ne'))))
    exact fun _ _ => mem_univ _
  have huLp : MemLp u 2 (volume.restrict (Ioc (X / 2) (4 * X))) :=
    (memLp_two_iff_integrable_sq hu.continuous.measurable.aestronglyMeasurable).mpr
      (((hu.continuous.pow 2).intervalIntegrable (X / 2) (4 * X)).1)
  have hvnorm := hsb t ht w hw
  have hVn : intervalL2 (X / 2) (4 * X) v ≤ Cb * A * Real.sqrt S :=
    hvnorm.2.1.trans ((mul_le_mul_of_nonneg_left hWn hCb.le).trans_eq (by ring))
  have hVd : intervalL2 (X / 2) (4 * X) (deriv v) ≤ Cb * A / Real.sqrt S :=
    hvnorm.2.2.trans ((mul_le_mul_of_nonneg_left hWd hCb.le).trans_eq (by ring))
  have hVs : ∀ y ∈ Icc (X / 2) (4 * X), |v y| ≤ 2 * A := by
    intro y hy
    have hy1 : 1 ≤ y := by linarith [hy.1]
    have hgap : 0 ≤ t * y ^ b := mul_nonneg ht.1 (Real.rpow_nonneg (by linarith) b)
    have hgap' : t * y ^ b ≤ y :=
      (mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) b) ht.2).trans
        (Real.rpow_le_self_of_one_le hy1 hb1.le)
    have hm : movingShift b t y ∈ Icc (X / 4) (8 * X) := by
      dsimp [movingShift]
      constructor <;> linarith [hy.1, hy.2]
    exact (abs_sub _ _).trans ((add_le_add (hWs _ hm)
      (hWs y ⟨by linarith [hy.1], by linarith [hy.2]⟩)).trans_eq (by ring))
  by_cases hRS : R ≤ S
  · have hDA : A ≤ D * A := by dsimp [D]; nlinarith
    have hCA : Cb * A ≤ D * A := by dsimp [D]; nlinarith
    have ht := htr s hs l hl r hr u v (D * A) R S (by positivity) hR hRS hSX
      hu.continuous.measurable huLp hvd
      (hUn.trans (mul_le_mul_of_nonneg_right hDA (Real.sqrt_nonneg _)))
      (hVn.trans (mul_le_mul_of_nonneg_right hCA (Real.sqrt_nonneg _)))
      (hVd.trans (div_le_div_of_nonneg_right hCA (Real.sqrt_nonneg _)))
      (fun y hy => (hUs y hy).trans hDA)
      (fun y hy => (hVs y hy).trans (by dsimp [D]; nlinarith))
    apply ht.trans
    have hnonneg : 0 ≤ Ca * Cb * A ^ 2 * X ^ a := by positivity
    dsimp [D] at *
    nlinarith only [hnonneg]
  · have hSR : S ≤ R := le_of_not_ge hRS
    have hsmall := (hsa s hs u hu.contDiffOn).1.trans
      (mul_le_mul_of_nonneg_left hUd (by positivity : 0 ≤ Ca * X ^ a))
    have hfi : MemLp f 2 (volume.restrict (Ioc l r)) :=
      (memLp_two_iff_integrable_sq hf.measurable.aestronglyMeasurable).mpr
        (((hf.pow 2).intervalIntegrable l r).1)
    have hvi : MemLp v 2 (volume.restrict (Ioc l r)) :=
      (memLp_two_iff_integrable_sq hv.measurable.aestronglyMeasurable).mpr
        (((hv.pow 2).intervalIntegrable l r).1)
    have hc := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
      (show MemLp f (ENNReal.ofReal 2) _ by simpa using hfi)
      (show MemLp v (ENNReal.ofReal 2) _ by simpa using hvi)
    have hn := (norm_integral_le_integral_norm (fun x => f x * v x)).trans
      (by simpa only [norm_mul] using hc)
    have hp : |∫ x in l..r, f x * v x| ≤ intervalL2 l r f * intervalL2 l r v := by
      simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow,
        intervalIntegral.integral_of_le hlr, intervalL2] using hn
    have hfn : intervalL2 l r f ≤ Ca * X ^ a * (A / Real.sqrt R) :=
      (Real.sqrt_le_sqrt (intervalIntegral.integral_mono_interval hl.1 hlr hr.2
        (Eventually.of_forall fun _ => sq_nonneg _) ((hf.pow 2).intervalIntegrable X (2 * X)))).trans hsmall
    have hvn : intervalL2 l r v ≤ Cb * A * Real.sqrt S :=
      (Real.sqrt_le_sqrt (intervalIntegral.integral_mono_interval
        (show X / 2 ≤ l by linarith [hl.1]) hlr (show r ≤ 4 * X by linarith [hr.2])
        (Eventually.of_forall fun _ => sq_nonneg _)
        ((hv.pow 2).intervalIntegrable (X / 2) (4 * X)))).trans hVn
    have hroots : Real.sqrt S / Real.sqrt R ≤ 1 :=
      (div_le_one (Real.sqrt_pos.mpr hR)).mpr (Real.sqrt_le_sqrt hSR)
    calc
      _ ≤ (Ca * X ^ a * (A / Real.sqrt R)) * (Cb * A * Real.sqrt S) :=
        hp.trans (mul_le_mul hfn hvn (Real.sqrt_nonneg _) (by positivity))
      _ = (Ca * Cb * A ^ 2 * X ^ a) * (Real.sqrt S / Real.sqrt R) := by ring
      _ ≤ (Ca * Cb * A ^ 2 * X ^ a) * 1 :=
        mul_le_mul_of_nonneg_left hroots (by positivity)
      _ ≤ _ := by
        have : 0 ≤ Ct * D ^ 2 * A ^ 2 * X ^ a := by positivity
        nlinarith only [this]

/-- A measurable moving difference is controlled by its unshifted norm on a larger interval. -/
theorem measurable_moving_difference_l2_bound {θ s X : ℝ} {u : ℝ → ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hs : s ∈ Icc (0 : ℝ) 1) (hX : 4 ≤ X)
    (hu : Measurable u) (huLp : MemLp u 2 (volume.restrict (Ioc (X / 4) (8 * X)))) :
    MemLp (fun x => u (movingShift θ s x) - u x) 2
        (volume.restrict (Ioc (X / 2) (4 * X))) ∧
      intervalL2 (X / 2) (4 * X) (fun x => u (movingShift θ s x) - u x) ≤
        2 * intervalL2 (X / 4) (8 * X) u := by
  have hX0 : 0 < X := by linarith
  have hφ : Continuous (movingShift θ s) :=
    continuous_id.add (continuous_const.mul (Real.continuous_rpow_const hθ.le))
  have hdp (x : ℝ) (hx : x ∈ Icc (X / 2) (4 * X)) :
      HasDerivAt (movingShift θ s) (1 + s * (θ * x ^ (θ - 1))) x :=
    (hasDerivAt_id x).add
      ((Real.hasDerivAt_rpow_const (Or.inl (by linarith [hx.1] : x ≠ 0))).const_mul s)
  have him (x : ℝ) (hx : x ∈ Icc (X / 2) (4 * X)) :
      movingShift θ s x ∈ Icc (X / 4) (8 * X) := by
    have hx1 : 1 ≤ x := by linarith [hx.1]
    have h0 : 0 ≤ s * x ^ θ := mul_nonneg hs.1 (Real.rpow_nonneg (by linarith) θ)
    have h1 : s * x ^ θ ≤ x :=
      (mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) θ) hs.2).trans
        (Real.rpow_le_self_of_one_le hx1 hθ1.le)
    dsimp [movingShift]
    constructor <;> linarith [hx.1, hx.2]
  have hc := square_comp_le (show X / 2 ≤ 4 * X by linarith)
    (show X / 4 ≤ 8 * X by linarith) hu huLp hφ.continuousOn
    (fun x hx => (hdp x hx).hasDerivWithinAt)
    (fun x hx => by
      have hn : 0 ≤ s * (θ * x ^ (θ - 1)) :=
        mul_nonneg hs.1 (mul_nonneg hθ.le (Real.rpow_nonneg (by linarith [hx.1]) _))
      linarith) him
  have hiu := huLp.mono_measure (Measure.restrict_mono
    (show Ioc (X / 2) (4 * X) ⊆ Ioc (X / 4) (8 * X) from
      Ioc_subset_Ioc (by linarith) (by linarith)) le_rfl)
  have hic : MemLp (fun x => u (movingShift θ s x)) 2
      (volume.restrict (Ioc (X / 2) (4 * X))) :=
    (memLp_two_iff_integrable_sq (hu.comp hφ.measurable).aestronglyMeasurable).mpr
      (hc.1.mono_set Ioc_subset_Icc_self)
  refine ⟨hic.sub hiu, ?_⟩
  have hib : IntervalIntegrable (fun x => u x ^ 2) volume (X / 4) (8 * X) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : X / 4 ≤ 8 * X)]
    exact huLp.integrable_sq
  have hic' : IntervalIntegrable (fun x => u (movingShift θ s x) ^ 2)
      volume (X / 2) (4 * X) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : X / 2 ≤ 4 * X)]
    exact hc.1
  have hiu' : IntervalIntegrable (fun x => u x ^ 2) volume (X / 2) (4 * X) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : X / 2 ≤ 4 * X)]
    exact hiu.integrable_sq
  have hm := intervalIntegral.integral_mono_interval
    (show X / 4 ≤ X / 2 by linarith) (show X / 2 ≤ 4 * X by linarith)
    (show 4 * X ≤ 8 * X by linarith) (Eventually.of_forall fun _ => sq_nonneg _) hib
  have hsq : (∫ x in (X / 2)..(4 * X), (u (movingShift θ s x) - u x) ^ 2) ≤
      4 * ∫ x in (X / 4)..(8 * X), u x ^ 2 := by
    calc
      _ ≤ ∫ x in (X / 2)..(4 * X), 2 * u (movingShift θ s x) ^ 2 + 2 * u x ^ 2 := by
        simp only [intervalIntegral.integral_of_le (show X / 2 ≤ 4 * X by linarith)]
        apply integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
          (((hic'.const_mul 2).add (hiu'.const_mul 2)).1)
        exact Eventually.of_forall (fun x => by nlinarith only [sq_nonneg (u (movingShift θ s x) + u x)])
      _ = 2 * (∫ x in (X / 2)..(4 * X), u (movingShift θ s x) ^ 2) +
          2 * ∫ x in (X / 2)..(4 * X), u x ^ 2 := by
        rw [intervalIntegral.integral_add (hic'.const_mul 2) (hiu'.const_mul 2)]
        simp only [intervalIntegral.integral_const_mul]
      _ ≤ _ := by linarith [hc.2]
  have hb := intervalIntegral.integral_nonneg_of_forall (μ := volume)
    (show X / 4 ≤ 8 * X by linarith) (fun x => sq_nonneg (u x))
  unfold intervalL2
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt hb]
  simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using hsq

/-- Derivative bounds at the terminal scale control its long moving difference. -/
theorem terminal_moving_difference_bounds {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : ℝ → ℝ, ∀ A K : ℝ,
        0 ≤ A → X ^ b ≤ K → ContDiff ℝ 1 u →
        intervalL2 (X / 4) (8 * X) (deriv u) ≤ A / Real.sqrt K →
        (∀ y ∈ Icc (X / 4) (8 * X), |deriv u y| ≤ A / K) →
        intervalL2 (X / 2) (4 * X) (fun x => u (movingShift b t x) - u x) ≤
          C * A * Real.sqrt K ∧
        intervalL2 (X / 2) (4 * X) (deriv (fun x => u (movingShift b t x) - u x)) ≤
          C * A / Real.sqrt K ∧
        (∀ y ∈ Icc (X / 2) (4 * X), |u (movingShift b t y) - u y| ≤ C * A) := by
  obtain ⟨C, hC, hs⟩ := smooth_moving_difference_outer_bounds hb hb1
  refine ⟨C + 4, by positivity, ?_⟩
  filter_upwards [hs, eventually_ge_atTop (4 : ℝ)] with X hs hX
  intro t ht u A K hA hk hu hDn hDs
  have hX0 : 0 < X := by linarith
  have hK : 0 < K := (Real.rpow_pos_of_pos hX0 b).trans_le hk
  have hroot : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have he : K / Real.sqrt K = Real.sqrt K := by
    apply (div_eq_iff hroot.ne').mpr
    nlinarith only [Real.sq_sqrt hK.le]
  have hn := hs t ht u hu
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ C * X ^ b * (A / Real.sqrt K) := hn.1.trans
        (mul_le_mul_of_nonneg_left hDn (by positivity))
      _ ≤ C * K * (A / Real.sqrt K) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hC.le) (by positivity)
      _ = C * A * Real.sqrt K := by rw [show C * K * (A / Real.sqrt K) = C * A * (K / Real.sqrt K) by ring, he]
      _ ≤ _ := by nlinarith [Real.sqrt_nonneg K]
  · exact (hn.2.2.trans (mul_le_mul_of_nonneg_left hDn hC.le)).trans
      (by simpa only [mul_div_assoc] using
        (div_le_div_of_nonneg_right (show C * A ≤ (C + 4) * A by nlinarith) (Real.sqrt_nonneg K)))
  intro y hy
  have hy1 : 1 ≤ y := by linarith [hy.1]
  have hgap0 : 0 ≤ t * y ^ b := mul_nonneg ht.1 (Real.rpow_nonneg (by linarith) b)
  have hgap1 : t * y ^ b ≤ y :=
    (mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) b) ht.2).trans
      (Real.rpow_le_self_of_one_le hy1 hb1.le)
  have hgap : t * y ^ b ≤ 4 * X ^ b := by
    calc
      _ ≤ y ^ b := mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) b) ht.2
      _ ≤ (4 * X) ^ b := Real.rpow_le_rpow (by linarith) hy.2 hb.le
      _ = 4 ^ b * X ^ b := Real.mul_rpow (by norm_num) hX0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hb1.le)
        (Real.rpow_nonneg hX0.le b)
  have hym : y ≤ movingShift b t y := by dsimp [movingShift]; linarith
  have hsub : Icc y (movingShift b t y) ⊆ Icc (X / 4) (8 * X) := by
    intro z hz
    dsimp [movingShift] at hz
    constructor <;> linarith [hy.1, hy.2, hz.1, hz.2]
  have heq := intervalIntegral.integral_deriv_of_contDiffOn_Icc
    (hu.contDiffOn : ContDiffOn ℝ 1 u (Icc y (movingShift b t y))) hym
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := deriv u) (a := y) (b := movingShift b t y) (C := A / K)
    (fun z hz => by
      have hz' : z ∈ Icc y (movingShift b t y) := by
        have : z ∈ Ioc y (movingShift b t y) := by simpa only [uIoc_of_le hym] using hz
        exact ⟨this.1.le, this.2⟩
      simpa only [Real.norm_eq_abs] using hDs z (hsub hz'))
  rw [heq, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hym)] at hbound
  have hegap : movingShift b t y - y = t * y ^ b := by simp [movingShift]
  rw [hegap] at hbound
  calc
    _ ≤ (t * y ^ b) * (A / K) := by simpa only [mul_comm] using hbound
    _ ≤ (4 * K) * (A / K) :=
      mul_le_mul_of_nonneg_right (hgap.trans (by linarith)) (by positivity)
    _ = 4 * A := by field_simp
    _ ≤ _ := by nlinarith

/-- Uniform bounds for the two residuals and all block pairs sum with quadratic dyadic cost. -/
theorem finite_covariance_expansion_bound {l r B₀ B₁ B₂ B₃ B₄ : ℝ} {N : ℕ}
    {F p₀ p₁ p₂ : ℝ → ℝ} {p₃ : ℕ → ℝ → ℝ} {p₄ : ℕ → ℕ → ℝ → ℝ}
    (h₀ : IntervalIntegrable p₀ volume l r) (h₁ : IntervalIntegrable p₁ volume l r)
    (h₂ : IntervalIntegrable p₂ volume l r)
    (h₃ : ∀ j ∈ Finset.range N, IntervalIntegrable (p₃ j) volume l r)
    (h₄ : ∀ j ∈ Finset.range N, ∀ i ∈ Finset.range N, IntervalIntegrable (p₄ j i) volume l r)
    (he : ∀ x ∈ uIcc l r, F x = p₀ x + p₁ x + p₂ x +
      ∑ j ∈ Finset.range N, p₃ j x + ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N, p₄ j i x)
    (hb₀ : |∫ x in l..r, p₀ x| ≤ B₀) (hb₁ : |∫ x in l..r, p₁ x| ≤ B₁)
    (hb₂ : |∫ x in l..r, p₂ x| ≤ B₂)
    (hb₃ : ∀ j ∈ Finset.range N, |∫ x in l..r, p₃ j x| ≤ B₃)
    (hb₄ : ∀ j ∈ Finset.range N, ∀ i ∈ Finset.range N, |∫ x in l..r, p₄ j i x| ≤ B₄) :
    |∫ x in l..r, F x| ≤ B₀ + B₁ + B₂ + (N : ℝ) * B₃ + (N : ℝ) ^ 2 * B₄ := by
  have hs₃ : IntervalIntegrable (fun x => ∑ j ∈ Finset.range N, p₃ j x) volume l r := by
    convert IntervalIntegrable.sum (Finset.range N) h₃ using 1
    funext x
    simp only [Finset.sum_apply]
  have hs₄j (j : ℕ) (hj : j ∈ Finset.range N) :
      IntervalIntegrable (fun x => ∑ i ∈ Finset.range N, p₄ j i x) volume l r := by
    convert IntervalIntegrable.sum (Finset.range N) (h₄ j hj) using 1
    funext x
    simp only [Finset.sum_apply]
  have hs₄ : IntervalIntegrable (fun x => ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N, p₄ j i x) volume l r := by
    convert IntervalIntegrable.sum (Finset.range N) hs₄j using 1
    funext x
    simp only [Finset.sum_apply]
  rw [intervalIntegral.integral_congr he,
    intervalIntegral.integral_add (((h₀.add h₁).add h₂).add hs₃) hs₄,
    intervalIntegral.integral_add ((h₀.add h₁).add h₂) hs₃,
    intervalIntegral.integral_add (h₀.add h₁) h₂,
    intervalIntegral.integral_add h₀ h₁,
    intervalIntegral.integral_finsetSum h₃,
    intervalIntegral.integral_finsetSum hs₄j]
  have he₄ : (∑ j ∈ Finset.range N, ∫ x in l..r, ∑ i ∈ Finset.range N, p₄ j i x) =
      ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N, ∫ x in l..r, p₄ j i x :=
    Finset.sum_congr rfl (fun j hj => intervalIntegral.integral_finsetSum (h₄ j hj))
  rw [he₄]
  have hs₃' := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hb₃)
  have hs₄' : |∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N, ∫ x in l..r, p₄ j i x| ≤
      (N : ℝ) ^ 2 * B₄ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have hb (j : ℕ) (hj : j ∈ Finset.range N) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (hb₄ j hj))
    have hh := Finset.sum_le_sum hb
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hh
    nlinarith only [hh]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs₃'
  exact (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add hb₀ hb₁)) hb₂)) hs₃')) hs₄')

end
end D5.S3.Arith.Robin.ForwardKernel.DyadicCovariancePairs
