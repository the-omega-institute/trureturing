/- GID: D5/S3/Estimation/TimeArrow/SharedRectangleCalibration
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/SharedRectangleCalibration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Four adjacent native score cells share one moving logistic calibration. -/

import D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes

open scoped BigOperators Topology
open Finset Filter
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
noncomputable section

/-- The score of a native count cell, with the compensation retained. -/
def cellScore (r ε : ℝ) (k l : ℕ) : ℝ :=
  (k : ℝ) * Real.log ((1 + r) / (1 - ε)) +
    (l : ℝ) * Real.log ((1 - r) / (1 + ε))

/-- The four score increments relative to the lower-left count cell. -/
def offsets (r ε : ℝ) : Fin 4 → ℝ :=
  ![0, Real.log ((1 + r) / (1 - ε)), Real.log ((1 - r) / (1 + ε)),
    Real.log ((1 + r) / (1 - ε)) + Real.log ((1 - r) / (1 + ε))]

/-- The checkerboard change of the calibration equation at fixed root. -/
def checkerboard (r ε x : ℝ) : ℝ :=
  Real.sigmoid x + Real.sigmoid (x + offsets r ε 3) -
    Real.sigmoid (x + offsets r ε 1) - Real.sigmoid (x + offsets r ε 2)

/-- Real interpolation of the four counts with both margins fixed. The
order is A, B, C, D, and the count in A is the parameter `t`. -/
def cellCounts (N R U t : ℝ) : Fin 4 → ℝ :=
  ![t, U - t, R - t, N - R - U + t]

/-- All rows outside the four cells remain in the calibration sum. -/
def calibratedMean {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U t x : ℝ) : ℝ :=
  (∑ i, Real.sigmoid (x + outside i)) +
    ∑ j, cellCounts N R U t j * Real.sigmoid (x + offsets r ε j)

/-- The variance of the same full Bernoulli calibration. -/
def calibratedVariance {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U t x : ℝ) : ℝ :=
  (∑ i, Real.sigmoid (x + outside i) * (1 - Real.sigmoid (x + outside i))) +
    ∑ j, cellCounts N R U t j * Real.sigmoid (x + offsets r ε j) *
      (1 - Real.sigmoid (x + offsets r ε j))

private theorem sigmoid_log {u : ℝ} (hu : 0 < u) :
    Real.sigmoid (Real.log u) = u / (1 + u) := by
  rw [Real.sigmoid_def, Real.exp_neg, Real.exp_log hu]
  field_simp
  <;> ring

private theorem checkerboard_center {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    checkerboard r 0 0 = -r ^ 4 / (2 * (2 - r ^ 2) * (4 - r ^ 2)) := by
  have hp : 0 < 1 + r := by linarith
  have hm : 0 < 1 - r := by linarith
  have hpq : 0 < (1 + r) * (1 - r) := mul_pos hp hm
  have h2 : 0 < 2 - r ^ 2 := by nlinarith
  have h4 : 0 < 4 - r ^ 2 := by nlinarith
  have hlog : Real.log (1 + r) + Real.log (1 - r) =
      Real.log ((1 + r) * (1 - r)) :=
    (Real.log_mul (ne_of_gt hp) (ne_of_gt hm)).symm
  change Real.sigmoid 0 +
    Real.sigmoid (0 + (Real.log ((1 + r) / (1 - 0)) +
      Real.log ((1 - r) / (1 + 0)))) -
    Real.sigmoid (0 + Real.log ((1 + r) / (1 - 0))) -
    Real.sigmoid (0 + Real.log ((1 - r) / (1 + 0))) = _
  simp only [zero_add, sub_zero, add_zero, div_one, Real.sigmoid_zero]
  rw [hlog, sigmoid_log hpq, sigmoid_log hp, sigmoid_log hm]
  field_simp
  <;> ring

private theorem checkerboard_center_neg {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    checkerboard r 0 0 < 0 := by
  rw [checkerboard_center hr hr1]
  have h2 : 0 < 2 - r ^ 2 := by nlinarith
  have h4 : 0 < 4 - r ^ 2 := by nlinarith
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (pow_pos hr 4)) (by positivity)

private theorem sigmoid_shift_deriv (a x : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sigmoid (x + a))
      (Real.sigmoid (x + a) * (1 - Real.sigmoid (x + a))) x := by
  simpa only [Function.comp_def, mul_one] using! (Real.hasDerivAt_sigmoid (x + a)).comp x ((hasDerivAt_id x).add_const a)

/-- Differentiate the complete calibration along one common root. The
histogram derivative is the checkerboard term, rather than four independent
root derivatives. -/
theorem moving_calibration_deriv {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U t x v : ℝ) (θ : ℝ → ℝ) (hθ : HasDerivAt θ v t)
    (hx : θ t = x) :
    HasDerivAt (fun t => calibratedMean outside r ε N R U t (θ t))
      (checkerboard r ε x + calibratedVariance outside r ε N R U t x * v) t := by
  classical
  have ho : HasDerivAt (fun t => ∑ i, Real.sigmoid (θ t + outside i))
      ((∑ i, Real.sigmoid (x + outside i) * (1 - Real.sigmoid (x + outside i))) * v) t := by
    simpa only [Function.comp_def, hx, sum_mul] using!
      HasDerivAt.sum (fun i (_ : i ∈ (univ : Finset ι)) =>
        (sigmoid_shift_deriv (outside i) (θ t)).comp t hθ)
  have hc (j : Fin 4) : HasDerivAt (fun t => cellCounts N R U t j)
      (![1, -1, -1, 1] j) t := by
    fin_cases j
    · exact hasDerivAt_id t
    · change HasDerivAt (fun a : ℝ => U - a) (-1) t
      simpa only [sub_zero, zero_sub] using! (hasDerivAt_const t U).sub (hasDerivAt_id t)
    · change HasDerivAt (fun a : ℝ => R - a) (-1) t
      simpa only [sub_zero, zero_sub] using! (hasDerivAt_const t R).sub (hasDerivAt_id t)
    · change HasDerivAt (fun a : ℝ => N - R - U + a) 1 t
      simpa only [zero_add] using! (hasDerivAt_const t (N - R - U)).add (hasDerivAt_id t)
  have hi := ho.add (HasDerivAt.sum (fun j (_ : j ∈ (univ : Finset (Fin 4))) =>
    (hc j).mul ((sigmoid_shift_deriv (offsets r ε j) (θ t)).comp t hθ)))
  convert! hi using 1
  simp [calibratedVariance, checkerboard, hx, Fin.sum_univ_four, cellCounts, offsets,
    Function.comp_def]
  <;> ring

/-- Every differentiable root of the same constant calibration equation has
the shared implicit response `-Delta / Dcal`. -/
theorem shared_root_response {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U q t x v : ℝ) (θ : ℝ → ℝ) (hθ : HasDerivAt θ v t)
    (hx : θ t = x)
    (hcal : ∀ᶠ a in 𝓝 t, calibratedMean outside r ε N R U a (θ a) = q)
    (hv : calibratedVariance outside r ε N R U t x ≠ 0) :
    v = -checkerboard r ε x / calibratedVariance outside r ε N R U t x := by
  have hd := moving_calibration_deriv outside r ε N R U t x v θ hθ hx
  have hz := hd.unique ((hasDerivAt_const t q).congr_of_eventuallyEq hcal)
  apply (eq_div_iff hv).mpr
  nlinarith

private theorem calibration_root_deriv {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U t x : ℝ) :
    HasDerivAt (calibratedMean outside r ε N R U t)
      (calibratedVariance outside r ε N R U t x) x := by
  classical
  have ho := HasDerivAt.sum (fun i (_ : i ∈ (univ : Finset ι)) =>
    sigmoid_shift_deriv (outside i) x)
  have hi := HasDerivAt.sum (fun j (_ : j ∈ (univ : Finset (Fin 4))) =>
    (sigmoid_shift_deriv (offsets r ε j) x).const_mul (cellCounts N R U t j))
  convert! ho.add hi using 1
  simp only [calibratedVariance]
  congr 1
  apply sum_congr rfl
  intro j _
  ring

/-- A locally defined shared calibration root exists whenever its actual full
variance is nonzero. Its derivative is computed from the same histogram. -/
theorem exists_shared_calibration_root {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U q t x : ℝ)
    (hcal : calibratedMean outside r ε N R U t x = q)
    (hv : calibratedVariance outside r ε N R U t x ≠ 0) :
    ∃ θ : ℝ → ℝ, θ t = x ∧
      (∀ᶠ a in 𝓝 t, calibratedMean outside r ε N R U a (θ a) = q) ∧
      HasDerivAt θ
        (-checkerboard r ε x / calibratedVariance outside r ε N R U t x) t := by
  classical
  let f := calibratedMean outside r ε N R U
  let f₁ : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun _ x =>
    ContinuousLinearMap.toSpanSingleton ℝ (checkerboard r ε x)
  let f₂ : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun t x =>
    ContinuousLinearMap.toSpanSingleton ℝ (calibratedVariance outside r ε N R U t x)
  have df₁ : ∀ᶠ a : ℝ × ℝ in 𝓝 (t, x), HasFDerivAt (f · a.2) (f₁ a.1 a.2) a.1 := by
    apply Filter.Eventually.of_forall
    intro a
    have hd := moving_calibration_deriv outside r ε N R U a.1 a.2 0
      (fun _ => a.2) (hasDerivAt_const a.1 a.2) rfl
    simpa only [mul_zero, add_zero] using hd.hasFDerivAt
  have df₂ : ∀ᶠ a : ℝ × ℝ in 𝓝 (t, x), HasFDerivAt (f a.1 ·) (f₂ a.1 a.2) a.2 :=
    Filter.Eventually.of_forall fun a =>
      (calibration_root_deriv outside r ε N R U a.1 a.2).hasFDerivAt
  have cf₁ : ContinuousAt (Function.uncurry f₁) (t, x) := by
    unfold f₁
    apply (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.continuousAt.comp
    dsimp [checkerboard]
    fun_prop
  have cf₂ : ContinuousAt (Function.uncurry f₂) (t, x) := by
    unfold f₂
    apply (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.continuousAt.comp
    dsimp [calibratedVariance, cellCounts]
    fun_prop
  have iv : (f₂ t x).IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := ContinuousLinearMap.toSpanSingleton ℝ
        (calibratedVariance outside r ε N R U t x)⁻¹)
    · ext a
      simp [f₂, mul_comm, mul_left_comm, hv]
    · ext a
      simp [f₂, mul_comm, mul_left_comm, hv]
  let θ := implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ iv
  have hx : θ t = x :=
    (eventually_apply_eq_iff_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ iv).self_of_nhds.mp rfl
  have hθ := (hasStrictFDerivAt_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ iv).hasFDerivAt.hasDerivAt
  have he : ∀ᶠ a in 𝓝 t, calibratedMean outside r ε N R U a (θ a) = q := by
    simpa only [hcal] using eventually_apply_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ iv
  refine ⟨θ, hx, he, ?_⟩
  rwa [shared_root_response outside r ε N R U q t x _ θ hθ hx he hv] at hθ

/-- The count-weighted A-cell response includes the feedback through the
common calibration; its sign at the symmetric center is strictly positive. -/
theorem calibrated_group_center_response {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r N R U q t bg : ℝ) (θ : ℝ → ℝ) (v : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hθ : HasDerivAt θ v t) (hx : θ t = 0)
    (hcal : ∀ᶠ a in 𝓝 t, calibratedMean outside r 0 N R U a (θ a) = q)
    (hv : 0 < calibratedVariance outside r 0 N R U t 0) (hc : 0 < bg + t) :
    HasDerivAt (fun a => (bg + a) * Real.sigmoid (θ a))
      (1 / 2 - (bg + t) * (1 / 4) * checkerboard r 0 0 /
        calibratedVariance outside r 0 N R U t 0) t ∧
    1 / 2 < 1 / 2 - (bg + t) * (1 / 4) * checkerboard r 0 0 /
      calibratedVariance outside r 0 N R U t 0 := by
  have he := shared_root_response outside r 0 N R U q t 0 v θ hθ hx hcal (ne_of_gt hv)
  have hm := ((hasDerivAt_id t).const_add bg).mul ((Real.hasDerivAt_sigmoid (θ t)).comp t hθ)
  constructor
  · convert! hm using 1
    · rfl
    · rw [hx, Real.sigmoid_zero, he]
      ring
  · have hn := checkerboard_center_neg hr hr1
    have hneg : (bg + t) * (1 / 4) * checkerboard r 0 0 /
        calibratedVariance outside r 0 N R U t 0 < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos hc (by norm_num)) hn) hv
    linarith

end
end D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
