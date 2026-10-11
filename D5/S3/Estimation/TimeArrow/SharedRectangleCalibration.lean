/- GID: D5/S3/Estimation/TimeArrow/SharedRectangleCalibration
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/SharedRectangleCalibration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Four adjacent score cells share one moving logistic calibration. -/

import Mathlib

open scoped BigOperators Topology
open Finset Filter

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
noncomputable section

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
    convert! HasDerivAt.sum (fun i (_ : i ∈ (univ : Finset ι)) =>
      (sigmoid_shift_deriv (outside i) (θ t)).comp t hθ) using 1
    · ext a
      simp
    · simp only [hx, sum_mul]
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
  · funext y
    simp only [calibratedMean, Pi.add_apply, Finset.sum_apply]
  · simp only [calibratedVariance, mul_assoc]

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
    simpa only [f, θ, hcal] using eventually_apply_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ iv
  refine ⟨θ, hx, he, ?_⟩
  rwa [shared_root_response outside r ε N R U q t x _ θ hθ hx he hv] at hθ

/-- The compensated group response uses the same root and full variance. -/
theorem compensated_group_deriv {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U q bg t x v : ℝ) (θ : ℝ → ℝ) (hθ : HasDerivAt θ v t)
    (hx : θ t = x)
    (hcal : ∀ᶠ u in 𝓝 t, calibratedMean outside r ε N R U u (θ u) = q)
    (hv : calibratedVariance outside r ε N R U t x ≠ 0) :
    HasDerivAt (fun u => (bg + u) * Real.sigmoid (θ u) - u / 2)
      (Real.sigmoid x - 1 / 2 - (bg + t) * Real.sigmoid x * (1 - Real.sigmoid x) *
        checkerboard r ε x / calibratedVariance outside r ε N R U t x) t := by
  have hr := shared_root_response outside r ε N R U q t x v θ hθ hx hcal hv
  have hg := (((hasDerivAt_id t).const_add bg).mul
    ((Real.hasDerivAt_sigmoid (θ t)).comp t hθ)).sub ((hasDerivAt_id t).div_const 2)
  convert! hg using 1
  simp only [Function.comp_apply, id_eq, hr, hx]
  ring

private theorem continuous_checkerboard_parameters {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ContinuousAt (fun a : ℝ × ℝ => checkerboard r a.1 a.2) (0, 0) := by
  have hp : (1 + r) / (1 - (0 : ℝ)) ≠ 0 := by simp; linarith
  have hm : (1 - r) / (1 + (0 : ℝ)) ≠ 0 := by simp; linarith
  have hpden : (1 : ℝ) - ((0, 0) : ℝ × ℝ).1 ≠ 0 := by norm_num
  have hmden : (1 : ℝ) + ((0, 0) : ℝ × ℝ).1 ≠ 0 := by norm_num
  have cp : ContinuousAt (fun a : ℝ × ℝ => Real.log ((1 + r) / (1 - a.1))) (0, 0) :=
    (continuousAt_const.div (continuousAt_const.sub continuous_fst.continuousAt) hpden).log hp
  have cm : ContinuousAt (fun a : ℝ × ℝ => Real.log ((1 - r) / (1 + a.1))) (0, 0) :=
    (continuousAt_const.div (continuousAt_const.add continuous_fst.continuousAt) hmden).log hm
  change ContinuousAt (fun a : ℝ × ℝ =>
    Real.sigmoid a.2 + Real.sigmoid (a.2 + (Real.log ((1 + r) / (1 - a.1)) +
      Real.log ((1 - r) / (1 + a.1)))) -
    Real.sigmoid (a.2 + Real.log ((1 + r) / (1 - a.1))) -
    Real.sigmoid (a.2 + Real.log ((1 - r) / (1 + a.1)))) (0, 0)
  exact (((continuous_sigmoid.continuousAt.comp continuous_snd.continuousAt).add
    (continuous_sigmoid.continuousAt.comp (continuous_snd.continuousAt.add (cp.add cm)))).sub
    (continuous_sigmoid.continuousAt.comp (continuous_snd.continuousAt.add cp))).sub
    (continuous_sigmoid.continuousAt.comp (continuous_snd.continuousAt.add cm))

/-- Strictly negative checkerboard response persists in a full neighborhood
of the compensated symmetric center, with one constant for all outside rows. -/
theorem checkerboard_negative_neighborhood {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ a : ℝ × ℝ in 𝓝 (0, 0), checkerboard r a.1 a.2 < -d := by
  let d := -checkerboard r 0 0 / 2
  have hd : 0 < d := by dsimp [d]; linarith [checkerboard_center_neg hr hr1]
  refine ⟨d, hd, ?_⟩
  exact (continuous_checkerboard_parameters hr hr1).eventually_lt_const (by dsimp [d]; linarith [checkerboard_center_neg hr hr1])


private theorem cellCounts_sum (N R U t : ℝ) : (∑ j, cellCounts N R U t j) = N := by
  simp [Fin.sum_univ_four, cellCounts]
  ring

private theorem calibratedVariance_pos {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U t x : ℝ) (hN : 0 < N)
    (hc : ∀ j, 0 ≤ cellCounts N R U t j) :
    0 < calibratedVariance outside r ε N R U t x := by
  classical
  have hp (a : ℝ) : 0 < Real.sigmoid a * (1 - Real.sigmoid a) :=
    mul_pos (Real.sigmoid_pos a) (sub_pos.mpr (Real.sigmoid_lt_one a))
  have hj : ∃ j, 0 < cellCounts N R U t j := by
    by_contra hn
    push_neg at hn
    have hs := sum_nonpos (fun j (_ : j ∈ (univ : Finset (Fin 4))) => hn j)
    rw [cellCounts_sum] at hs
    linarith
  rcases hj with ⟨j, hj⟩
  have ho : 0 ≤ ∑ i, Real.sigmoid (x + outside i) * (1 - Real.sigmoid (x + outside i)) :=
    sum_nonneg fun i _ => (hp _).le
  have hi : 0 < ∑ j, cellCounts N R U t j * Real.sigmoid (x + offsets r ε j) *
      (1 - Real.sigmoid (x + offsets r ε j)) := by
    have he := single_le_sum (s := univ) (f := fun j => cellCounts N R U t j *
      Real.sigmoid (x + offsets r ε j) * (1 - Real.sigmoid (x + offsets r ε j)))
      (fun k _ => by rw [mul_assoc]; exact mul_nonneg (hc k) (hp _).le) (mem_univ j)
    have hjp : 0 < cellCounts N R U t j * Real.sigmoid (x + offsets r ε j) *
        (1 - Real.sigmoid (x + offsets r ε j)) := by
      rw [mul_assoc]
      exact mul_pos hj (hp _)
    exact hjp.trans_le he
  exact add_pos_of_nonneg_of_pos ho hi

private theorem unique_shared_root {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U q t : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hqM : q < (Fintype.card ι : ℝ) + N)
    (hc : ∀ j, 0 ≤ cellCounts N R U t j) :
    ∃! x, calibratedMean outside r ε N R U t x = q := by
  classical
  have hbot (a : ℝ) : Tendsto (fun x : ℝ => Real.sigmoid (x + a)) atBot (𝓝 0) :=
    Real.tendsto_sigmoid_atBot.comp (tendsto_atBot_add_const_right _ a tendsto_id)
  have htop (a : ℝ) : Tendsto (fun x : ℝ => Real.sigmoid (x + a)) atTop (𝓝 1) :=
    Real.tendsto_sigmoid_atTop.comp (tendsto_atTop_add_const_right _ a tendsto_id)
  have hb : Tendsto (calibratedMean outside r ε N R U t) atBot (𝓝 0) := by
    simpa [calibratedMean] using!
      (tendsto_finsetSum univ (fun i _ => hbot (outside i))).add
        (tendsto_finsetSum univ (fun j _ => (hbot (offsets r ε j)).const_mul
          (cellCounts N R U t j)))
  have ht : Tendsto (calibratedMean outside r ε N R U t) atTop
      (𝓝 ((Fintype.card ι : ℝ) + N)) := by
    simpa [calibratedMean, cellCounts_sum] using!
      (tendsto_finsetSum univ (fun i _ => htop (outside i))).add
        (tendsto_finsetSum univ (fun j _ => (htop (offsets r ε j)).const_mul
          (cellCounts N R U t j)))
  have hcont : Continuous (calibratedMean outside r ε N R U t) := by
    unfold calibratedMean
    fun_prop
  obtain ⟨x, hx⟩ := intermediate_value_univ₂_eventually₂ hcont continuous_const
    (hb.eventually_le_const hq) (ht.eventually_const_le hqM)
  have hm : StrictMono (calibratedMean outside r ε N R U t) :=
    strictMono_of_deriv_pos fun x => by
      rw [(calibration_root_deriv outside r ε N R U t x).deriv]
      exact calibratedVariance_pos outside r ε N R U t x hN hc
  exact ⟨x, hx, fun y hy => hm.injective (hy.trans hx.symm)⟩

/-- One shared root is defined on the entire feasible open interval. Local
implicit roots agree with it by uniqueness, so their responses belong to one
curve rather than separately selected roots. This does not assert a uniform
lower bound on the variance. -/
theorem shared_calibration_curve {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U q a b : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hqM : q < (Fintype.card ι : ℝ) + N)
    (hc : ∀ t ∈ Set.Ioo a b, ∀ j, 0 ≤ cellCounts N R U t j) :
    ∃ θ : ℝ → ℝ, ∀ t ∈ Set.Ioo a b,
      calibratedMean outside r ε N R U t (θ t) = q ∧
      HasDerivAt θ
        (-checkerboard r ε (θ t) / calibratedVariance outside r ε N R U t (θ t)) t ∧
      0 < calibratedVariance outside r ε N R U t (θ t) := by
  classical
  have hex (t : ℝ) (ht : t ∈ Set.Ioo a b) :=
    unique_shared_root outside r ε N R U q t hN hq hqM (hc t ht)
  let θ : ℝ → ℝ := fun t => if ht : t ∈ Set.Ioo a b then (hex t ht).exists.choose else 0
  have heq (t : ℝ) (ht : t ∈ Set.Ioo a b) :
      calibratedMean outside r ε N R U t (θ t) = q := by
    simp only [θ, dif_pos ht]
    exact (hex t ht).exists.choose_spec
  refine ⟨θ, fun t ht => ?_⟩
  have hv := calibratedVariance_pos outside r ε N R U t (θ t) hN (hc t ht)
  obtain ⟨φ, hφt, hφeq, hφder⟩ := exists_shared_calibration_root outside r ε N R U q
    t (θ t) (heq t ht) (ne_of_gt hv)
  have hagree : θ =ᶠ[𝓝 t] φ := by
    filter_upwards [hφeq, isOpen_Ioo.mem_nhds ht] with u hu hui
    exact (hex u hui).unique (heq u hui) hu
  exact ⟨heq t ht, hφt ▸ hφder.congr_of_eventuallyEq hagree, hv⟩


/-- At a centered feasible histogram the compensated feedback is uniformly
positive on one neighborhood of the same shared root curve. The neighborhood
and constants may depend on the finite histogram; no asymptotic uniformity is
asserted. -/
theorem positive_feedback_germ {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r N R U q bg a b t : ℝ) (hr : 0 < r) (hr1 : r < 1) (hN : 0 < N) (hq : 0 < q)
    (hqM : q < (Fintype.card ι : ℝ) + N) (ht : t ∈ Set.Ioo a b)
    (hc : ∀ u ∈ Set.Ioo a b, ∀ j, 0 ≤ cellCounts N R U u j)
    (hcenter : calibratedMean outside r 0 N R U t 0 = q) (hgroup : 0 < bg + t) :
    ∃ θ : ℝ → ℝ, ∃ d D : ℝ, 0 < d ∧ 0 < D ∧ θ t = 0 ∧
      ∀ᶠ u in 𝓝 t,
        calibratedMean outside r 0 N R U u (θ u) = q ∧
        checkerboard r 0 (θ u) < 0 ∧
        ∃ v, d ≤ v ∧ v ≤ D ∧
          HasDerivAt (fun x => (bg + x) * Real.sigmoid (θ x) - x / 2) v u := by
  obtain ⟨θ, hθ⟩ := shared_calibration_curve outside r 0 N R U q a b hN hq hqM hc
  have hzero : θ t = 0 :=
    (unique_shared_root outside r 0 N R U q t hN hq hqM (hc t ht)).unique
      (hθ t ht).1 hcenter
  let B : ℝ → ℝ := fun u => Real.sigmoid (θ u) - 1 / 2 -
    (bg + u) * Real.sigmoid (θ u) * (1 - Real.sigmoid (θ u)) * checkerboard r 0 (θ u) /
      calibratedVariance outside r 0 N R U u (θ u)
  have hv := (hθ t ht).2.2
  have hB0 : 0 < B t := by
    dsimp [B]
    rw [hzero]
    simp only [Real.sigmoid_zero]
    have hn := checkerboard_center_neg hr hr1
    have hp : 0 < (bg + t) * (2 : ℝ)⁻¹ * (1 - (2 : ℝ)⁻¹) := by
      positivity
    have hd := div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hp hn)
      (calibratedVariance_pos outside r 0 N R U t 0 hN (hc t ht))
    linarith
  have hθcont : ContinuousAt θ t := (hθ t ht).2.1.continuousAt
  have hBcont : ContinuousAt B t := by
    dsimp [B, calibratedVariance, cellCounts, checkerboard]
    fun_prop (disch := exact ne_of_gt hv)
  obtain ⟨d0, hd0, hnegative⟩ := checkerboard_negative_neighborhood hr hr1
  have hpair : Tendsto (fun u => ((0 : ℝ), θ u)) (𝓝 t) (𝓝 ((0 : ℝ), 0)) := by
    have hp : ContinuousAt (fun u => ((0 : ℝ), θ u)) t := continuousAt_const.prodMk hθcont
    change Tendsto (fun u => ((0 : ℝ), θ u)) (𝓝 t) (𝓝 ((0 : ℝ), θ t)) at hp
    simpa only [hzero] using hp
  have hn := hpair.eventually hnegative
  refine ⟨θ, B t / 2, 2 * B t, by positivity, by positivity, hzero, ?_⟩
  filter_upwards [isOpen_Ioo.mem_nhds ht, hn,
    hBcont.eventually_const_lt (by linarith : B t / 2 < B t),
    hBcont.eventually_lt_const (by linarith : B t < 2 * B t)] with u hu hn hlo hhi
  have hcal : ∀ᶠ x in 𝓝 u, calibratedMean outside r 0 N R U x (θ x) = q := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with x hx
    exact (hθ x hx).1
  exact ⟨(hθ u hu).1, by linarith, B u, hlo.le, hhi.le,
    compensated_group_deriv outside r 0 N R U q bg u (θ u) _ θ (hθ u hu).2.1 rfl
      hcal (ne_of_gt (hθ u hu).2.2)⟩

end
end D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
