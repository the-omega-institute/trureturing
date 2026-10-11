/- GID: D5/S3/Estimation/TimeArrow/SharedRectangleCalibration
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/SharedRectangleCalibration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Four adjacent score cells share one moving logistic calibration. -/

import D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
import D5.S3.Estimation.SequentialDecisionRisk.UniformPosteriorOdds

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
private theorem positive_feedback_germ {ι : Type*} [Fintype ι] (outside : ι → ℝ)
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

open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes

/-- Only true signal rows in the four adjacent count cells receive an
interior cell index. All background rows remain in the full outside sum. -/
def nativeRowCell {M q s : ℕ} (S : Support M q) (e : Experiment) (o : Obs M s e)
    (k l : ℕ) (i : Fin M) : Option (Fin 4) := by
  classical
  exact if i ∈ S.val then
    if count e o i 1 = k ∧ count e o i (-1) = l then some 0 else
    if count e o i 1 = k + 1 ∧ count e o i (-1) = l then some 1 else
    if count e o i 1 = k ∧ count e o i (-1) = l + 1 then some 2 else
    if count e o i 1 = k + 1 ∧ count e o i (-1) = l + 1 then some 3 else none
  else none

private theorem native_row_cell_iff {M q s : ℕ} (S : Support M q) (e : Experiment)
    (o : Obs M s e) (k l : ℕ) (i : Fin M) (j : Fin 4) :
    nativeRowCell S e o k l i = some j ↔ i ∈ S.val ∧
      count e o i 1 = k + ![0, 1, 0, 1] j ∧
      count e o i (-1) = l + ![0, 0, 1, 1] j := by
  classical
  by_cases hs : i ∈ S.val
  · by_cases hA : count e o i 1 = k ∧ count e o i (-1) = l
    · fin_cases j <;> simp [nativeRowCell, hs, hA, hA.1, hA.2]
    · by_cases hB : count e o i 1 = k + 1 ∧ count e o i (-1) = l
      · fin_cases j <;> simp [nativeRowCell, hs, hA, hB, hB.1, hB.2]
      · by_cases hC : count e o i 1 = k ∧ count e o i (-1) = l + 1
        · fin_cases j <;> simp [nativeRowCell, hs, hA, hB, hC, hC.1, hC.2]
        · by_cases hD : count e o i 1 = k + 1 ∧ count e o i (-1) = l + 1
          · fin_cases j <;> simp [nativeRowCell, hs, hA, hB, hC, hD, hD.1, hD.2]
          · fin_cases j <;> simp [nativeRowCell, hs, hA, hB, hC, hD]
  · simp [nativeRowCell, hs]

/-- The exact labelled row subsets supplying the four calibration counts. -/
def nativeCalibrationCells {M q s : ℕ} (S : Support M q) (e : Experiment)
    (o : Obs M s e) (k l : ℕ) (j : Fin 4) : Finset (Fin M) := by
  classical
  exact univ.filter fun i => nativeRowCell S e o k l i = some j

private theorem native_row_score_offset {M q s : ℕ} (S : Support M q) (r : ℝ)
    (e : Experiment) (o : Obs M s e) (k l : ℕ) (i : Fin M) (j : Fin 4)
    (hij : nativeRowCell S e o k l i = some j) :
    score q r e o i -
      ((k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
        (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))) =
      offsets r (compensation M q r) j := by
  have hi := (native_row_cell_iff S e o k l i j).mp hij
  unfold score
  rw [hi.2.1, hi.2.2]
  fin_cases j <;> simp [offsets] <;> ring

/-- The full original row calibration is the same one shared by the four
cells. The outside index contains every background row and every signal row
outside the rectangle; no row is discarded. -/
theorem native_full_calibration_sum {M q s : ℕ} (S : Support M q) (r : ℝ)
    (e : Experiment) (o : Obs M s e) (k l : ℕ) (x : ℝ) :
    let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
      (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
    let C : Fin 4 → ℝ := fun j => (nativeCalibrationCells S e o k l j).card
    let outside : {i : Fin M // nativeRowCell S e o k l i = none} → ℝ :=
      fun i => score q r e o i.val - z0
    (∑ i : Fin M, Real.sigmoid (x + (score q r e o i - z0))) =
      calibratedMean outside r (compensation M q r)
        (C 0 + C 1 + C 2 + C 3) (C 0 + C 2) (C 0 + C 1) (C 0) x := by
  classical
  dsimp only
  let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
      (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
  let C : Fin 4 → ℝ := fun j => (nativeCalibrationCells S e o k l j).card
  let f : Fin M → ℝ := fun i => Real.sigmoid (x + (score q r e o i - z0))
  have hf (j : Fin 4) :
      (∑ i ∈ univ.filter (fun i => nativeRowCell S e o k l i = some j), f i) =
        C j * Real.sigmoid (x + offsets r (compensation M q r) j) := by
    calc
      _ = ∑ _i ∈ nativeCalibrationCells S e o k l j,
          Real.sigmoid (x + offsets r (compensation M q r) j) := by
        apply sum_congr rfl
        intro i hi
        dsimp only [f]
        rw [native_row_score_offset S r e o k l i j (mem_filter.mp hi).2]
      _ = _ := by simp only [sum_const, nsmul_eq_mul]; rfl
  have hcounts (j : Fin 4) :
      cellCounts (C 0 + C 1 + C 2 + C 3) (C 0 + C 2) (C 0 + C 1) (C 0) j = C j := by
    fin_cases j <;> dsimp [cellCounts] <;> ring
  have hsum := (sum_fiberwise univ (nativeRowCell S e o k l) f).symm
  rw [Fintype.sum_option] at hsum
  rw [hsum]
  unfold calibratedMean
  change (∑ i with nativeRowCell S e o k l i = none, f i) +
      (∑ j, ∑ i with nativeRowCell S e o k l i = some j, f i) =
    (∑ i : {i : Fin M // nativeRowCell S e o k l i = none}, f i.val) +
      ∑ j, cellCounts (C 0 + C 1 + C 2 + C 3) (C 0 + C 2) (C 0 + C 1) (C 0) j *
        Real.sigmoid (x + offsets r (compensation M q r) j)
  simp only [hcounts]
  congr 1
  · exact (sum_subtype (univ.filter fun i => nativeRowCell S e o k l i = none)
      (fun i => by simp) f)
  · exact sum_congr rfl (fun j _ => hf j)

private theorem native_calibrated_row_parameter {M q s : ℕ} (r : ℝ)
    (e : Experiment) (o : Obs M s e)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (t : ℝ) (ht : 0 < t) (i : Fin M) :
    let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
    Real.sigmoid (score q r e o i - Real.log B0 + Real.log t) =
      t * weight q r e o i / (B0 + t * weight q r e o i) := by
  let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
  have hB0 : 0 < B0 := by
    apply div_pos <;> exact_mod_cast (by omega : 0 < _)
  have hw := ((finite_support_bayes (s := s) hq hqm hr hr1 ha ha1 e).2.2.2.1 o).2.1 i
  have hexp : Real.exp (score q r e o i - Real.log B0 + Real.log t) =
      t * weight q r e o i / B0 := by
    rw [Real.exp_add, Real.exp_sub, Real.exp_log hB0, Real.exp_log ht, ← hw.2]
    ring
  dsimp only
  rw [Real.sigmoid_def, Real.exp_neg, hexp]
  change (1 + (t * weight q r e o i / B0)⁻¹)⁻¹ =
    t * weight q r e o i / (B0 + t * weight q r e o i)
  have hden : B0 + t * weight q r e o i ≠ 0 := ne_of_gt (add_pos hB0 (mul_pos ht hw.1))
  field_simp [ne_of_gt ht, ne_of_gt hw.1, ne_of_gt hB0, hden]
  <;> try ring
  rw [← add_mul, mul_inv_cancel₀ hden]

/-- The original calibrated Bernoulli parameters, with their original common
multiplicative parameter, use exactly the same full-row four-cell equation. -/
private theorem native_original_calibration_identification {M q s : ℕ} (S : Support M q) (r : ℝ)
    (e : Experiment) (o : Obs M s e) (k l : ℕ)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (t : ℝ) (ht : 0 < t) :
    let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
    let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
      (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
    let x := z0 - Real.log B0 + Real.log t
    let C : Fin 4 → ℝ := fun j => (nativeCalibrationCells S e o k l j).card
    let outside : {i : Fin M // nativeRowCell S e o k l i = none} → ℝ :=
      fun i => score q r e o i.val - z0
    (∑ i : Fin M, t * weight q r e o i / (B0 + t * weight q r e o i)) =
      calibratedMean outside r (compensation M q r)
        (C 0 + C 1 + C 2 + C 3) (C 0 + C 2) (C 0 + C 1) (C 0) x := by
  dsimp only
  rw [← native_full_calibration_sum]
  apply sum_congr rfl
  intro i _
  rw [← native_calibrated_row_parameter r e o hq hqm hr hr1 ha ha1 t ht i]
  congr 1
  ring

/-- The original group-zero posterior center and auxiliary Bernoulli center
both use all rows of the same count cell, including background rows. -/
theorem native_group_zero_centers {M q s : ℕ} (r : ℝ)
    (e : Experiment) (o : Obs M s e) (k l : ℕ)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (t : ℝ) (ht : 0 < t) (i0 : Fin M)
    (hi0 : count e o i0 1 = k ∧ count e o i0 (-1) = l) :
    let All : Support M M := ⟨univ, by simp⟩
    let G := nativeCalibrationCells All e o k l 0
    let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
    let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
      (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
    (∑ i ∈ G, inclusion q r e o i) = (G.card : ℝ) * inclusion q r e o i0 ∧
    (∑ i ∈ G, t * weight q r e o i / (B0 + t * weight q r e o i)) =
      (G.card : ℝ) * Real.sigmoid (z0 - Real.log B0 + Real.log t) := by
  classical
  dsimp only
  let All : Support M M := ⟨univ, by simp⟩
  let G := nativeCalibrationCells All e o k l 0
  have hc (i : Fin M) (hi : i ∈ G) :
      count e o i 1 = k ∧ count e o i (-1) = l := by
    have h := (native_row_cell_iff All e o k l i 0).mp (mem_filter.mp hi).2
    simpa using h.2
  have hw (i : Fin M) (hi : i ∈ G) : weight q r e o i = weight q r e o i0 := by
    simp only [weight, (hc i hi).1, (hc i hi).2, hi0.1, hi0.2]
  have ho := ((finite_support_bayes (s := s) hq hqm hr hr1 ha ha1 e).2.2.2.1 o).2.2.2.2
  constructor
  · calc
      _ = ∑ _i ∈ G, inclusion q r e o i0 := by
        apply sum_congr rfl
        intro i hi
        exact le_antisymm ((ho i i0).mpr (le_of_eq (hw i hi)))
          ((ho i0 i).mpr (le_of_eq (hw i hi).symm))
      _ = _ := by simp only [sum_const, nsmul_eq_mul]; rfl
  · calc
      _ = ∑ _i ∈ G, Real.sigmoid
          ((k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
            (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r)) -
              Real.log (((M - q : ℕ) : ℝ) / (q : ℝ)) + Real.log t) := by
        apply sum_congr rfl
        intro i hi
        rw [← native_calibrated_row_parameter r e o hq hqm hr hr1 ha ha1 t ht i]
        simp only [score, (hc i hi).1, (hc i hi).2]
      _ = _ := by simp only [sum_const, nsmul_eq_mul]; rfl

/-- The full group-zero size is a fixed background count plus the native
rectangle A count on the same complete collapsed-history fiber. -/
private theorem native_group_zero_count_bridge {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) (k l : ℕ) (y : NativeSignalConditionalFiber.Fiber S e o) :
    let All : Support M M := ⟨univ, by simp⟩
    let G := nativeCalibrationCells All e y.val k l 0
    let BG := nativeCalibrationCells All e o k l 0 \ S.val
    G.card = BG.card + RectangleHypergeometricKernel.nativeRectangleACount S e o k l y := by
  classical
  let All : Support M M := ⟨univ, by simp⟩
  let G := nativeCalibrationCells All e y.val k l 0
  let BG := nativeCalibrationCells All e o k l 0 \ S.val
  have hG (v : Obs M s e) (i : Fin M) :
      i ∈ nativeCalibrationCells All e v k l 0 ↔
        count e v i 1 = k ∧ count e v i (-1) = l := by
    simp [nativeCalibrationCells, native_row_cell_iff, All]
  have hbg : G \ S.val = BG := by
    ext i
    change i ∈ nativeCalibrationCells All e y.val k l 0 \ S.val ↔
      i ∈ nativeCalibrationCells All e o k l 0 \ S.val
    simp only [Finset.mem_sdiff, hG]
    by_cases hi : i ∈ S.val
    · simp only [hi, not_true_eq_false, and_false]
    · rw [NativeSignalConditionalFiber.native_background_row_counts S e o y i hi 1,
        NativeSignalConditionalFiber.native_background_row_counts S e o y i hi (-1)]
  have hsig : (G.subtype (fun i => i ∈ S.val)).card =
      RectangleHypergeometricKernel.nativeRectangleACount S e o k l y := by
    congr 1
    ext i
    simp only [mem_subtype, G, hG, RectangleHypergeometricKernel.nativeRectangleACount,
      mem_filter, mem_univ, true_and]
  have hc := card_sdiff_add_card_inter G S.val
  rw [hbg] at hc
  have hs := card_subtype (fun i => i ∈ S.val) G
  simp only [filter_mem_eq_inter] at hs
  rw [hs] at hsig
  exact hc.symm.trans (congrArg (fun n => BG.card + n) hsig)


private theorem sigmoid_lipschitz_certificate :
    LipschitzWith (1 / 4 : NNReal) Real.sigmoid := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_sigmoid
  intro x
  rw [Real.deriv_sigmoid]
  change ‖Real.sigmoid x * (1 - Real.sigmoid x)‖ ≤ (1 / 4 : ℝ)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sigmoid_nonneg x)
    (sub_nonneg.mpr (Real.sigmoid_le_one x)))]
  nlinarith [sq_nonneg (Real.sigmoid x - 1 / 2)]

private theorem sigmoid_log_odds {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Real.sigmoid (Real.log (p / (1 - p))) = p := by
  rw [sigmoid_log (div_pos hp (sub_pos.mpr hp1))]
  field_simp [ne_of_gt (sub_pos.mpr hp1)]
  <;> ring

/-- The full original group posterior is compared with its common calibrated
center. The mean and variance premises are exactly those of the frozen
posterior-odds theorem; no auxiliary posterior replaces the original one. -/
private theorem native_group_zero_posterior_approximation :
    ∃ C : ℝ, 0 < C ∧ ∃ V0 : ℝ, 0 < V0 ∧
      ∀ (M q s : ℕ) (r : ℝ), 1 ≤ q → q < M → 0 < r → r < 1 →
        compensation M q r < 1 → ∀ (e : Experiment) (o : Obs M s e) (t : ℝ),
          0 < t → ∀ k l : ℕ,
          let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
          let p := fun i : Fin M => t * weight q r e o i / (B0 + t * weight q r e o i)
          let V := ∑ i, p i * (1 - p i)
          let All : Support M M := ⟨univ, by simp⟩
          let G := nativeCalibrationCells All e o k l 0
          let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
            (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
          (∑ i, p i) = (q : ℝ) → V0 ≤ V →
            |(∑ i ∈ G, inclusion q r e o i) -
              (G.card : ℝ) * Real.sigmoid (z0 - Real.log B0 + Real.log t)| ≤
                C * (G.card : ℝ) / V := by
  classical
  obtain ⟨C, hC, V0, hV0, hpost⟩ :=
    D5.S3.Estimation.SequentialDecisionRisk.UniformPosteriorOdds.result
  refine ⟨C / 4, by positivity, V0, hV0, ?_⟩
  intro M q s r hq hqm hr hr1 ha1 e o t ht k l
  dsimp only
  let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
  let p := fun i : Fin M => t * weight q r e o i / (B0 + t * weight q r e o i)
  let V := ∑ i, p i * (1 - p i)
  let All : Support M M := ⟨univ, by simp⟩
  let G := nativeCalibrationCells All e o k l 0
  let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
    (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
  change (∑ i, p i) = (q : ℝ) → V0 ≤ V → _
  intro hmean hvar
  change |(∑ i ∈ G, inclusion q r e o i) -
    (G.card : ℝ) * Real.sigmoid (z0 - Real.log B0 + Real.log t)| ≤
      C / 4 * (G.card : ℝ) / V
  have hVp : 0 < V := hV0.trans_le hvar
  have ha : 0 ≤ compensation M q r := by unfold compensation; positivity
  by_cases hG : G.Nonempty
  · obtain ⟨i, hi⟩ := hG
    have hi0 : count e o i 1 = k ∧ count e o i (-1) = l := by
      have hi' := (native_row_cell_iff All e o k l i 0).mp (mem_filter.mp hi).2
      simpa using hi'.2
    have hcenters := native_group_zero_centers r e o k l hq hqm hr hr1 ha ha1 t ht i hi0
    change (∑ j ∈ G, inclusion q r e o j) =
      (G.card : ℝ) * inclusion q r e o i ∧ _ at hcenters
    rw [hcenters.1, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg G.card)]
    have ho := hpost M q s r hq hqm hr hr1 ha1 e o t ht hmean hvar i
    have hlog : score q r e o i - Real.log B0 + Real.log t =
        z0 - Real.log B0 + Real.log t := by
      simp only [score, hi0.1, hi0.2, z0]
    have hlip := sigmoid_lipschitz_certificate.dist_le_mul
      (Real.log (inclusion q r e o i / (1 - inclusion q r e o i)))
      (z0 - Real.log B0 + Real.log t)
    rw [Real.dist_eq, Real.dist_eq, sigmoid_log_odds ho.1 ho.2.1] at hlip
    have herrLog : |Real.log (inclusion q r e o i / (1 - inclusion q r e o i)) -
        (score q r e o i - Real.log B0 + Real.log t)| ≤ C / V := ho.2.2
    rw [hlog] at herrLog
    have herr : |inclusion q r e o i - Real.sigmoid (z0 - Real.log B0 + Real.log t)| ≤
        (1 / 4 : ℝ) * (C / V) := by
      exact hlip.trans (mul_le_mul_of_nonneg_left herrLog (by norm_num))
    calc
      _ ≤ (G.card : ℝ) * ((1 / 4 : ℝ) * (C / V)) :=
        mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg G.card)
      _ = _ := by ring
  · have he : G = ∅ := not_nonempty_iff_eq_empty.mp hG
    simp [he]


/-- Every row outside the signal rectangle retains both native counts on
one coarse environment fiber. Background rows are included. -/
private theorem native_environment_outside_counts {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) (k l : ℕ)
    (y z : NativeSignalConditionalFiber.Fiber S e o)
    (henv : RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l y =
      RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l z)
    (i : Fin M) (hi : nativeRowCell S e z.val k l i = none) :
    count e y.val i 1 = count e z.val i 1 ∧
      count e y.val i (-1) = count e z.val i (-1) ∧
      nativeRowCell S e y.val k l i = none := by
  classical
  by_cases hs : i ∈ S.val
  · let j : {i : Fin M // i ∈ S.val} := ⟨i, hs⟩
    have hn (v : NativeSignalConditionalFiber.Fiber S e o) :
        nativeRowCell S e v.val k l i = none ↔
          j ∉ RectangleHypergeometricKernel.nativeRectangleRows S e o k l v := by
      simp only [RectangleHypergeometricKernel.nativeRectangleRows, mem_filter,
        mem_univ, true_and, j]
      simp only [nativeRowCell, hs, ↓reduceIte]
      split_ifs <;> aesop
    have hz := (hn z).mp hi
    have hV := congrArg Prod.fst henv
    change RectangleHypergeometricKernel.nativeRectangleRows S e o k l y =
      RectangleHypergeometricKernel.nativeRectangleRows S e o k l z at hV
    have hy : j ∉ RectangleHypergeometricKernel.nativeRectangleRows S e o k l y := by
      rwa [hV]
    have he := congrArg (fun v => v.2.1 j) henv
    change (if j ∈ RectangleHypergeometricKernel.nativeRectangleRows S e o k l y then none
      else some (count e y.val j.val 1, count e y.val j.val (-1))) =
      (if j ∈ RectangleHypergeometricKernel.nativeRectangleRows S e o k l z then none
      else some (count e z.val j.val 1, count e z.val j.val (-1))) at he
    simp only [if_neg hy, if_neg hz, Option.some.injEq, Prod.mk.injEq, j] at he
    exact ⟨he.1, he.2, (hn y).mpr hy⟩
  · rw [NativeSignalConditionalFiber.native_background_row_counts S e o y i hs 1,
      NativeSignalConditionalFiber.native_background_row_counts S e o z i hs 1,
      NativeSignalConditionalFiber.native_background_row_counts S e o y i hs (-1),
      NativeSignalConditionalFiber.native_background_row_counts S e o z i hs (-1)]
    exact ⟨rfl, rfl, by simp [nativeRowCell, hs]⟩

/-- The original outside logits are fixed by the same numerical-margin
readout as the native hypergeometric law. -/
private theorem native_environment_outside_score {M q s : ℕ} (S : Support M q)
    (r : ℝ) (e : Experiment) (o : Obs M s e) (k l : ℕ)
    (y z : NativeSignalConditionalFiber.Fiber S e o)
    (henv : RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l y =
      RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l z)
    (i : Fin M) (hi : nativeRowCell S e z.val k l i = none) :
    score q r e y.val i = score q r e z.val i ∧
      nativeRowCell S e y.val k l i = none := by
  have h := native_environment_outside_counts S e o k l y z henv i hi
  exact ⟨by simp only [score, h.1, h.2.1], h.2.2⟩


/-- The all-row calibration on a native rectangle environment uses one
fixed outside function. Only the four cell multiplicities change. -/
private theorem native_environment_calibration_identification {M q s : ℕ}
    (S : Support M q) (r : ℝ) (e : Experiment) (o : Obs M s e) (k l : ℕ)
    (y z : NativeSignalConditionalFiber.Fiber S e o)
    (henv : RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l y =
      RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l z)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (t : ℝ) (ht : 0 < t) :
    let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
    let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
      (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
    let x := z0 - Real.log B0 + Real.log t
    let C : Fin 4 → ℝ := fun j => (nativeCalibrationCells S e y.val k l j).card
    let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ :=
      fun i => score q r e z.val i.val - z0
    (∑ i : Fin M, t * weight q r e y.val i / (B0 + t * weight q r e y.val i)) =
      calibratedMean outside r (compensation M q r)
        (C 0 + C 1 + C 2 + C 3) (C 0 + C 2) (C 0 + C 1) (C 0) x := by
  classical
  dsimp only
  rw [native_original_calibration_identification S r e y.val k l hq hqm hr hr1 ha ha1 t ht]
  unfold calibratedMean
  congr 1
  have hn (i : Fin M) : nativeRowCell S e y.val k l i = none ↔
      nativeRowCell S e z.val k l i = none :=
    ⟨fun hi => (native_environment_outside_score S r e o k l z y henv.symm i hi).2,
      fun hi => (native_environment_outside_score S r e o k l y z henv i hi).2⟩
  let E := Equiv.subtypeEquivRight hn
  apply Fintype.sum_equiv E
  intro i
  have hi := native_environment_outside_score S r e o k l z y henv.symm i.val i.property
  simp only [E, Equiv.subtypeEquivRight_apply, hi.1]

end
end D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
