/- GID: D5/S3/Estimation/TimeArrow/SharedRectangleCalibration
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/SharedRectangleCalibration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Four adjacent score cells share one moving logistic calibration. -/

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
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

theorem sigmoid_shift_deriv (a x : ℝ) :
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

theorem exists_calibration_root {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U q t : ℝ) (hq : 0 < q)
    (hqM : q < (Fintype.card ι : ℝ) + N)
    :
    ∃ x, calibratedMean outside r ε N R U t x = q := by
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
  exact ⟨x,hx⟩

theorem unique_shared_root {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U q t : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hqM : q < (Fintype.card ι : ℝ) + N)
    (hc : ∀ j, 0 ≤ cellCounts N R U t j) :
    ∃! x, calibratedMean outside r ε N R U t x = q := by
  obtain ⟨x,hx⟩ := exists_calibration_root outside r ε N R U q t hq hqM
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

theorem native_row_cell_iff {M q s : ℕ} (S : Support M q) (e : Experiment)
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

/-- The original four signal-cell sizes give exactly the two numerical
margins and A-count in the native conditional readout. -/
theorem native_calibration_counts_margins {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) (k l : ℕ)
    (y : NativeSignalConditionalFiber.Fiber S e o) :
    let V := RectangleHypergeometricKernel.nativeRectangleRows S e o k l y
    let C := fun j => (nativeCalibrationCells S e y.val k l j).card
    V.card = C 0 + C 1 + C 2 + C 3 ∧
      (V.filter fun i => count e y.val i.val 1 = k).card = C 0 + C 2 ∧
      (V.filter fun i => count e y.val i.val (-1) = l).card = C 0 + C 1 ∧
      RectangleHypergeometricKernel.nativeRectangleACount S e o k l y = C 0 := by
  classical
  dsimp only
  have hc (J : Finset (Fin 4)) :
      ((univ : Finset {i : Fin M // i ∈ S.val}).filter fun i =>
        ∃ j ∈ J, nativeRowCell S e y.val k l i.val = some j).card =
      ∑ j ∈ J, (nativeCalibrationCells S e y.val k l j).card := by
    let P := (univ : Finset (Fin M)).filter fun i =>
      ∃ j ∈ J, nativeRowCell S e y.val k l i = some j
    have hs : ∀ i ∈ P, i ∈ S.val := by
      intro i hi
      obtain ⟨j, _, hj⟩ := (mem_filter.mp hi).2
      exact ((native_row_cell_iff S e y.val k l i j).mp hj).1
    have he : (univ.filter fun i : {i : Fin M // i ∈ S.val} =>
        ∃ j ∈ J, nativeRowCell S e y.val k l i.val = some j) =
          P.subtype (fun i => i ∈ S.val) := by
      ext i
      simp [P]
    rw [he, card_subtype, filter_true_of_mem hs]
    have hf := sum_card_fiberwise_eq_card_filter (univ : Finset (Fin M))
      (J.image (some : Fin 4 → Option (Fin 4))) (nativeRowCell S e y.val k l)
    rw [sum_image (fun _ _ _ _ h => Option.some.inj h)] at hf
    simpa [P, nativeCalibrationCells, eq_comm] using hf.symm
  have hN : RectangleHypergeometricKernel.nativeRectangleRows S e o k l y =
      univ.filter (fun i : {i : Fin M // i ∈ S.val} =>
        ∃ j ∈ (univ : Finset (Fin 4)), nativeRowCell S e y.val k l i.val = some j) := by
    ext i
    simp [RectangleHypergeometricKernel.nativeRectangleRows, native_row_cell_iff,
      i.property, Fin.exists_fin_succ]
    omega
  have hR : (RectangleHypergeometricKernel.nativeRectangleRows S e o k l y).filter
      (fun i => count e y.val i.val 1 = k) =
      univ.filter (fun i : {i : Fin M // i ∈ S.val} =>
        ∃ j ∈ ({0, 2} : Finset (Fin 4)), nativeRowCell S e y.val k l i.val = some j) := by
    ext i
    simp [RectangleHypergeometricKernel.nativeRectangleRows, native_row_cell_iff, i.property]
    omega
  have hU : (RectangleHypergeometricKernel.nativeRectangleRows S e o k l y).filter
      (fun i => count e y.val i.val (-1) = l) =
      univ.filter (fun i : {i : Fin M // i ∈ S.val} =>
        ∃ j ∈ ({0, 1} : Finset (Fin 4)), nativeRowCell S e y.val k l i.val = some j) := by
    ext i
    simp [RectangleHypergeometricKernel.nativeRectangleRows, native_row_cell_iff, i.property]
    omega
  have hA : (univ.filter fun i : {i : Fin M // i ∈ S.val} =>
      count e y.val i.val 1 = k ∧ count e y.val i.val (-1) = l) =
      univ.filter (fun i : {i : Fin M // i ∈ S.val} =>
        ∃ j ∈ ({0} : Finset (Fin 4)), nativeRowCell S e y.val k l i.val = some j) := by
    ext i
    simp [native_row_cell_iff, i.property]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hN, hc]
    simp [Fin.sum_univ_four, add_assoc]
  · rw [hR, hc]
    simp
  · rw [hU, hc]
    simp
  · unfold RectangleHypergeometricKernel.nativeRectangleACount
    rw [hA, hc]
    simp

private theorem sigmoid_lipschitz_certificate :
    LipschitzWith (1 / 4 : NNReal) Real.sigmoid := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_sigmoid
  intro x
  rw [Real.deriv_sigmoid]
  change ‖Real.sigmoid x * (1 - Real.sigmoid x)‖ ≤ (1 / 4 : ℝ)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sigmoid_nonneg x)
    (sub_nonneg.mpr (Real.sigmoid_le_one x)))]
  nlinarith [sq_nonneg (Real.sigmoid x - 1 / 2)]

end
end D5.S3.Estimation.TimeArrow.SharedRectangleCalibration

open scoped BigOperators Topology
open Finset Filter
open D5.S3.Estimation.TimeArrow.SharedRectangleCalibration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds
noncomputable section

private theorem sigmoid_variance_formula (x : ℝ) :
    Real.sigmoid x * (1 - Real.sigmoid x) =
      Real.exp (-x) / (1 + Real.exp (-x)) ^ 2 := by
  rw [Real.sigmoid_def]
  field_simp
  <;> ring

/-- A bounded common odds tilt controls every Bernoulli variance by the
same factors, independently of its unshifted score. -/
theorem sigmoid_variance_tilt (x h : ℝ)
    (hl : 1 / 2 ≤ Real.exp (-h)) (hu : Real.exp (-h) ≤ 2) :
    (Real.sigmoid x * (1 - Real.sigmoid x)) / 2 ≤
        Real.sigmoid (x + h) * (1 - Real.sigmoid (x + h)) ∧
      Real.sigmoid (x + h) * (1 - Real.sigmoid (x + h)) ≤
        2 * (Real.sigmoid x * (1 - Real.sigmoid x)) := by
  rw [sigmoid_variance_formula, sigmoid_variance_formula, neg_add, Real.exp_add]
  let w := Real.exp (-x)
  let z := Real.exp (-h)
  have hw : 0 < w := Real.exp_pos _
  have hz : 0 < z := Real.exp_pos _
  change 1 / 2 ≤ z at hl
  change z ≤ 2 at hu
  change w / (1 + w) ^ 2 / 2 ≤ w * z / (1 + w * z) ^ 2 ∧
    w * z / (1 + w * z) ^ 2 ≤ 2 * (w / (1 + w) ^ 2)
  have hd : 0 < (1 + w) ^ 2 := sq_pos_of_pos (by positivity)
  have he : 0 < (1 + w * z) ^ 2 := sq_pos_of_pos (by positivity)
  constructor
  · rw [div_div, div_le_div_iff₀ (mul_pos hd (by norm_num : (0 : ℝ) < 2)) he]
    have hp : 0 ≤ z * (2 - z) * w ^ 2 :=
      mul_nonneg (mul_nonneg hz.le (by linarith)) (sq_nonneg w)
    nlinarith
  · rw [← mul_div_assoc, div_le_div_iff₀ he hd]
    have hp : 0 ≤ z * (2 * z - 1) * w ^ 2 :=
      mul_nonneg (mul_nonneg hz.le (by linarith)) (sq_nonneg w)
    nlinarith

private theorem sigmoid_variance_bounds (x : ℝ) :
    0 ≤ Real.sigmoid x * (1 - Real.sigmoid x) ∧
      Real.sigmoid x * (1 - Real.sigmoid x) ≤ 1 / 4 := by
  constructor
  · exact mul_nonneg (Real.sigmoid_nonneg x) (sub_nonneg.mpr (Real.sigmoid_le_one x))
  · nlinarith [sq_nonneg (Real.sigmoid x - 1 / 2)]

/-- Changing the same rectangle histogram has a uniform effect on full
variance at a fixed root. The outside rows cancel exactly. -/
private theorem variance_histogram_displacement {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U t t0 x : ℝ) :
    |calibratedVariance outside r ε N R U t x -
      calibratedVariance outside r ε N R U t0 x| ≤ |t - t0| := by
  have hi : calibratedVariance outside r ε N R U t x -
      calibratedVariance outside r ε N R U t0 x =
      (t - t0) * (Real.sigmoid x * (1 - Real.sigmoid x) +
        Real.sigmoid (x + offsets r ε 3) * (1 - Real.sigmoid (x + offsets r ε 3)) -
        Real.sigmoid (x + offsets r ε 1) * (1 - Real.sigmoid (x + offsets r ε 1)) -
        Real.sigmoid (x + offsets r ε 2) * (1 - Real.sigmoid (x + offsets r ε 2))) := by
    simp [calibratedVariance, cellCounts, offsets, Fin.sum_univ_four]
    ring
  rw [hi, abs_mul]
  have hb : |Real.sigmoid x * (1 - Real.sigmoid x) +
        Real.sigmoid (x + offsets r ε 3) * (1 - Real.sigmoid (x + offsets r ε 3)) -
        Real.sigmoid (x + offsets r ε 1) * (1 - Real.sigmoid (x + offsets r ε 1)) -
        Real.sigmoid (x + offsets r ε 2) * (1 - Real.sigmoid (x + offsets r ε 2))| ≤ 1 := by
    apply abs_le.mpr
    have h0 := sigmoid_variance_bounds x
    have h1 := sigmoid_variance_bounds (x + offsets r ε 1)
    have h2 := sigmoid_variance_bounds (x + offsets r ε 2)
    have h3 := sigmoid_variance_bounds (x + offsets r ε 3)
    constructor <;> linarith
  exact (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans_eq (mul_one _)

/-- A bounded root tilt gives uniform full-variance comparison for every
feasible rectangle histogram, including every outside row. -/
private theorem variance_root_tilt {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U t x h : ℝ) (hc : ∀ j, 0 ≤ cellCounts N R U t j)
    (hl : 1 / 2 ≤ Real.exp (-h)) (hu : Real.exp (-h) ≤ 2) :
    calibratedVariance outside r ε N R U t x / 2 ≤
        calibratedVariance outside r ε N R U t (x + h) ∧
      calibratedVariance outside r ε N R U t (x + h) ≤
        2 * calibratedVariance outside r ε N R U t x := by
  have ho (i : ι) := sigmoid_variance_tilt (x + outside i) h hl hu
  have hi (j : Fin 4) := sigmoid_variance_tilt (x + offsets r ε j) h hl hu
  unfold calibratedVariance
  constructor
  · rw [add_div, sum_div, sum_div]
    apply add_le_add
    · apply sum_le_sum
      intro i _
      simpa only [add_assoc, add_comm, add_left_comm] using (ho i).1
    · apply sum_le_sum
      intro j _
      have hh := mul_le_mul_of_nonneg_left (hi j).1 (hc j)
      simpa only [mul_div_assoc, mul_assoc, add_assoc, add_comm, add_left_comm] using hh
  · rw [mul_add, mul_sum, mul_sum]
    apply add_le_add
    · apply sum_le_sum
      intro i _
      simpa only [add_assoc, add_comm, add_left_comm] using (ho i).2
    · apply sum_le_sum
      intro j _
      have hh := mul_le_mul_of_nonneg_left (hi j).2 (hc j)
      simpa only [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using hh

/-- A single base variance controls the entire feasible central rectangle
fiber and a fixed root box. No histogram-dependent neighborhood is used. -/
theorem central_fiber_variance_bounds {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U t t0 x h w : ℝ) (hc : ∀ j, 0 ≤ cellCounts N R U t j)
    (ht : |t - t0| ≤ w) (hl : 1 / 2 ≤ Real.exp (-h)) (hu : Real.exp (-h) ≤ 2) :
    (calibratedVariance outside r ε N R U t0 x - w) / 2 ≤
        calibratedVariance outside r ε N R U t (x + h) ∧
      calibratedVariance outside r ε N R U t (x + h) ≤
        2 * (calibratedVariance outside r ε N R U t0 x + w) := by
  have hd := (abs_le.mp ((variance_histogram_displacement outside r ε N R U t t0 x).trans ht))
  have hb := variance_root_tilt outside r ε N R U t x h hc hl hu
  constructor <;> linarith

private theorem checkerboard_abs_le_two (r ε x : ℝ) : |checkerboard r ε x| ≤ 2 := by
  unfold checkerboard
  apply abs_le.mpr
  have h0 := Real.sigmoid_nonneg x
  have h0' := Real.sigmoid_le_one x
  have h1 := Real.sigmoid_nonneg (x + offsets r ε 1)
  have h1' := Real.sigmoid_le_one (x + offsets r ε 1)
  have h2 := Real.sigmoid_nonneg (x + offsets r ε 2)
  have h2' := Real.sigmoid_le_one (x + offsets r ε 2)
  have h3 := Real.sigmoid_nonneg (x + offsets r ε 3)
  have h3' := Real.sigmoid_le_one (x + offsets r ε 3)
  constructor <;> linarith

private theorem calibration_histogram_displacement {ι : Type*} [Fintype ι]
    (outside : ι → ℝ) (r ε N R U t t0 x : ℝ) :
    |calibratedMean outside r ε N R U t x - calibratedMean outside r ε N R U t0 x| ≤
      2 * |t - t0| := by
  have hi : calibratedMean outside r ε N R U t x -
      calibratedMean outside r ε N R U t0 x = (t - t0) * checkerboard r ε x := by
    simp [calibratedMean, cellCounts, checkerboard, offsets, Fin.sum_univ_four]
    ring
  have hb := checkerboard_abs_le_two r ε x
  rw [hi, abs_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (abs_nonneg (t - t0))

/-- A positive derivative on a fixed box turns a center residual into
an explicit displacement bound for any root of the same equation. -/
theorem root_box_of_residual (F : ℝ → ℝ) (q x0 x d a b : ℝ)
    (hd : 0 < d) (ha : 0 < a) (hmono : StrictMono F)
    (hcont : ContinuousOn F (Set.Icc (x0 - d) (x0 + d)))
    (hdiff : DifferentiableOn ℝ F (interior (Set.Icc (x0 - d) (x0 + d))))
    (hlower : ∀ u ∈ interior (Set.Icc (x0 - d) (x0 + d)), a ≤ deriv F u)
    (hroot : F x = q) (hres : |F x0 - q| ≤ b) (hsmall : b ≤ a * d) :
    |x - x0| ≤ d ∧ a * |x - x0| ≤ b := by
  have hslope := (convex_Icc (x0 - d) (x0 + d)).mul_sub_le_image_sub_of_le_deriv
    hcont hdiff hlower
  have h0 : x0 ∈ Set.Icc (x0 - d) (x0 + d) := ⟨by linarith, by linarith⟩
  have hbot : x0 - d ∈ Set.Icc (x0 - d) (x0 + d) := ⟨le_rfl, by linarith⟩
  have htop : x0 + d ∈ Set.Icc (x0 - d) (x0 + d) := ⟨by linarith, le_rfl⟩
  have hres' := abs_le.mp hres
  have hb := hslope (x0 - d) hbot x0 h0 (by linarith)
  have hu := hslope x0 h0 (x0 + d) htop (by linarith)
  have hx : x ∈ Set.Icc (x0 - d) (x0 + d) := by
    constructor
    · apply hmono.le_iff_le.mp
      rw [hroot]
      nlinarith only [hb, hsmall, hres'.1, hres'.2]
    · apply hmono.le_iff_le.mp
      rw [hroot]
      nlinarith only [hu, hsmall, hres'.1, hres'.2]
  refine ⟨abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
  by_cases h : x0 ≤ x
  · have hh := hslope x0 h0 x hx h
    rw [hroot] at hh
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    linarith only [hh, hres'.1]
  · have hh := hslope x hx x0 h0 (le_of_not_ge h)
    rw [hroot] at hh
    rw [abs_of_nonpos (by linarith : x - x0 ≤ 0)]
    linarith only [hh, hres'.2]

/-- A quantitative bootstrap confines any root of a feasible central
histogram to one fixed box around the base root and bounds its displacement.
The base variance alone supplies the derivative lower bound throughout the
box; it is not a separate uniform-feedback assumption. -/
theorem shared_root_central_bootstrap {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U q t t0 x0 x w : ℝ) (hN : 0 < N)
    (hc : ∀ j, 0 ≤ cellCounts N R U t j) (ht : |t - t0| ≤ w)
    (hbase : calibratedMean outside r ε N R U t0 x0 = q)
    (hroot : calibratedMean outside r ε N R U t x = q)
    (hvar : w < calibratedVariance outside r ε N R U t0 x0)
    (hsmall : 2 * w ≤ (calibratedVariance outside r ε N R U t0 x0 - w) / 2 * Real.log 2) :
    |x - x0| ≤ Real.log 2 ∧
      |x - x0| ≤ 4 * w / (calibratedVariance outside r ε N R U t0 x0 - w) ∧
      (calibratedVariance outside r ε N R U t0 x0 - w) / 2 ≤
        calibratedVariance outside r ε N R U t x ∧
      calibratedVariance outside r ε N R U t x ≤
        2 * (calibratedVariance outside r ε N R U t0 x0 + w) := by
  let d := Real.log (2 : ℝ)
  let a := (calibratedVariance outside r ε N R U t0 x0 - w) / 2
  let F := calibratedMean outside r ε N R U t
  change F x = q at hroot
  have hd : 0 < d := Real.log_pos (by norm_num)
  have ha : 0 < a := by dsimp [a]; linarith
  have htilt (h : ℝ) (hh : |h| ≤ d) :
      1 / 2 ≤ Real.exp (-h) ∧ Real.exp (-h) ≤ 2 := by
    have hb := abs_le.mp hh
    constructor
    · calc
        1 / 2 = Real.exp (-d) := by simp [d, Real.exp_neg, Real.exp_log]
        _ ≤ Real.exp (-h) := Real.exp_le_exp.mpr (by linarith)
    · calc
        Real.exp (-h) ≤ Real.exp d := Real.exp_le_exp.mpr (by linarith)
        _ = 2 := Real.exp_log (by norm_num)
  have hlower (u : ℝ) (hu : u ∈ Set.Icc (x0 - d) (x0 + d)) :
      a ≤ calibratedVariance outside r ε N R U t u := by
    have hh : |u - x0| ≤ d := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hb := central_fiber_variance_bounds outside r ε N R U t t0 x0 (u - x0) w
      hc ht (htilt _ hh).1 (htilt _ hh).2
    simpa only [add_sub_cancel] using hb.1
  have hcont : ContinuousOn F (Set.Icc (x0 - d) (x0 + d)) := by
    exact fun u _ =>
      (D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibration_root_deriv
        outside r ε N R U t u).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ F (interior (Set.Icc (x0 - d) (x0 + d))) :=
    fun u _ => (D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibration_root_deriv outside r ε N R U t u).differentiableAt.differentiableWithinAt
  have hdisp : |F x0 - q| ≤ 2 * w := by
    have hh := calibration_histogram_displacement outside r ε N R U t t0 x0
    rw [hbase] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left ht (by norm_num))
  have hmono : StrictMono F := strictMono_of_deriv_pos fun u => by
    rw [(D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibration_root_deriv
      outside r ε N R U t u).deriv]
    exact D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibratedVariance_pos
      outside r ε N R U t u hN hc
  have hb := root_box_of_residual F q x0 x d a (2 * w) hd ha hmono hcont hdiff
    (fun u hu => by
      rw [(D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibration_root_deriv
        outside r ε N R U t u).deriv]
      exact hlower u (interior_subset hu)) hroot hdisp hsmall
  have hbox := hb.1
  have hmotion := hb.2
  have hmove : |x - x0| ≤ 4 * w /
      (calibratedVariance outside r ε N R U t0 x0 - w) := by
    apply (le_div_iff₀ (sub_pos.mpr hvar)).mpr
    dsimp [a] at hmotion
    nlinarith
  have hv := central_fiber_variance_bounds outside r ε N R U t t0 x0 (x - x0) w
    hc ht (htilt _ hbox).1 (htilt _ hbox).2
  simpa only [add_sub_cancel] using And.intro hbox (And.intro hmove hv)

/-- Quantitative feedback in a common compensated root box. Its size is
controlled by the same full variance, rather than an independent denominator. -/
theorem compensated_feedback_bounds (r ε x B D d a b X : ℝ)
    (ha : 0 < a) (haD : a ≤ D) (hDb : D ≤ b)
    (hB : 0 ≤ B) (hd : 0 ≤ d) (hneg : checkerboard r ε x ≤ -d)
    (hx : |x| ≤ X) (hbox : |x| ≤ Real.log 2) :
    B * d / (8 * b) - X / 4 ≤
      Real.sigmoid x - 1 / 2 -
        B * Real.sigmoid x * (1 - Real.sigmoid x) * checkerboard r ε x / D ∧
      Real.sigmoid x - 1 / 2 -
        B * Real.sigmoid x * (1 - Real.sigmoid x) * checkerboard r ε x / D ≤
          X / 4 + B / (2 * a) := by
  have hD : 0 < D := lt_of_lt_of_le ha haD
  have hb : 0 < b := lt_of_lt_of_le hD hDb
  have ht : 1 / 2 ≤ Real.exp (-x) ∧ Real.exp (-x) ≤ 2 := by
    have hh := abs_le.mp hbox
    constructor
    · calc
        1 / 2 = Real.exp (-Real.log (2 : ℝ)) := by simp [Real.exp_neg, Real.exp_log]
        _ ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    · calc
        Real.exp (-x) ≤ Real.exp (Real.log (2 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
        _ = 2 := Real.exp_log (by norm_num)
  have hv : 1 / 8 ≤ Real.sigmoid x * (1 - Real.sigmoid x) := by
    have hh := (sigmoid_variance_tilt 0 x ht.1 ht.2).1
    norm_num [Real.sigmoid_def] at hh
    simpa [Real.sigmoid_def] using hh
  have hvu := (sigmoid_variance_bounds x).2
  have hp := (sigmoid_variance_bounds x).1
  have hn : d ≤ -checkerboard r ε x := by linarith
  have hnu : -checkerboard r ε x ≤ 2 := by
    have hh := abs_le.mp (checkerboard_abs_le_two r ε x)
    linarith
  have hs : |Real.sigmoid x - 1 / 2| ≤ X / 4 := by
    have hh := D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_lipschitz_certificate.dist_le_mul x 0
    norm_num [Real.dist_eq, Real.sigmoid_def] at hh
    exact hh.trans (by linarith)
  have hl : B * d / (8 * b) ≤
      B * (Real.sigmoid x * (1 - Real.sigmoid x)) * (-checkerboard r ε x) / D := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 8 * b) hD).mpr
    have h1 := mul_le_mul hv hn hd hp
    have h2 := mul_le_mul_of_nonneg_left h1 hB
    have h3 := mul_le_mul_of_nonneg_left hDb (mul_nonneg hB hd)
    have h4 := mul_le_mul_of_nonneg_left h2 hb.le
    nlinarith
  have hu : B * (Real.sigmoid x * (1 - Real.sigmoid x)) * (-checkerboard r ε x) / D ≤
      B / (2 * a) := by
    apply (div_le_div_iff₀ hD (by positivity : (0 : ℝ) < 2 * a)).mpr
    have h1 := mul_le_mul hvu hnu (by linarith : 0 ≤ -checkerboard r ε x) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have h2 := mul_le_mul_of_nonneg_left h1 hB
    have h3 := mul_le_mul_of_nonneg_left haD hB
    have h4 := mul_le_mul_of_nonneg_left h2 ha.le
    nlinarith
  have he : Real.sigmoid x - 1 / 2 -
      B * Real.sigmoid x * (1 - Real.sigmoid x) * checkerboard r ε x / D =
        Real.sigmoid x - 1 / 2 +
          B * (Real.sigmoid x * (1 - Real.sigmoid x)) * (-checkerboard r ε x) / D := by ring
  rw [he]
  constructor <;> linarith [abs_le.mp hs]

/-- One rectangle-independent compensated root box works for every
outside histogram and both native experiments. -/
theorem compensated_feedback_box {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ d δ : ℝ, 0 < d ∧ 0 < δ ∧ δ ≤ Real.log 2 ∧
      ∀ ε x : ℝ, |ε| < δ → |x| < δ → checkerboard r ε x ≤ -d := by
  obtain ⟨d, hd, hh⟩ := checkerboard_negative_neighborhood hr hr1
  obtain ⟨η, hη, he⟩ := Metric.eventually_nhds_iff.mp hh
  refine ⟨d, min η (Real.log 2), hd, lt_min hη (Real.log_pos (by norm_num)), min_le_right _ _, ?_⟩
  intro ε x hε hx
  apply le_of_lt
  apply he (y := (ε, x))
  simpa only [Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff] using
    And.intro (hε.trans_le (min_le_left _ _)) (hx.trans_le (min_le_left _ _))

end
end D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds

open Filter
open scoped Topology BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance

namespace D5.S3.Estimation.TimeArrow.NativeGrowthRounding
noncomputable section
/-- Index zero corresponds to the first decimal exponent of the original sequence. -/
def decimalExponent : ℕ → ℕ
  | 0 => 1
  | n + 1 => 10 ^ (5 * decimalExponent n)
/-- The original decimal denominator. -/
def denominator (n : ℕ) : ℕ := 10 ^ decimalExponent n
/-- The original integer observation scale. -/
def scale (n : ℕ) : ℕ := denominator n ^ 3
/-- The lower-left signal cell retains the original floor. -/
def centralPositive (r : ℝ) (L : ℕ) : ℕ := ⌊((1 + r) / 2) * (L : ℝ)⌋₊
/-- The second coordinate retains the exact total count. -/
def centralNegative (r : ℝ) (L : ℕ) : ℕ := L - centralPositive r L
/-- The uncompensated score at the original lower-left cell. -/
def center (r : ℝ) (L : ℕ) : ℝ :=
  centralPositive r L * Real.log (1 + r) +
    centralNegative r L * Real.log (1 - r)
/-- Original population size, with its base-two floor. -/
def population (r β : ℝ) (L : ℕ) : ℕ :=
  2 ^ ⌊phi r * (L : ℝ) / (β * Real.log 2)⌋₊
/-- Original signal cardinality, with its final floor. -/
def signalSize (r β : ℝ) (L : ℕ) : ℕ :=
  ⌊(population r β L : ℝ) * Real.exp (-center r L)⌋₊
/-- The original A-cell logit uses the complete background population. -/
def cellLogit (r β : ℝ) (L : ℕ) : ℝ :=
  let M := population r β L
  let q := signalSize r β L
  centralPositive r L * Real.log ((1 + r) / (1 - compensation M q r)) +
    centralNegative r L * Real.log ((1 - r) / (1 + compensation M q r)) -
      Real.log (((M - q : ℕ) : ℝ) / q)
/-- Both central coordinates have a bounded rounding error. -/
theorem central_rounding (r : ℝ) (L : ℕ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    centralPositive r L ≤ L ∧
      0 ≤ ((1 + r) / 2) * (L : ℝ) - centralPositive r L ∧
      ((1 + r) / 2) * (L : ℝ) - centralPositive r L < 1 ∧
      (centralNegative r L : ℝ) = (L : ℝ) - centralPositive r L := by
  have ha : 0 ≤ ((1 + r) / 2) * (L : ℝ) := by positivity
  have hk : centralPositive r L ≤ L := by
    apply Nat.floor_le_of_le
    nlinarith [show (0 : ℝ) ≤ L from Nat.cast_nonneg L]
  refine ⟨hk, sub_nonneg.mpr (Nat.floor_le ha), ?_, ?_⟩
  · have h : ((1 + r) / 2) * (L : ℝ) <
        (⌊((1 + r) / 2) * (L : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    change ((1 + r) / 2) * (L : ℝ) - ⌊((1 + r) / 2) * (L : ℝ)⌋₊ < 1
    linarith
  · exact Nat.cast_sub hk
/-- The original score is the information rate times scale minus a bounded error. -/
theorem center_rounding (r : ℝ) (L : ℕ) (hr : 0 ≤ r) (hr1 : r < 1) :
    phi r * (L : ℝ) - Real.log ((1 + r) / (1 - r)) ≤ center r L ∧
      center r L ≤ phi r * (L : ℝ) := by
  obtain ⟨hk, hx0, hx1, hl⟩ := central_rounding r L hr hr1.le
  have hp : 0 < 1 + r := by linarith
  have hm : 0 < 1 - r := by linarith
  have hc : 0 ≤ Real.log (1 + r) - Real.log (1 - r) :=
    sub_nonneg.mpr (Real.log_le_log hm (by linarith))
  have he : center r L = phi r * (L : ℝ) -
      (((1 + r) / 2) * (L : ℝ) - centralPositive r L) *
        (Real.log (1 + r) - Real.log (1 - r)) := by
    unfold center phi
    rw [hl]
    ring
  rw [he, Real.log_div hp.ne' hm.ne']
  constructor <;> nlinarith
/-- The base-two floor costs at most one factor of two. -/
theorem population_exponential_bounds (r β : ℝ) (L : ℕ)
    (hφ : 0 ≤ phi r) (hβ : 0 < β) :
    Real.exp (phi r / β * (L : ℝ)) / 2 ≤ (population r β L : ℝ) ∧
      (population r β L : ℝ) ≤ Real.exp (phi r / β * (L : ℝ)) := by
  let t := phi r * (L : ℝ) / (β * Real.log 2)
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hm : 0 < (population r β L : ℝ) := by unfold population; positivity
  have he : Real.log (population r β L : ℝ) = (⌊t⌋₊ : ℝ) * Real.log 2 := by
    simp [population, t, Real.log_pow]
  have hlo := mul_le_mul_of_nonneg_right (Nat.floor_le ht) hlog.le
  have hhi := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one t) hlog
  have hrate : t * Real.log 2 = phi r / β * (L : ℝ) := by
    dsimp [t]
    field_simp
  rw [← he, hrate] at hlo
  have hlower : phi r / β * (L : ℝ) - Real.log 2 ≤
      Real.log (population r β L : ℝ) := by
    rw [add_mul, one_mul, ← he, hrate] at hhi
    linarith
  constructor
  · have h := Real.exp_le_exp.mpr hlower
    simpa [Real.exp_sub, Real.exp_log hm, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  · simpa only [Real.exp_log hm] using Real.exp_le_exp.mpr hlo
/-- The fixed nonzero signal amplitude gives a strictly positive information rate. -/
theorem information_rate_bounds (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    0 < phi r ∧ phi r < Real.log 2 := by
  have hp : 0 < 1 + r := by linarith
  have hm : 0 < 1 - r := by linarith
  have hstrict := Real.strictConvexOn_mul_log.2 hp.le hm.le
    (show 1 + r ≠ 1 - r by linarith) (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) + 1/2 = 1)
  have he : (1/2 : ℝ) • (1+r) + (1/2 : ℝ) • (1-r) = 1 := by
    simp only [smul_eq_mul]; ring
  rw [he] at hstrict
  dsimp only at hstrict
  simp only [Real.log_one, mul_zero, smul_eq_mul] at hstrict
  have hlp : Real.log (1+r) < Real.log 2 := Real.log_lt_log hp (by linarith)
  have hlm : Real.log (1-r) < Real.log 2 := Real.log_lt_log hm (by linarith)
  have h1 := mul_lt_mul_of_pos_left hlp hp
  have h2 := mul_lt_mul_of_pos_left hlm hm
  unfold phi
  constructor <;> nlinarith
end
end D5.S3.Estimation.TimeArrow.NativeGrowthRounding
