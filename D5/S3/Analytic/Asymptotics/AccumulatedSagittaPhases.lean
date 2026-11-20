/- GID: D5/S3/Analytic/Asymptotics/AccumulatedSagittaPhases
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/AccumulatedSagittaPhases
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Accumulated versine of N equal angle steps: bounds and three limit regimes. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Accumulated versine of equal angle steps

`N` equal steps of angle `σ * (T / N) ^ α` each contribute the versine `1 - cos`. On the
unit circle the versine of `θ` is the sagitta of an arc of half-angle `θ`, which is why
the declarations are named after the sagitta. The total is squeezed between two explicit
polynomials in the step angle. For `0 < T` its limit as `N → ∞` is `0` when `1 / 2 < α`,
`σ ^ 2 * T / 2` when `α = 1 / 2`, and `+∞` when `0 < α < 1 / 2` and `σ ≠ 0`; nothing is
claimed for `α ≤ 0`.
-/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Analytic.Asymptotics.AccumulatedSagittaPhases

open Filter Topology

/-- The common angle of each of `N` steps: `σ * (T / N) ^ α`. -/
def stepAngle (σ T α : ℝ) (N : ℕ) : ℝ := σ * (T / N) ^ α

/-- The accumulated versine of `N` steps of angle `stepAngle σ T α N`. -/
def accumulatedSagitta (σ T α : ℝ) (N : ℕ) : ℝ :=
  N * (1 - Real.cos (stepAngle σ T α N))

private lemma versine_le (x : ℝ) : 1 - Real.cos x ≤ x ^ 2 / 2 := by
  linarith [Real.one_sub_sq_div_two_le_cos (x := x)]

lemma versine_ge (x : ℝ) : x ^ 2 / 2 - x ^ 4 / 24 ≤ 1 - Real.cos x := by
  have hhalf : Real.sin (x / 2) ^ 2 = 1 / 2 - Real.cos x / 2 := by
    have h := Real.sin_sq_eq_half_sub (x / 2)
    rwa [mul_div_cancel₀ x (two_ne_zero)] at h
  have hd := Real.abs_sub_sin_le (x / 2)
  have hy4 : |x / 2| * (|x / 2| ^ 3 / 6) = (x / 2) ^ 4 / 6 := by
    have h2 : |x / 2| ^ 2 = (x / 2) ^ 2 := sq_abs (x / 2)
    calc |x / 2| * (|x / 2| ^ 3 / 6) = (|x / 2| ^ 2) ^ 2 / 6 := by ring
      _ = (x / 2) ^ 4 / 6 := by rw [h2]; ring
  have hprod : x / 2 * (x / 2 - Real.sin (x / 2)) ≤ (x / 2) ^ 4 / 6 := by
    calc x / 2 * (x / 2 - Real.sin (x / 2))
        ≤ |x / 2 * (x / 2 - Real.sin (x / 2))| := le_abs_self _
      _ = |x / 2| * |x / 2 - Real.sin (x / 2)| := abs_mul _ _
      _ ≤ |x / 2| * (|x / 2| ^ 3 / 6) :=
        mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      _ = (x / 2) ^ 4 / 6 := hy4
  nlinarith [sq_nonneg (x / 2 - Real.sin (x / 2))]

private lemma step_sq {σ T α : ℝ} (hT : 0 < T) {N : ℕ} (hN : 0 < N) :
    stepAngle σ T α N ^ 2 = σ ^ 2 * T ^ (2 * α) * (N : ℝ) ^ (-(2 * α)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (T / N) ^ α = T ^ α / (N : ℝ) ^ α := Real.div_rpow hT.le hN'.le α
  have h2 : (T ^ α) ^ 2 = T ^ (2 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le]
    congr 1
    push_cast
    ring
  have h3 : ((N : ℝ) ^ α) ^ 2 = (N : ℝ) ^ (2 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN'.le]
    congr 1
    push_cast
    ring
  have h4 : (N : ℝ) ^ (-(2 * α)) = ((N : ℝ) ^ (2 * α))⁻¹ := Real.rpow_neg hN'.le _
  unfold stepAngle
  rw [h1, h4, mul_pow, div_pow, h2, h3]
  ring

private lemma nat_mul_rpow {α : ℝ} {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * (N : ℝ) ^ (-(2 * α)) = (N : ℝ) ^ (1 - 2 * α) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := Real.rpow_add hN' 1 (-(2 * α))
  rw [Real.rpow_one] at h
  rw [← h, sub_eq_add_neg]

private lemma accumulated_nonneg (σ T α : ℝ) (N : ℕ) : 0 ≤ accumulatedSagitta σ T α N :=
  mul_nonneg (Nat.cast_nonneg N) (by linarith [Real.cos_le_one (stepAngle σ T α N)])

private lemma tendsto_natCast_rpow_neg {y : ℝ} (hy : 0 < y) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (-y)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hy).comp tendsto_natCast_atTop_atTop

/-- The accumulated versine of `N` equal steps of angle `θ = σ * (T / N) ^ α` lies between
`N * (θ ^ 2 / 2 - θ ^ 4 / 24)` and `N * (θ ^ 2 / 2)`, for all real `σ`, `T`, `α` and every
natural `N`. Division by `N = 0` and real powers follow the Lean conventions; both bounds
and the accumulated value are `0` at `N = 0`. -/
theorem accumulated_sagitta_bounds (σ T α : ℝ) (N : ℕ) :
    N * (stepAngle σ T α N ^ 2 / 2 - stepAngle σ T α N ^ 4 / 24) ≤
      accumulatedSagitta σ T α N ∧
    accumulatedSagitta σ T α N ≤ N * (stepAngle σ T α N ^ 2 / 2) :=
  ⟨mul_le_mul_of_nonneg_left (versine_ge _) (Nat.cast_nonneg N),
    mul_le_mul_of_nonneg_left (versine_le _) (Nat.cast_nonneg N)⟩

/-- For `0 < T`, the accumulated versine of `N` equal steps of angle `σ * (T / N) ^ α`
tends, as `N → ∞`, to `0` when `1 / 2 < α`, to `σ ^ 2 * T / 2` when `α = 1 / 2`, and to
`+∞` when `0 < α < 1 / 2` and `σ ≠ 0`. -/
theorem accumulated_sagitta_phases (σ T α : ℝ) (hT : 0 < T) :
    (1 / 2 < α → Tendsto (accumulatedSagitta σ T α) atTop (𝓝 0)) ∧
    (α = 1 / 2 → Tendsto (accumulatedSagitta σ T α) atTop (𝓝 (σ ^ 2 * T / 2))) ∧
    (σ ≠ 0 → 0 < α → α < 1 / 2 → Tendsto (accumulatedSagitta σ T α) atTop atTop) := by
  set c : ℝ := σ ^ 2 * T ^ (2 * α) with hc
  have hc0 : 0 ≤ c := mul_nonneg (sq_nonneg σ) (Real.rpow_nonneg hT.le _)
  -- `N * θ ^ 2 = c * N ^ (1 - 2 α)` and `θ ^ 2 = c * N ^ (-(2 α))` for positive `N`.
  have hq : ∀ N : ℕ, 0 < N →
      (N : ℝ) * stepAngle σ T α N ^ 2 = c * (N : ℝ) ^ (1 - 2 * α) := by
    intro N hN
    rw [step_sq hT hN, ← nat_mul_rpow hN]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro hα
    have hlim : Tendsto (fun N : ℕ => c * (N : ℝ) ^ (1 - 2 * α) / 2) atTop (𝓝 0) := by
      have h := (tendsto_natCast_rpow_neg (y := 2 * α - 1) (by linarith)).const_mul (c / 2)
      simp only [mul_zero] at h
      refine h.congr fun N => ?_
      rw [show -(2 * α - 1) = 1 - 2 * α by ring]
      ring
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall (accumulated_nonneg σ T α)) ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    calc accumulatedSagitta σ T α N ≤ N * (stepAngle σ T α N ^ 2 / 2) :=
          (accumulated_sagitta_bounds σ T α N).2
      _ = c * (N : ℝ) ^ (1 - 2 * α) / 2 := by rw [← hq N hN]; ring
  · intro hα
    subst hα
    have hcT : c = σ ^ 2 * T := by
      rw [hc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]
    have hq' : ∀ N : ℕ, 0 < N → (N : ℝ) * stepAngle σ T (1 / 2) N ^ 2 = σ ^ 2 * T := by
      intro N hN
      rw [hq N hN, show (1 : ℝ) - 2 * (1 / 2) = 0 by norm_num, Real.rpow_zero, mul_one, hcT]
    have hlower : Tendsto
        (fun N : ℕ => σ ^ 2 * T / 2 - (σ ^ 2 * T) ^ 2 / 24 * (N : ℝ) ^ (-(1 : ℝ)))
        atTop (𝓝 (σ ^ 2 * T / 2)) := by
      have h := ((tendsto_natCast_rpow_neg (y := 1) one_pos).const_mul
        ((σ ^ 2 * T) ^ 2 / 24)).const_sub (σ ^ 2 * T / 2)
      simpa using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have hinv : (N : ℝ) ^ (-(1 : ℝ)) = (N : ℝ)⁻¹ := by
        rw [Real.rpow_neg hN'.le, Real.rpow_one]
      have hsq : stepAngle σ T (1 / 2) N ^ 2 = σ ^ 2 * T * (N : ℝ)⁻¹ := by
        have h := hq' N hN
        field_simp
        linarith
      calc σ ^ 2 * T / 2 - (σ ^ 2 * T) ^ 2 / 24 * (N : ℝ) ^ (-(1 : ℝ))
          = N * (stepAngle σ T (1 / 2) N ^ 2 / 2 - stepAngle σ T (1 / 2) N ^ 4 / 24) := by
            rw [hinv, show stepAngle σ T (1 / 2) N ^ 4 = (stepAngle σ T (1 / 2) N ^ 2) ^ 2 by ring,
              hsq]
            field_simp
        _ ≤ accumulatedSagitta σ T (1 / 2) N := (accumulated_sagitta_bounds σ T (1 / 2) N).1
    · filter_upwards [eventually_gt_atTop 0] with N hN
      calc accumulatedSagitta σ T (1 / 2) N
          ≤ N * (stepAngle σ T (1 / 2) N ^ 2 / 2) :=
            (accumulated_sagitta_bounds σ T (1 / 2) N).2
        _ = σ ^ 2 * T / 2 := by rw [← hq' N hN]; ring
  · intro hσ hα0 hα
    have hcpos : 0 < c := mul_pos (sq_pos_iff.mpr hσ) (Real.rpow_pos_of_pos hT _)
    -- the step angle squared tends to zero
    have hsmall : Tendsto (fun N : ℕ => c * (N : ℝ) ^ (-(2 * α))) atTop (𝓝 0) := by
      have h := (tendsto_natCast_rpow_neg (y := 2 * α) (by linarith)).const_mul c
      simpa using h
    have hbig : Tendsto (fun N : ℕ => c / 4 * (N : ℝ) ^ (1 - 2 * α)) atTop atTop :=
      ((tendsto_rpow_atTop (y := 1 - 2 * α) (by linarith)).comp
        tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity)
    refine tendsto_atTop_mono' atTop ?_ hbig
    filter_upwards [eventually_gt_atTop 0,
      hsmall.eventually (ge_mem_nhds (show (0 : ℝ) < 6 by norm_num))] with N hN hsix
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hsq : stepAngle σ T α N ^ 2 = c * (N : ℝ) ^ (-(2 * α)) := by
      rw [step_sq hT hN]
    have hq0 : 0 ≤ (N : ℝ) * stepAngle σ T α N ^ 2 := mul_nonneg hN'.le (sq_nonneg _)
    calc c / 4 * (N : ℝ) ^ (1 - 2 * α)
        = (N : ℝ) * stepAngle σ T α N ^ 2 / 4 := by rw [hq N hN]; ring
      _ ≤ N * (stepAngle σ T α N ^ 2 / 2 - stepAngle σ T α N ^ 4 / 24) := by
          have h6 : stepAngle σ T α N ^ 2 ≤ 6 := hsq ▸ hsix
          nlinarith [mul_nonneg hq0 (sub_nonneg.mpr h6)]
      _ ≤ accumulatedSagitta σ T α N := (accumulated_sagitta_bounds σ T α N).1

#print axioms accumulated_sagitta_bounds
#print axioms accumulated_sagitta_phases

end D5.S3.Analytic.Asymptotics.AccumulatedSagittaPhases
