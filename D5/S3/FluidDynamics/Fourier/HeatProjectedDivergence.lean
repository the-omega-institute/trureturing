/- GID: D5/S3/FluidDynamics/Fourier/HeatProjectedDivergence
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Fourier/HeatProjectedDivergence
   mirror-E: none(waiver:universal-analytic-estimate)
   anchors: []
   utility: none
   digest: Full-frequency projected heat-divergence has inverse-square-root time decay. -/

import Mathlib
import D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.FluidDynamics.Fourier.HeatProjectedDivergence

open D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution

/-- The full-frequency heat-divergence operator, including the Leray projection,
acts on weighted tensor coefficients with the sharp source-compatible bound. -/
theorem heat_projected_divergence_operator (ν r : ℝ) (hν : 0 < ν) (hr : 0 < r) :
    let K := ℤ × ℤ
    let V := EuclideanSpace ℂ (Fin 2)
    let TV := EuclideanSpace ℂ (Fin 2 × Fin 2)
    let H := lp (fun _ : K => V) 2
    let G := lp (fun _ : K => TV) 2
    let ρ : K → ℝ := fun k => (k.1 : ℝ)^2 + (k.2 : ℝ)^2
    let κ : K → V := fun k => WithLp.toLp 2 (fun i => (![k.1, k.2] i : ℂ))
    let P := fun k => (ℂ ∙ κ k)ᗮ.starProjection
    ∃ L : G →L[ℂ] H,
      (∀ Z k, L Z k = Real.exp (-ν*r*ρ k) •
        (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
          ∑ j : Fin 2, κ k j * Z k (j,i))))) ∧
      (∀ Z, ‖L Z‖ ≤ (ν*r)^(-(1/2:ℝ)) * ‖Z‖) := by
  classical
  intro K V TV H G ρ κ P
  have hρ (k : K) : 0 ≤ ρ k := by dsimp [ρ]; positivity
  have hc : 0 < ν*r := mul_pos hν hr
  have hGaussian (k : K) :
      Real.sqrt (ρ k) * Real.exp (-ν*r*ρ k) ≤ (ν*r)^(-(1/2:ℝ)) := by
    have hz : 0 ≤ ν*r*ρ k := mul_nonneg hc.le (hρ k)
    have he : ν*r*ρ k ≤ Real.exp (ν*r*ρ k) :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
    have heP := Real.rpow_le_rpow hz he (by norm_num : (0:ℝ) ≤ 1/2)
    have hB : (ν*r)^(1/2:ℝ) *
        ((ρ k)^(1/2:ℝ) * Real.exp (-ν*r*ρ k)) ≤ 1 := by
      calc
        _ = (ν*r*ρ k)^(1/2:ℝ) * Real.exp (-(ν*r*ρ k)) := by
          rw [Real.mul_rpow hc.le (hρ k)]
          rw [show -ν*r*ρ k = -(ν*r*ρ k) by ring]
          ring
        _ ≤ (Real.exp (ν*r*ρ k))^(1/2:ℝ) *
            Real.exp (-(ν*r*ρ k)) :=
          mul_le_mul_of_nonneg_right heP (Real.exp_pos _).le
        _ = Real.exp (-(ν*r*ρ k)/2) := by
          rw [← Real.exp_mul, ← Real.exp_add]
          congr 1
          ring
        _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hc.le, ← one_div]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hc _)).mpr
    simpa [mul_comm] using hB
  have hcontract (k : K) (Z : TV) :
      ‖(WithLp.toLp 2 (fun i : Fin 2 => ∑ j : Fin 2, κ k j * Z (j,i)) : V)‖ ≤
        Real.sqrt (ρ k) * ‖Z‖ := by
    let row := fun i : Fin 2 =>
      (WithLp.toLp 2 (fun j : Fin 2 => Z (j,i)) : V)
    have hrow (i) : ‖∑ j : Fin 2, κ k j * Z (j,i)‖ ≤ ‖κ k‖ * ‖row i‖ := by
      simpa [V, TV, PiLp.inner_apply, κ, row, mul_comm] using
        norm_inner_le_norm (𝕜 := ℂ) (κ k) (row i)
    have hk : ‖κ k‖ ^ 2 = ρ k := by
      simp [V, EuclideanSpace.norm_sq_eq, κ, ρ, Complex.norm_intCast, sq_abs,
        Fin.sum_univ_two]
    have hrows : ∑ i : Fin 2, ‖row i‖ ^ 2 = ‖Z‖ ^ 2 := by
      simp only [TV, EuclideanSpace.norm_sq_eq, row,
        Fintype.sum_prod_type]
      exact Finset.sum_comm
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt (hρ k)]
    calc
      _ = ∑ i : Fin 2, ‖∑ j : Fin 2, κ k j * Z (j,i)‖ ^ 2 :=
        EuclideanSpace.norm_sq_eq _
      _ ≤ ∑ i : Fin 2, (‖κ k‖ * ‖row i‖) ^ 2 :=
        Finset.sum_le_sum (fun i _ =>
          pow_le_pow_left₀ (norm_nonneg _) (hrow i) 2)
      _ = _ := by simp only [mul_pow, ← Finset.mul_sum, hk, hrows]
  let Dlin (k : K) : TV →ₗ[ℂ] V :=
    { toFun := fun Z => WithLp.toLp 2 (fun i : Fin 2 =>
        ∑ j : Fin 2, κ k j * Z (j,i))
      map_add' := by
        intro Z W
        ext i
        change (∑ j : Fin 2, κ k j * (Z (j,i) + W (j,i))) =
          (∑ j : Fin 2, κ k j * Z (j,i)) +
            ∑ j : Fin 2, κ k j * W (j,i)
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro z Z
        ext i
        change (∑ j : Fin 2, κ k j * (z * Z (j,i))) =
          z * ∑ j : Fin 2, κ k j * Z (j,i)
        simp [← Finset.mul_sum, mul_left_comm] }
  let DC (k : K) : TV →L[ℂ] V :=
    (Dlin k).mkContinuous (Real.sqrt (ρ k)) (hcontract k)
  let DCp (k : K) : TV →L[ℂ] V := Complex.I • (P k).comp (DC k)
  have hDC (k : K) (Z : TV) : ‖DCp k Z‖ ≤ Real.sqrt (ρ k) * ‖Z‖ := by
    change ‖Complex.I • P k (DC k Z)‖ ≤ _
    rw [norm_smul, Complex.norm_I, one_mul]
    exact ((ℂ ∙ κ k)ᗮ.norm_starProjection_apply_le _).trans (hcontract k Z)
  let RK (k : K) : TV →L[ℂ] V := Real.exp (-ν*r*ρ k) • DCp k
  have hRK (k : K) : ‖RK k‖ ≤ (ν*r)^(-(1/2:ℝ)) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg hc.le _)
    intro Z
    change ‖(Real.exp (-ν*r*ρ k) : ℝ) • DCp k Z‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-ν*r*ρ k) * (Real.sqrt (ρ k) * ‖Z‖) :=
        mul_le_mul_of_nonneg_left (hDC k Z) (Real.exp_pos _).le
      _ ≤ (ν*r)^(-(1/2:ℝ)) * ‖Z‖ := by
        calc
          _ = (Real.sqrt (ρ k) * Real.exp (-ν*r*ρ k)) * ‖Z‖ := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (hGaussian k) (norm_nonneg _)
  let L : G →L[ℂ] H :=
    lp.mapCLM 2 RK (Real.rpow_nonneg hc.le _) hRK
  refine ⟨L, ?_, ?_⟩
  · intro Z k
    rfl
  · intro Z
    apply L.le_of_opNorm_le
    exact lp.norm_mapCLM_le 2 RK (Real.rpow_nonneg hc.le _) hRK

#print axioms heat_projected_divergence_operator

end D5.S3.FluidDynamics.Fourier.HeatProjectedDivergence
