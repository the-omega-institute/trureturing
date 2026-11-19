/- GID: D5/S3/VertexAlgebra/Characters/OriginalOrbifoldCuspExpansion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/OriginalOrbifoldCuspExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cusp expansions of the actual Golay–Leech character and its product with Delta. -/

import D5.S3.VertexAlgebra.Characters.OriginalOrbifoldAnalyticCharacter
import D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldLowSpectrum
import D5.S3.Arith.ModularForms.IntegralDiscriminant

/-! Cusp expansions for the actual rank-24 orbifold trace and its product with `Δ`. -/

set_option autoImplicit false

noncomputable section

open Complex Filter Function
open UpperHalfPlane hiding I
open scoped Topology Manifold MatrixGroups

namespace D5.S3.VertexAlgebra.OriginalOrbifoldCuspExpansion

open OriginalOrbifoldAnalyticCharacter (character)
open TwistedGround.OriginalOrbifoldLowSpectrum (actual_leech_low_spectrum)
open D5.S3.Arith.ModularForms (discriminantCoefficient discriminantCoefficient_correct)
open ModularForm (E₄)

open private hasFPowerSeriesOnBall_update hasSum_cuspFunction_of_hasSum_punctured from
  Mathlib.NumberTheory.ModularForms.QExpansion

local notation "𝕢" => Periodic.qParam
local notation "Δ" => ModularForm.discriminant
local notation "multiplicity" => OriginalOrbifoldAnalyticCharacter.multiplicity
local notation "normalizedTrace" => (fun τ : ℍ => 𝕢 1 τ * character τ)
local notation "normalizedDelta" => (fun τ : ℍ => (𝕢 1 τ)⁻¹ * Δ τ)
local notation "weightedTrace" => (fun τ : ℍ => character τ * Δ τ)
local notation "eisensteinCube" => (fun τ : ℍ => E₄ τ ^ (3 : ℕ))

/-- Multiplying the actual shifted trace by the nome gives the unshifted multiplicity series. -/
theorem normalizedCharacter_hasSum (τ : ℍ) :
    HasSum (fun n : ℕ => (multiplicity n : ℂ) * 𝕢 1 τ ^ n) (𝕢 1 τ * character τ) := by
  have hs := (OriginalOrbifoldAnalyticCharacter.actual_leech_shifted_character τ τ.im_pos).1
  have hterm (n : ℕ) : 𝕢 1 τ * (exp (2 * Real.pi * I * τ * ((n : ℂ) - 1)) *
      (multiplicity n : ℂ)) = (multiplicity n : ℂ) * 𝕢 1 τ ^ n := by
    rw [← mul_assoc, Periodic.qParam, Complex.ofReal_one, div_one, ← exp_add, ← exp_nat_mul]
    rw [mul_comm _ (multiplicity n : ℂ)]
    congr 2
    ring
  exact (hs.of_norm.hasSum.mul_left (𝕢 1 τ)).congr_fun (fun n => (hterm n).symm)

private theorem cusp_series {f : ℍ → ℂ} {c : ℕ → ℂ}
    (hs : ∀ τ : ℍ, HasSum (fun n : ℕ => c n • 𝕢 1 τ ^ n) (f τ)) :
    HasFPowerSeriesOnBall (cuspFunction 1 f) (.ofScalars ℂ c) 0 1 := by
  have hzero : cuspFunction 1 f 0 = c 0 := by
    have h := tendsto_atImInfty_of_hasSum_qExpansion one_pos hs
    have hlim := (h.comp tendsto_comap_im_ofComplex).comp (Periodic.invQParam_tendsto one_pos)
    simpa only [cuspFunction, Periodic.cuspFunction, update_self, Function.comp_def] using
      hlim.limUnder_eq
  simpa only [← hzero, update_eq_self] using hasFPowerSeriesOnBall_update one_pos hs

private theorem qExpansion_of_cusp_series {f : ℍ → ℂ} {c : ℕ → ℂ}
    (hs : HasFPowerSeriesOnBall (cuspFunction 1 f) (.ofScalars ℂ c) 0 1) :
    qExpansion 1 f = PowerSeries.mk c := by
  have hq : HasFPowerSeriesAt (cuspFunction 1 f)
      (.ofScalars ℂ (fun n => (qExpansion 1 f).coeff n)) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm]
      using hs.analyticAt.hasFPowerSeriesAt
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mk]
  simpa only [FormalMultilinearSeries.coeff_ofScalars]
    using congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n)
      (hq.eq_formalMultilinearSeries hs.hasFPowerSeriesAt)

private theorem normalizedCharacter_hasSum_smul (τ : ℍ) :
    HasSum (fun n : ℕ => (multiplicity n : ℂ) • 𝕢 1 τ ^ n) (normalizedTrace τ) := by
  simpa only [smul_eq_mul] using normalizedCharacter_hasSum τ

/-- The normalized character extends across the cusp and has its actual multiplicity
power series on the whole open unit disk. -/
theorem normalizedCharacter_cusp_series :
    HasFPowerSeriesOnBall (cuspFunction 1 normalizedTrace)
      (.ofScalars ℂ (fun n : ℕ => (multiplicity n : ℂ))) 0 1 :=
  cusp_series normalizedCharacter_hasSum_smul

private theorem multiplicity_zero_one_two :
    multiplicity 0 = 1 ∧ multiplicity 1 = 0 ∧ multiplicity 2 = 196884 := by
  let D := ActualLeechHyperbolic.leechData
  let hD := ActualLeechHyperbolic.leech_spec
  let L₀ := TwistedGround.OriginalOrbifoldConformal.L D hD.2.1 hD.2.2.1 0
  let rankAt (z : ℂ) := Module.finrank ℂ (L₀.eigenspace z)
  refine ⟨?_, ?_, ?_⟩
  · change rankAt ((0 : ℕ) : ℂ) = 1
    exact (congrArg rankAt (Nat.cast_zero (R := ℂ))).trans actual_leech_low_spectrum.2.2.2.1
  · change rankAt ((1 : ℕ) : ℂ) = 0
    exact (congrArg rankAt (Nat.cast_one (R := ℂ))).trans actual_leech_low_spectrum.2.2.2.2.1
  · simpa only [OriginalOrbifoldAnalyticCharacter.multiplicity, Nat.cast_ofNat] using
      actual_leech_low_spectrum.2.2.2.2.2.1

/-- The coefficients of the normalized trace are the actual conformal zero-mode multiplicities. -/
theorem normalizedCharacter_qExpansion :
    qExpansion 1 normalizedTrace = PowerSeries.mk (fun n : ℕ => (multiplicity n : ℂ)) :=
  qExpansion_of_cusp_series normalizedCharacter_cusp_series

/-- The first three coefficients of the normalized actual trace. -/
theorem normalizedCharacter_qExpansion_first_three :
    (qExpansion 1 normalizedTrace).coeff 0 = 1 ∧
    (qExpansion 1 normalizedTrace).coeff 1 = 0 ∧
    (qExpansion 1 normalizedTrace).coeff 2 = 196884 := by
  rw [normalizedCharacter_qExpansion]
  simp [multiplicity_zero_one_two.1, multiplicity_zero_one_two.2.1,
    multiplicity_zero_one_two.2.2]

private theorem mdifferentiable_qParam_one : MDiff (fun τ : ℍ => 𝕢 1 τ) :=
  Periodic.differentiable_qParam.mdifferentiable.comp mdifferentiable_coe

/-- The actual shifted character is holomorphic on the upper half-plane. -/
theorem character_holomorphic : MDiff (fun τ : ℍ => character τ) := by
  have hcomp : (fun τ : ℍ => character τ) =
      fun τ : ℍ => cuspFunction 1 normalizedTrace (𝕢 1 τ) / 𝕢 1 τ := by
    funext τ
    have hq : 𝕢 1 τ ≠ 0 := Periodic.qParam_ne_zero _
    have hc := hasSum_cuspFunction_of_hasSum_punctured one_pos
      normalizedCharacter_hasSum_smul (Periodic.norm_qParam_lt_one one_pos τ.im_pos) hq
    have he : cuspFunction 1 normalizedTrace (𝕢 1 τ) = 𝕢 1 τ * character τ :=
      hc.unique (normalizedCharacter_hasSum_smul τ)
    rw [he]
    field_simp
  rw [hcomp]
  intro τ
  have hq : 𝕢 1 τ ∈ Metric.eball (0 : ℂ) 1 := by
    simpa [← ENNReal.coe_one, Metric.eball_coe] using τ.norm_qParam_lt_one 1
  exact ((normalizedCharacter_cusp_series.analyticAt_of_mem hq).differentiableAt
    |>.mdifferentiableAt.comp τ (mdifferentiable_qParam_one τ)).div
      (mdifferentiable_qParam_one τ) (Periodic.qParam_ne_zero _)

private theorem discriminant_hasSum_shifted (τ : ℍ) :
    HasSum (fun n : ℕ => (discriminantCoefficient (n + 1) : ℂ) • 𝕢 1 τ ^ n)
      (normalizedDelta τ) := by
  have hs := ModularForm.hasSum_qExpansion CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL τ
  have hzero : (qExpansion 1 CuspForm.discriminant).coeff 0 = 0 :=
    CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos one_mem_strictPeriods_SL
  have htail := (hasSum_nat_add_iff' 1).mpr hs
  simp only [Finset.sum_range_one, hzero, zero_mul, sub_zero] at htail
  have hq : 𝕢 1 τ ≠ 0 := Periodic.qParam_ne_zero _
  apply (htail.mul_left (𝕢 1 τ)⁻¹).congr_fun
  intro n
  change _ = (𝕢 1 τ)⁻¹ * ((qExpansion 1 Δ).coeff (n + 1) * 𝕢 1 τ ^ (n + 1))
  rw [discriminantCoefficient_correct, smul_eq_mul, pow_succ]
  symm
  calc
    _ = ((𝕢 1 τ)⁻¹ * 𝕢 1 τ) *
        ((discriminantCoefficient (n + 1) : ℂ) * 𝕢 1 τ ^ n) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hq, one_mul]

private theorem discriminant_cusp_series :
    HasFPowerSeriesOnBall (cuspFunction 1 normalizedDelta)
      (.ofScalars ℂ (fun n : ℕ => (discriminantCoefficient (n + 1) : ℂ))) 0 1 :=
  cusp_series discriminant_hasSum_shifted

private theorem normalizedDelta_qExpansion :
    qExpansion 1 normalizedDelta =
      PowerSeries.mk (fun n : ℕ => (discriminantCoefficient (n + 1) : ℂ)) :=
  qExpansion_of_cusp_series discriminant_cusp_series

private theorem weightedTrace_eq : weightedTrace = normalizedTrace * normalizedDelta := by
  funext τ
  simp only [Pi.mul_apply]
  have hq : 𝕢 1 τ ≠ 0 := Periodic.qParam_ne_zero _
  field_simp

/-- The weight-shifted character is holomorphic on the upper half-plane. -/
theorem weightedCharacter_holomorphic : MDiff weightedTrace :=
  character_holomorphic.mul (ModularFormClass.holo CuspForm.discriminant)

/-- The weight-shifted trace tends to one at the cusp. -/
theorem weightedCharacter_tendsto : Tendsto weightedTrace atImInfty (𝓝 1) := by
  have h := (tendsto_atImInfty_of_hasSum_qExpansion one_pos
    normalizedCharacter_hasSum_smul).mul
      (tendsto_atImInfty_of_hasSum_qExpansion one_pos discriminant_hasSum_shifted)
  have hd : discriminantCoefficient 1 = 1 := by decide +kernel
  have hlim : Tendsto (fun τ : ℍ => normalizedTrace τ * normalizedDelta τ) atImInfty (𝓝 1) := by
    simpa only [multiplicity_zero_one_two.1, hd, Nat.cast_one, Int.cast_one, mul_one] using h
  exact hlim.congr fun τ => (congrFun weightedTrace_eq τ).symm

/-- The weight-shifted trace is bounded at infinity. -/
theorem weightedCharacter_bounded : IsBoundedAtImInfty weightedTrace :=
  weightedCharacter_tendsto.isBigO_one ℝ

private theorem weightedCharacter_cusp_analytic :
    AnalyticAt ℂ (cuspFunction 1 weightedTrace) 0 := by
  have hf := normalizedCharacter_cusp_series.analyticAt
  have hg := discriminant_cusp_series.analyticAt
  rw [weightedTrace_eq, cuspFunction_mul hf.continuousAt hg.continuousAt]
  exact hf.mul hg

/-- All coefficients of `χΔ` are obtained by convolution of the actual multiplicities
with the discriminant coefficients shifted by one. -/
theorem weightedCharacter_qExpansion :
    qExpansion 1 weightedTrace =
      PowerSeries.mk (fun n : ℕ => (multiplicity n : ℂ)) *
        PowerSeries.mk (fun n : ℕ => (discriminantCoefficient (n + 1) : ℂ)) := by
  rw [weightedTrace_eq, UpperHalfPlane.qExpansion_mul normalizedCharacter_cusp_series.analyticAt
    discriminant_cusp_series.analyticAt, normalizedCharacter_qExpansion,
    normalizedDelta_qExpansion]

/-- The first three coefficients of `χΔ` are `1, -24, 197136`. -/
theorem weightedCharacter_qExpansion_first_three :
    (qExpansion 1 weightedTrace).coeff 0 = 1 ∧
    (qExpansion 1 weightedTrace).coeff 1 = -24 ∧
    (qExpansion 1 weightedTrace).coeff 2 = 197136 := by
  have hΔ1 : discriminantCoefficient (0 + 1) = 1 := by decide +kernel
  have hΔ2 : discriminantCoefficient 2 = -24 := by decide +kernel
  have hΔ3 : discriminantCoefficient 3 = 252 := by decide +kernel
  rw [weightedCharacter_qExpansion]
  constructor
  · simp [PowerSeries.coeff_zero_eq_constantCoeff, multiplicity_zero_one_two.1, hΔ1]
  constructor
  · simp [PowerSeries.coeff_one_mul, multiplicity_zero_one_two.1,
      multiplicity_zero_one_two.2.1, hΔ2]
  · rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ, multiplicity_zero_one_two.1, multiplicity_zero_one_two.2.1,
      multiplicity_zero_one_two.2.2, hΔ1, hΔ2, hΔ3]

/-- The cusp function of the actual `χΔ` is analytic, takes the value one, and has
derivative `-24` in the nome at zero. -/
theorem weightedCharacter_cusp_first_order :
    AnalyticAt ℂ (cuspFunction 1 weightedTrace) 0 ∧
    cuspFunction 1 weightedTrace 0 = 1 ∧
    HasDerivAt (cuspFunction 1 weightedTrace) (-24) 0 := by
  have hcoeff := weightedCharacter_qExpansion_first_three
  refine ⟨weightedCharacter_cusp_analytic, ?_, ?_⟩
  · simpa [qExpansion_coeff] using hcoeff.1
  · have hd : deriv (cuspFunction 1 weightedTrace) 0 = -24 := by
      simpa [qExpansion_coeff, iteratedDeriv_one] using hcoeff.2.1
    rw [← hd]
    exact weightedCharacter_cusp_analytic.differentiableAt.hasDerivAt

private theorem eisensteinCube_cusp_analytic :
    AnalyticAt ℂ (cuspFunction 1 eisensteinCube) 0 := by
  exact ModularFormClass.analyticAt_cuspFunction_zero (E₄.pow 3) one_pos one_mem_strictPeriods_SL

/-- The difference `χΔ - E₄³` has zero constant coefficient and first coefficient `-744`. -/
theorem weightedCharacter_sub_eisensteinCube_qExpansion :
    (qExpansion 1 (weightedTrace - eisensteinCube)).coeff 0 = 0 ∧
    (qExpansion 1 (weightedTrace - eisensteinCube)).coeff 1 = -744 := by
  have h0 : PowerSeries.constantCoeff (qExpansion 1 E₄) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    exact EisensteinSeries.E_qExpansion_coeff_zero (by decide : 3 ≤ 4) ⟨2, rfl⟩
  have hc : qExpansion 1 eisensteinCube = qExpansion 1 E₄ ^ 3 :=
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₄ 3
  rw [UpperHalfPlane.qExpansion_sub weightedCharacter_cusp_analytic eisensteinCube_cusp_analytic,
    hc]
  constructor
  · rw [map_sub, weightedCharacter_qExpansion_first_three.1,
      PowerSeries.coeff_zero_eq_constantCoeff, map_pow, h0]
    norm_num
  · rw [map_sub, weightedCharacter_qExpansion_first_three.2.1, PowerSeries.coeff_one_pow, h0,
      ModularForm.E₄_qExpansion_coeff_one]
    norm_num

#print axioms normalizedCharacter_hasSum
#print axioms normalizedCharacter_cusp_series
#print axioms normalizedCharacter_qExpansion
#print axioms normalizedCharacter_qExpansion_first_three
#print axioms character_holomorphic
#print axioms weightedCharacter_holomorphic
#print axioms weightedCharacter_tendsto
#print axioms weightedCharacter_bounded
#print axioms weightedCharacter_qExpansion
#print axioms weightedCharacter_qExpansion_first_three
#print axioms weightedCharacter_cusp_first_order
#print axioms weightedCharacter_sub_eisensteinCube_qExpansion

end D5.S3.VertexAlgebra.OriginalOrbifoldCuspExpansion
