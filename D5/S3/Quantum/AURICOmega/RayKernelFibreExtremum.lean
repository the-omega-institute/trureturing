/- GID: D5/S3/Quantum/AURICOmega/RayKernelFibreExtremum
   generality: I
   mirror-B: D5/B/S3/Quantum/AURICOmega/RayKernelFibreExtremum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The ray kernel is the fibre maximum of the round trip and the fibre integral over pi. -/

import D5.S3.Quantum.AURICOmega.QuaternionRayKernel
import D5.S3.Quantum.AURICOmega.UnitQuaternionClosedSubgroup
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The phase circle of the unit quaternions and the ray kernel along its fibres.

The phase circle is the subgroup of unit quaternions `a + b i`. Along a right coset `x (a + b i)`
the shifted reading `2 kappa(x (a + b i), y) - 1` equals `a A - b B`, where `A` and `B` are the two
shifted readings whose squares add up to `rayKernel x y`. Its square has maximum `A ^ 2 + B ^ 2`
over the circle `a ^ 2 + b ^ 2 = 1`, and its integral over a full turn is `π (A ^ 2 + B ^ 2)`. The
round-trip reading `kappa(y, p y⁻¹ p)` of a unit quaternion `p` is the square of
`2 kappa(p, y) - 1`, so it has the same maximum along the coset. Hence the ray kernel is the
maximum of the round-trip reading over a fibre and `π⁻¹` times the integral of the squared inner
product over it. -/

open scoped InnerProductSpace Quaternion

noncomputable section

namespace D5.S3.Quantum.AURICOmega.RayKernelFibreExtremum

open D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open D5.S3.Quantum.AURICOmega.QuaternionRayKernel
open D5.S3.Quantum.AURICOmega.UnitQuaternionClosedSubgroup

/-- The right phase circle: the unit quaternions in the real span of `1` and `i`. -/
def phaseCircle : Subgroup (unitary ℍ[ℝ]) where
  carrier := {c | (c : ℍ[ℝ]).imJ = 0 ∧ (c : ℍ[ℝ]).imK = 0}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩ <;>
      simp only [Submonoid.coe_mul, Quaternion.imJ_mul, Quaternion.imK_mul, ha1, ha2, hb1, hb2,
        mul_zero, zero_mul, add_zero, sub_zero]
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨?_, ?_⟩ <;>
      simp only [← Unitary.star_eq_inv, Unitary.coe_star, Quaternion.imJ_star,
        Quaternion.imK_star, ha1, ha2, neg_zero]

/-- Right multiplication by `a + b i` mixes the inner products with `q` and with `q i`. -/
private lemma inner_mul_phase (p q : ℍ[ℝ]) (a b : ℝ) :
    ⟪p * ⟨a, b, 0, 0⟩, q⟫_ℝ = a * ⟪p, q⟫_ℝ - b * ⟪p, q * (unitI : ℍ[ℝ])⟫_ℝ := by
  have hI : ((unitI : unitary ℍ[ℝ]) : ℍ[ℝ]) = ⟨0, 1, 0, 0⟩ := rfl
  rw [inner_eq_components, inner_eq_components, inner_eq_components, hI]
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

/-- A phase is the quaternion `a + b i` of its first two components. -/
private lemma coe_eq_of_mem_phaseCircle {c : unitary ℍ[ℝ]} (hc : c ∈ phaseCircle) :
    (c : ℍ[ℝ]) = ⟨(c : ℍ[ℝ]).re, (c : ℍ[ℝ]).imI, 0, 0⟩ := by
  ext
  · rfl
  · rfl
  · exact hc.1
  · exact hc.2

/-- The shifted reading against a phase-shifted argument, in terms of the two shifted readings
that make up `rayKernel`. -/
private lemma two_kappa_mul_phase (x y c : unitary ℍ[ℝ]) (hc : c ∈ phaseCircle) :
    2 * quaternionModel.kappa (x * c) y - 1 =
      (c : ℍ[ℝ]).re * (2 * quaternionModel.kappa x y - 1) -
        (c : ℍ[ℝ]).imI * (2 * quaternionModel.kappa x (y * unitI) - 1) := by
  change 2 * ((1 + ⟪((x * c : unitary ℍ[ℝ]) : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ) / 2) - 1 =
    (c : ℍ[ℝ]).re * (2 * ((1 + ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ) / 2) - 1) -
      (c : ℍ[ℝ]).imI *
        (2 * ((1 + ⟪(x : ℍ[ℝ]), ((y * unitI : unitary ℍ[ℝ]) : ℍ[ℝ])⟫_ℝ) / 2) - 1)
  rw [Submonoid.coe_mul, Submonoid.coe_mul, coe_eq_of_mem_phaseCircle hc, inner_mul_phase]
  ring

/-- The round-trip reading of `y` through a unit quaternion `p` is the square of the shifted
reading `2 kappa(p, y) - 1`. -/
private lemma kappa_tri_self (p y : unitary ℍ[ℝ]) :
    quaternionModel.kappa y (quaternionModel.tri p y p) =
      (2 * quaternionModel.kappa p y - 1) ^ 2 := by
  have hp : ⟪(p : ℍ[ℝ]), (p : ℍ[ℝ])⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, CStarRing.norm_coe_unitary, one_pow]
  have hy : ⟪(y : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, CStarRing.norm_coe_unitary, one_pow]
  have key : ⟪(y : ℍ[ℝ]), (p : ℍ[ℝ]) * star (y : ℍ[ℝ]) * p⟫_ℝ =
      2 * ⟪(p : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ ^ 2 -
        ⟪(p : ℍ[ℝ]), (p : ℍ[ℝ])⟫_ℝ * ⟪(y : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ := by
    simp only [inner_eq_components, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
      Quaternion.imK_star]
    ring
  change (1 + ⟪(y : ℍ[ℝ]), ((p * y⁻¹ * p : unitary ℍ[ℝ]) : ℍ[ℝ])⟫_ℝ) / 2 =
    (2 * ((1 + ⟪(p : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ) / 2) - 1) ^ 2
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Unitary.star_eq_inv, Unitary.coe_star, key, hp, hy]
  ring

/-- The maximum of `(a A - b B) ^ 2` over the phases `a + b i` is `A ^ 2 + B ^ 2`. -/
private lemma isGreatest_phase (A B : ℝ) :
    IsGreatest {r | ∃ c ∈ phaseCircle, r = ((c : ℍ[ℝ]).re * A - (c : ℍ[ℝ]).imI * B) ^ 2}
      (A ^ 2 + B ^ 2) := by
  constructor
  · by_cases h0 : A ^ 2 + B ^ 2 = 0
    · refine ⟨1, one_mem _, ?_⟩
      have hA : A = 0 := by nlinarith [sq_nonneg A, sq_nonneg B]
      have hB : B = 0 := by nlinarith [sq_nonneg A, sq_nonneg B]
      rw [hA, hB]
      ring
    · set r := Real.sqrt (A ^ 2 + B ^ 2) with hr
      have hr2 : r ^ 2 = A ^ 2 + B ^ 2 := Real.sq_sqrt (by positivity)
      have hr0 : r ≠ 0 := by
        intro h
        rw [h] at hr2
        exact h0 (by rw [← hr2]; ring)
      have hab : (A / r) ^ 2 + (-B / r) ^ 2 = 1 := by
        rw [div_pow, div_pow, neg_sq, ← add_div, ← hr2]
        exact div_self (pow_ne_zero 2 hr0)
      have hmem : (⟨A / r, -B / r, 0, 0⟩ : ℍ[ℝ]) ∈ unitary ℍ[ℝ] := by
        refine mem_unitary_of_normSq ?_
        rw [Quaternion.normSq_def']
        change (A / r) ^ 2 + (-B / r) ^ 2 + 0 ^ 2 + 0 ^ 2 = 1
        linear_combination hab
      refine ⟨⟨_, hmem⟩, ⟨rfl, rfl⟩, ?_⟩
      change A ^ 2 + B ^ 2 = (A / r * A - -B / r * B) ^ 2
      rw [← hr2]
      field_simp
      rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hr2]
      ring
  · rintro _ ⟨c, hc, rfl⟩
    have hn := sq_add_sq_coe_unitary c
    rw [hc.1, hc.2] at hn
    nlinarith [sq_nonneg ((c : ℍ[ℝ]).re * B + (c : ℍ[ℝ]).imI * A)]

/-- The mean of `⟪p (cos χ + sin χ i), q⟫ ^ 2` over a full turn is half of
`⟪p, q⟫ ^ 2 + ⟪p, q i⟫ ^ 2`. -/
private lemma integral_inner_mul_phase_sq (p q : ℍ[ℝ]) :
    ∫ χ in (0 : ℝ)..(2 * Real.pi), ⟪p * ⟨Real.cos χ, Real.sin χ, 0, 0⟩, q⟫_ℝ ^ 2 =
      Real.pi * (⟪p, q⟫_ℝ ^ 2 + ⟪p, q * (unitI : ℍ[ℝ])⟫_ℝ ^ 2) := by
  set A := ⟪p, q⟫_ℝ
  set B := ⟪p, q * (unitI : ℍ[ℝ])⟫_ℝ
  have hf : ∀ χ : ℝ, ⟪p * ⟨Real.cos χ, Real.sin χ, 0, 0⟩, q⟫_ℝ ^ 2 =
      A ^ 2 * Real.cos χ ^ 2 + B ^ 2 * Real.sin χ ^ 2 -
        2 * A * B * (Real.sin χ * Real.cos χ) := by
    intro χ
    rw [inner_mul_phase]
    ring
  simp only [hf]
  have h1 : IntervalIntegrable (fun χ : ℝ => A ^ 2 * Real.cos χ ^ 2) MeasureTheory.volume 0
      (2 * Real.pi) :=
    (by fun_prop : Continuous fun χ : ℝ => A ^ 2 * Real.cos χ ^ 2).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun χ : ℝ => B ^ 2 * Real.sin χ ^ 2) MeasureTheory.volume 0
      (2 * Real.pi) :=
    (by fun_prop : Continuous fun χ : ℝ => B ^ 2 * Real.sin χ ^ 2).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun χ : ℝ => 2 * A * B * (Real.sin χ * Real.cos χ))
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (by fun_prop : Continuous fun χ : ℝ => 2 * A * B * (Real.sin χ * Real.cos χ)).intervalIntegrable
      _ _
  rw [intervalIntegral.integral_sub (h1.add h2) h3, intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_cos_sq, integral_sin_sq, integral_sin_mul_cos₁]
  simp only [Real.sin_two_pi, Real.cos_two_pi, Real.sin_zero, Real.cos_zero]
  ring

/-- Along the right phase circle of the first argument, the round-trip reading
`kappa(y, (x c) y⁻¹ (x c))` and the squared shifted reading `(2 kappa(x c, y) - 1) ^ 2` both attain
`rayKernel x y` as their maximum, and `π⁻¹` times the integral of `⟪x (cos χ + sin χ i), y⟫ ^ 2`
over a full turn is `rayKernel x y`. -/
theorem rayKernel_isGreatest_and_integral (x y : unitary ℍ[ℝ]) :
    IsGreatest {r | ∃ c ∈ phaseCircle,
        r = quaternionModel.kappa y (quaternionModel.tri (x * c) y (x * c))} (rayKernel x y) ∧
      IsGreatest {r | ∃ c ∈ phaseCircle,
        r = (2 * quaternionModel.kappa (x * c) y - 1) ^ 2} (rayKernel x y) ∧
      ∫ χ in (0 : ℝ)..(2 * Real.pi),
          ⟪(x : ℍ[ℝ]) * ⟨Real.cos χ, Real.sin χ, 0, 0⟩, (y : ℍ[ℝ])⟫_ℝ ^ 2 =
        Real.pi * rayKernel x y := by
  have h2 : {r | ∃ c ∈ phaseCircle, r = (2 * quaternionModel.kappa (x * c) y - 1) ^ 2} =
      {r | ∃ c ∈ phaseCircle, r = ((c : ℍ[ℝ]).re * (2 * quaternionModel.kappa x y - 1) -
        (c : ℍ[ℝ]).imI * (2 * quaternionModel.kappa x (y * unitI) - 1)) ^ 2} := by
    ext r
    constructor <;> rintro ⟨c, hc, rfl⟩ <;> exact ⟨c, hc, by rw [two_kappa_mul_phase x y c hc]⟩
  have h1 : {r | ∃ c ∈ phaseCircle,
        r = quaternionModel.kappa y (quaternionModel.tri (x * c) y (x * c))} =
      {r | ∃ c ∈ phaseCircle, r = (2 * quaternionModel.kappa (x * c) y - 1) ^ 2} := by
    ext r
    constructor <;> rintro ⟨c, hc, rfl⟩ <;> exact ⟨c, hc, by rw [kappa_tri_self]⟩
  have hG := isGreatest_phase (2 * quaternionModel.kappa x y - 1)
    (2 * quaternionModel.kappa x (y * unitI) - 1)
  refine ⟨h1 ▸ h2 ▸ hG, h2 ▸ hG, ?_⟩
  rw [integral_inner_mul_phase_sq, rayKernel_eq_inner]

end D5.S3.Quantum.AURICOmega.RayKernelFibreExtremum

