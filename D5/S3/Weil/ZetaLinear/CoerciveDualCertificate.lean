/- GID: D5/S3/Weil/ZetaLinear/CoerciveDualCertificate
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaLinear/CoerciveDualCertificate
   mirror-E: none(waiver:unbounded-domain-variational-certificate)
   anchors: []
   digest: Certify a constrained energy-dual norm from any trial vector and its full projected residual. -/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
A residual-certified version of the classical variational formula for the
inverse of a positive operator. The domain D need not be complete or normed,
and M need not extend to a bounded operator on H. Only the candidate-orthogonal
domain has to be coercive. No inverse, exact dual solution, finite-dimensional
cutoff, or desired readout inequality is supplied as an assumption.

For q(f)=Re <i f,M f>, a unit candidate k and v perpendicular to k, define
r=P_(k perp)(g-Mv) and C(v)=2 Re <g,i v>-q(v)+||r||^2/kappa.
Completing the actual domain energy gives, for every f perpendicular to k,
  2 Re <g,i f>-q(f) <= C(v).
A complex scalar test then proves |<g,i f>|^2 <= C(v) q(f).
The residual is in the full Hilbert space, including any omitted modes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaLinear.CoerciveDualCertificate

open scoped ComplexConjugate ComplexInnerProductSpace

variable {H D : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [AddCommGroup D] [Module ℂ D]

/-- The actual quadratic energy induced by the two domain maps. -/
def domainEnergy (ι M : D →ₗ[ℂ] H) (f : D) : ℝ := (⟪ι f, M f⟫_ℂ).re

/-- The full dual residual with a candidate-direction term removed. For a
unit candidate this is the orthogonal projection onto its complement. The
variational inequality below only needs its pairings on that complement. -/
def dualResidual (ι M : D →ₗ[ℂ] H) (k : D) (g : H) (v : D) : H :=
  (g - M v) - ⟪ι k, g - M v⟫_ℂ • ι k

/-- An explicit expression that can be enclosed from bounds on the trial
pairing, energy and full residual norm. It contains no inverse operator. -/
def dualBudget (ι M : D →ₗ[ℂ] H) (k : D) (g : H) (κ : ℝ) (v : D) : ℝ :=
  2 * (⟪g, ι v⟫_ℂ).re - domainEnergy ι M v + ‖dualResidual ι M k g v‖ ^ 2 / κ

private theorem residual_pair (ι M : D →ₗ[ℂ] H) (k v h : D) (g : H)
    (hh : ⟪ι k, ι h⟫_ℂ = 0) :
    ⟪dualResidual ι M k g v, ι h⟫_ℂ = ⟪g - M v, ι h⟫_ℂ := by
  simp [dualResidual, inner_sub_left, inner_smul_left, hh]

private theorem energy_smul (ι M : D →ₗ[ℂ] H) (c : ℂ) (f : D) :
    domainEnergy ι M (c • f) = ‖c‖ ^ 2 * domainEnergy ι M f := by
  simp only [domainEnergy, map_smul, inner_smul_left, inner_smul_right]
  change (conj c * (c * ⟪ι f, M f⟫_ℂ)).re = ‖c‖ ^ 2 * (⟪ι f, M f⟫_ℂ).re
  simp [Complex.mul_re, Complex.mul_im, Complex.sq_norm, Complex.normSq_apply]
  <;> ring

private theorem objective_difference (ι M : D →ₗ[ℂ] H)
    (hsym : ∀ x y : D, ⟪ι x, M y⟫_ℂ = ⟪M x, ι y⟫_ℂ)
    (g : H) (v f : D) :
    2 * (⟪g, ι f⟫_ℂ).re - domainEnergy ι M f =
      2 * (⟪g, ι v⟫_ℂ).re - domainEnergy ι M v +
        (2 * (⟪g - M v, ι (f - v)⟫_ℂ).re - domainEnergy ι M (f - v)) := by
  have hcross : (⟪ι f, M v⟫_ℂ).re = (⟪M v, ι f⟫_ℂ).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  have hself : (⟪M v, ι v⟫_ℂ).re = (⟪ι v, M v⟫_ℂ).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  simp only [domainEnergy, map_sub, inner_sub_left, inner_sub_right, Complex.sub_re]
  rw [hsym v f]
  linarith

/-- Every trial vector gives a global upper certificate for the constrained
variational objective. The proof retains both mixed terms and uses the
norm of the full projected residual, not a finite retained residual. -/
theorem dual_variational_upper (ι M : D →ₗ[ℂ] H) (k : D) (g : H) (κ : ℝ)
    (hκ : 0 < κ)
    (hsym : ∀ x y : D, ⟪ι x, M y⟫_ℂ = ⟪M x, ι y⟫_ℂ)
    (hcoercive : ∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
      κ * ‖ι f‖ ^ 2 ≤ domainEnergy ι M f)
    (v : D) (hv : ⟪ι k, ι v⟫_ℂ = 0)
    (f : D) (hf : ⟪ι k, ι f⟫_ℂ = 0) :
    2 * (⟪g, ι f⟫_ℂ).re - domainEnergy ι M f ≤ dualBudget ι M k g κ v := by
  have hh : ⟪ι k, ι (f - v)⟫_ℂ = 0 := by
    simp [map_sub, inner_sub_right, hf, hv]
  have hq := hcoercive (f - v) hh
  have hr := (Complex.re_le_norm (⟪dualResidual ι M k g v, ι (f - v)⟫_ℂ)).trans
    (norm_inner_le_norm (𝕜 := ℂ) _ _)
  have hyoung : 2 * (⟪dualResidual ι M k g v, ι (f - v)⟫_ℂ).re -
      domainEnergy ι M (f - v) ≤ ‖dualResidual ι M k g v‖ ^ 2 / κ := by
    apply (le_div_iff₀ hκ).mpr
    nlinarith [sq_nonneg (‖dualResidual ι M k g v‖ - κ * ‖ι (f - v)‖),
      mul_nonneg hκ.le (sub_nonneg.mpr hq),
      mul_nonneg hκ.le (sub_nonneg.mpr hr)]
  rw [residual_pair ι M k v (f - v) g hh] at hyoung
  rw [objective_difference ι M hsym g v f, dualBudget]
  linarith

/-- A full residual and a coercivity certificate yield an energy-weighted
readout bound for every candidate-orthogonal domain vector. The coefficient
is proved nonnegative. No exact dual solve is required. -/
theorem dual_energy_readout (ι M : D →ₗ[ℂ] H) (k : D) (g : H) (κ : ℝ)
    (hκ : 0 < κ)
    (hsym : ∀ x y : D, ⟪ι x, M y⟫_ℂ = ⟪M x, ι y⟫_ℂ)
    (hcoercive : ∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
      κ * ‖ι f‖ ^ 2 ≤ domainEnergy ι M f)
    (v : D) (hv : ⟪ι k, ι v⟫_ℂ = 0) :
    0 ≤ dualBudget ι M k g κ v ∧
      ∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
        ‖⟪g, ι f⟫_ℂ‖ ^ 2 ≤ dualBudget ι M k g κ v * domainEnergy ι M f := by
  have hvar := dual_variational_upper ι M k g κ hκ hsym hcoercive v hv
  have hC : 0 ≤ dualBudget ι M k g κ v := by
    simpa [domainEnergy] using hvar 0 (by simp)
  refine ⟨hC, ?_⟩
  intro f hf
  by_cases hi : ι f = 0
  · simp [hi, domainEnergy]
  have hq : 0 < domainEnergy ι M f :=
    (mul_pos hκ (sq_pos_of_pos (norm_pos_iff.mpr hi))).trans_le (hcoercive f hf)
  let q := domainEnergy ι M f
  let b := ⟪g, ι f⟫_ℂ
  have hbb : conj b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.sq_norm, Complex.normSq_apply] <;> ring
  let test := ((q⁻¹ : ℝ) : ℂ) • (conj b • f)
  have htest : ⟪ι k, ι test⟫_ℂ = 0 := by
    simp [test, map_smul, inner_smul_right, hf]
  have hbtest : (⟪g, ι test⟫_ℂ).re = q⁻¹ * ‖b‖ ^ 2 := by
    simp only [test, map_smul, inner_smul_right]
    change ((((q⁻¹ : ℝ) : ℂ) * (conj b * b))).re = _
    rw [hbb]
    simp
  have hqtest : domainEnergy ι M test = (q⁻¹) ^ 2 * ‖b‖ ^ 2 * q := by
    simp only [test, energy_smul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_conj, sq_abs]
    change (q⁻¹) ^ 2 * (‖b‖ ^ 2 * q) = (q⁻¹) ^ 2 * ‖b‖ ^ 2 * q
    ring
  have h := hvar test htest
  rw [hbtest, hqtest] at h
  have hid : 2 * (q⁻¹ * ‖b‖ ^ 2) - (q⁻¹) ^ 2 * ‖b‖ ^ 2 * q = ‖b‖ ^ 2 / q := by
    field_simp [show q ≠ 0 from ne_of_gt hq]
    <;> ring
  rw [hid] at h
  exact (div_le_iff₀ hq).mp h

/-- A zero projected residual gives the optimal energy-dual coefficient.
The proof of minimality uses the actual trial as a test. Its nonzero image
is essential; no existence of an exact dual vector is asserted. -/
theorem exact_dual_budget_optimal (ι M : D →ₗ[ℂ] H) (k : D) (g : H) (κ : ℝ)
    (hκ : 0 < κ)
    (hsym : ∀ x y : D, ⟪ι x, M y⟫_ℂ = ⟪M x, ι y⟫_ℂ)
    (hcoercive : ∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
      κ * ‖ι f‖ ^ 2 ≤ domainEnergy ι M f)
    (v : D) (hv : ⟪ι k, ι v⟫_ℂ = 0) (hne : ι v ≠ 0)
    (hr : dualResidual ι M k g v = 0) :
    dualBudget ι M k g κ v = domainEnergy ι M v ∧
      (∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
        ‖⟪g, ι f⟫_ℂ‖ ^ 2 ≤ domainEnergy ι M v * domainEnergy ι M f) ∧
      ∀ B : ℝ, (∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
        ‖⟪g, ι f⟫_ℂ‖ ^ 2 ≤ B * domainEnergy ι M f) →
        domainEnergy ι M v ≤ B := by
  have hp := residual_pair ι M k v v g hv
  rw [hr, inner_zero_left, inner_sub_left] at hp
  have heq : ⟪g, ι v⟫_ℂ = ⟪M v, ι v⟫_ℂ := sub_eq_zero.mp hp.symm
  have hre : (⟪g, ι v⟫_ℂ).re = domainEnergy ι M v := by
    rw [heq, domainEnergy]
    exact inner_re_symm (𝕜 := ℂ) _ _
  have hvalue : dualBudget ι M k g κ v = domainEnergy ι M v := by
    simp [dualBudget, hr, hre]
    <;> ring
  refine ⟨hvalue, ?_, ?_⟩
  · have hb := (dual_energy_readout ι M k g κ hκ hsym hcoercive v hv).2
    rwa [hvalue] at hb
  · intro B hB
    have hq : 0 < domainEnergy ι M v :=
      (mul_pos hκ (sq_pos_of_pos (norm_pos_iff.mpr hne))).trans_le (hcoercive v hv)
    have hlow := Complex.re_le_norm (⟪g, ι v⟫_ℂ)
    rw [hre] at hlow
    have hs := pow_le_pow_left₀ hq.le hlow 2
    have h := hB v hv
    have hmul : domainEnergy ι M v * domainEnergy ι M v ≤ B * domainEnergy ι M v := by
      nlinarith
    exact (mul_le_mul_iff_right₀ hq).mp hmul

#print axioms dual_energy_readout
#print axioms exact_dual_budget_optimal

end D5.S3.Weil.ZetaLinear.CoerciveDualCertificate
