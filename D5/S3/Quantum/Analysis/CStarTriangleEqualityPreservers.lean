/- GID: D5/S3/Quantum/Analysis/CStarTriangleEqualityPreservers
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/CStarTriangleEqualityPreservers
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Triangle-equality rigidity for complex C-star algebras. -/

/-
admission_basis: open-problem-resolution (#27007; Proved)
escape_witness: none
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27516
Declarations (definition rows carry no proof-shape claim):
PreservesTEABothDirections: definition; consumers: claim, claim_of_seminorm_rigidity.
ScalarMultipleOfIsometry: definition; consumers: claim, claim_of_seminorm_rigidity, scalar_isometry_of_norm_scaling, scalar_isometry_of_positive_norm_scaling, scalar_isometry_of_subsingleton.
claim: definition; consumers: claim_of_seminorm_rigidity, result.
scalar_isometry_of_positive_norm_scaling: proof_shape: bind-only; consumers: scalar_isometry_of_norm_scaling, scalar_isometry_of_subsingleton.
scalar_isometry_of_subsingleton: proof_shape: bind-only; consumers: scalar_isometry_of_norm_scaling.
scalar_isometry_of_norm_scaling: proof_shape: bind-only; consumers: claim_of_seminorm_rigidity.
claim_of_seminorm_rigidity: proof_shape: bind-only; consumers: result.
seminorm_scale_of_cross: proof_shape: bind-only; consumers: seminorm_rigidity.
seminorm_rigidity: proof_shape: content; consumers: result.
result: proof_shape: content; consumers: none.
-/

import D5.S3.Quantum.Analysis.CStarTriangleEqualityHereditary
import D5.S3.Quantum.Analysis.CStarTriangleEqualityNonunitalContinuity
import D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane
import Mathlib.Tactic.FieldSimp

namespace D5.S3.Quantum.Analysis.CStarTriangleEqualityPreservers

section
def PreservesTEABothDirections {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (T : A →ₗ[ℂ] B) : Prop :=
  ∀ a b : A, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b ↔ D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair (T a) (T b)

/-- The isometry is surjective because the source map is a linear bijection. -/
def ScalarMultipleOfIsometry {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] (T : A →ₗ[ℂ] B) : Prop :=
  ∃ (γ : ℂ) (U : A ≃ₗᵢ[ℂ] B), γ ≠ 0 ∧ ∀ a : A, T a = γ • U a

/-- Li–Tsai–Wang–Wong, arXiv:2611.06187v1, Problem 1.1, TEA clause. -/
def claim : Prop :=
  ∀ (A B : Type) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (T : A →ₗ[ℂ] B),
    Function.Bijective T →
    PreservesTEABothDirections T →
    ScalarMultipleOfIsometry T


end
section

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B]

/-- A positive norm-scaling bijection has the exact scalar-isometry representation. -/
private theorem scalar_isometry_of_positive_norm_scaling (T : A →ₗ[ℂ] B)
    (hT : Function.Bijective T) (c : ℝ) (hc : 0 < c)
    (hnorm : ∀ a, ‖T a‖ = c * ‖a‖) : ScalarMultipleOfIsometry T := by
  classical
  let S : A →ₗ[ℂ] B := (c : ℂ)⁻¹ • T
  have hcC : (c : ℂ) ≠ 0 := by exact Complex.ne_zero_of_re_pos hc
  have hS : ∀ a, ‖S a‖ = ‖a‖ := by
    intro a
    simp only [S, LinearMap.smul_apply, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hc.le, hnorm]
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  let I : A →ₗᵢ[ℂ] B := ⟨S, hS⟩
  have hsurj : Function.Surjective I := by
    intro b
    obtain ⟨a, ha⟩ := hT.2 ((c : ℂ) • b)
    refine ⟨a, ?_⟩
    change (c : ℂ)⁻¹ • T a = b
    rw [ha, inv_smul_smul₀ hcC]
  let U : A ≃ₗᵢ[ℂ] B := LinearIsometryEquiv.ofSurjective I hsurj
  refine ⟨(c : ℂ), U, hcC, ?_⟩
  intro a
  change T a = (c : ℂ) • ((c : ℂ)⁻¹ • T a)
  rw [smul_inv_smul₀ hcC]

/-- The degenerate source is included in the binding claim. -/
private theorem scalar_isometry_of_subsingleton [Subsingleton A] (T : A →ₗ[ℂ] B)
    (hT : Function.Bijective T) : ScalarMultipleOfIsometry T := by
  have hnorm : ∀ a, ‖T a‖ = (1 : ℝ) * ‖a‖ := by
    intro a
    have ha : a = 0 := Subsingleton.elim _ _
    simp [ha]
  exact scalar_isometry_of_positive_norm_scaling T hT 1 zero_lt_one hnorm

/-- The geometric rigidity obligation implies the source conclusion, with the zero case explicit. -/
private theorem scalar_isometry_of_norm_scaling (T : A →ₗ[ℂ] B)
    (hT : Function.Bijective T) (c : ℝ) (hc : 0 ≤ c)
    (hnorm : ∀ a, ‖T a‖ = c * ‖a‖) : ScalarMultipleOfIsometry T := by
  by_cases hA : Subsingleton A
  · letI := hA
    exact scalar_isometry_of_subsingleton T hT
  · have hcpos : 0 < c := by
      by_contra hh
      have hcz : c = 0 := le_antisymm (le_of_not_gt hh) hc
      have hz : ∀ a : A, a = 0 := by
        intro a
        apply hT.1
        have hn := hnorm a
        rw [hcz, zero_mul] at hn
        simpa using norm_eq_zero.mp hn
      apply hA
      exact ⟨fun a b => (hz a).trans (hz b).symm⟩
    exact scalar_isometry_of_positive_norm_scaling T hT c hcpos hnorm

end

section

/-- The stronger seminorm assertion is sufficient for the exact, unmodified source claim. -/
private theorem claim_of_seminorm_rigidity
    (hrigidity : ∀ (A : Type) [NonUnitalCStarAlgebra A] (p : Seminorm ℂ A),
      (∀ a b : A, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → p (a + b) = p a + p b) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ a : A, p a = c * ‖a‖) : claim := by
  intro A B _ _ T hT htea
  let p : Seminorm ℂ A := (normSeminorm ℂ B).comp T
  have hp : ∀ a b : A, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → p (a + b) = p a + p b := by
    intro a b hab
    change ‖T (a + b)‖ = ‖T a‖ + ‖T b‖
    rw [map_add]
    exact (htea a b).mp hab
  obtain ⟨c, hc, hn⟩ := hrigidity A p hp
  exact scalar_isometry_of_norm_scaling T hT c hc hn

end
section

/-- A common cross-scale identity determines a single nonnegative scale, including the zero space. -/
private theorem seminorm_scale_of_cross {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : Seminorm ℂ E) (hcross : ∀ a b : E, p a * ‖b‖ = p b * ‖a‖) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ a : E, p a = c * ‖a‖ := by
  classical
  cases subsingleton_or_nontrivial E with
  | inl hs =>
    letI := hs
    exact ⟨0, le_rfl, fun a => by rw [Subsingleton.elim a 0]; simp⟩
  | inr hn =>
    letI := hn
    obtain ⟨b, hb⟩ := exists_ne (0 : E)
    have hbn : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
    refine ⟨p b / ‖b‖, div_nonneg (apply_nonneg p b) (norm_nonneg b), ?_⟩
    intro a
    apply (mul_right_cancel₀ hbn)
    calc
      p a * ‖b‖ = p b * ‖a‖ := hcross a b
      _ = (p b / ‖b‖ * ‖a‖) * ‖b‖ := by field_simp

/-- Every finite complex seminorm additive on the original TEA pairs of a C*-algebra is rigid. -/
private theorem seminorm_rigidity {A : Type*} [NonUnitalCStarAlgebra A]
    (p : Seminorm ℂ A)
    (hp : ∀ a b : A, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → p (a+b) = p a + p b) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ a : A, p a = c * ‖a‖ := by
  classical
  by_cases hu : ∃ q : A, ∀ a : A, q * a = a ∧ a * q = a
  · exact D5.S3.Quantum.Analysis.CStarTriangleEqualityHereditary.seminorm_algebraically_unital_rigidity hu p hp
  · obtain ⟨C, hC⟩ := D5.S3.Quantum.Analysis.CStarTriangleEqualityNonunitalContinuity.seminorm_nonunital_lipschitz hu p hp
    exact seminorm_scale_of_cross p (D5.S3.Quantum.Analysis.CStarTriangleEqualityHereditary.seminorm_cross_scale_of_continuous p hC.continuous hp)

/-- The exact TEA clause of Li–Tsai–Wang–Wong Problem 1.1. -/
theorem result : claim := by
  apply claim_of_seminorm_rigidity
  intro A _ p hp
  exact seminorm_rigidity p hp

end

end D5.S3.Quantum.Analysis.CStarTriangleEqualityPreservers
