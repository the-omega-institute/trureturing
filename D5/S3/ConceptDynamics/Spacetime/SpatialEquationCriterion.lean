/- GID: D5/S3/ConceptDynamics/Spacetime/SpatialEquationCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/SpatialEquationCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Principal right multiples characterize spatial equations, with uniqueness in a domain. -/

/-
proof_shape: bind-only; admission_basis: rule-11-upstream-wrapper.
The exact core is Mathlib's mul_left_cancel₀, with mul_sub and mul_assoc
supplying the closure clauses. Proposition 28 requires those facts at the typed
principal-multiple carrier, together with its solvability equivalence and zero
factor branch. The principalMultiples_* statements are companion algebraic
clauses of that same atom; spatial_equation_criterion depends on
mem_principalMultiples_iff.
-/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Set.Lattice

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Spacetime.SpatialEquationCriterion

/- The notation fR from the source proposition is represented by the set of all
   right multiples of f. We retain it as a Set so that no quotient or division
   operation is smuggled into the statement. -/
def principalMultiples {R : Type*} [Mul R] (f : R) : Set R :=
  {h | ∃ r, f * r = h}

theorem mem_principalMultiples_iff {R : Type*} [Mul R] (f h : R) :
    h ∈ principalMultiples f ↔ ∃ r, f * r = h := by
  rfl

theorem principalMultiples_zero {R : Type*} [MulZeroClass R] (f : R) :
    (0 : R) ∈ principalMultiples f := by
  exact ⟨0, mul_zero f⟩

theorem principalMultiples_sub {R : Type*} [Ring R] (f a b : R)
    (ha : a ∈ principalMultiples f) (hb : b ∈ principalMultiples f) :
    a - b ∈ principalMultiples f := by
  rcases ha with ⟨r, rfl⟩
  rcases hb with ⟨s, rfl⟩
  exact ⟨r - s, by rw [mul_sub]⟩

theorem principalMultiples_mul {R : Type*} [Semiring R] (f a b : R)
    (ha : a ∈ principalMultiples f) :
    a * b ∈ principalMultiples f := by
  rcases ha with ⟨r, rfl⟩
  exact ⟨r * b, by rw [mul_assoc]⟩

/-- The spatial equation criterion from CSA Proposition 28.

The first conjunct is the principal-multiple membership condition. The second
conjunct records the source's uniqueness clause under the no-zero-divisor
hypothesis used by its preceding convolution proposition. -/
theorem spatial_equation_criterion {R : Type*} [Ring R] [NoZeroDivisors R]
    (f h : R) :
    ((∃ g, f * g = h) ↔ h ∈ principalMultiples f) ∧
      (f ≠ 0 → ∀ {g₁ g₂ : R}, f * g₁ = h → f * g₂ = h → g₁ = g₂) ∧
      (f = 0 → ((∃ g, f * g = h) ↔ h = 0) ∧
        (h = 0 → ∀ g : R, f * g = h)) := by
  constructor
  · exact Iff.symm (mem_principalMultiples_iff f h)
  constructor
  · intro hf g₁ g₂ hg₁ hg₂
    apply mul_left_cancel₀ hf
    exact hg₁.trans hg₂.symm
  · intro hf
    constructor
    · constructor
      · rintro ⟨g, hg⟩
        simpa [hf] using hg.symm
      · intro hh
        exact ⟨0, by simp [hf, hh]⟩
    · intro hh g
      simp [hf, hh]

end D5.S3.ConceptDynamics.Spacetime.SpatialEquationCriterion
