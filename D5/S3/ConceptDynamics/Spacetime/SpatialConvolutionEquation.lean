/- GID: D5/S3/ConceptDynamics/Spacetime/SpatialConvolutionEquation
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/SpatialConvolutionEquation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Spatial convolution equations have principal-multiple and uniqueness criteria. -/

/-
proof_shape: bind-only; admission_basis: rule-11-upstream-wrapper.
The spatial-equation atom requires the original finitely supported integer
functions on the three-dimensional integer lattice. Mathlib's coeffAddEquiv and
coeff_mul identify the carrier and its convolution. The concrete NoZeroDivisors
instance is AddMonoidAlgebra.instNoZeroDivisorsOfUniqueSums, with UniqueSums on
Position synthesized from the integer instances. No extra domain hypothesis is
an input to the public equation theorem.

The coefficient and unit statements are companion source-identification
obligations for spatial_convolution_equation_criterion. Its equation and closure
clauses consume the frozen SpatialEquationCriterion declarations.
All declarations concern an unbounded carrier; none enumerates or certifies a
bounded instance, provides a checker, or performs a numeric reduction.
-/

import D5.S3.ConceptDynamics.Spacetime.SpatialEquationCriterion
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Data.Int.Order.Basic

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Spacetime.SpatialConvolutionEquation

open SpatialEquationCriterion

abbrev Position := Fin 3 → ℤ
abbrev SpatialRing := AddMonoidAlgebra ℤ Position

/-- The additive carrier is precisely the finitely supported integer functions. -/
noncomputable def coefficientEquiv : SpatialRing ≃+ (Position →₀ ℤ) :=
  AddMonoidAlgebra.coeffAddEquiv

/-- Multiplication is the finite convolution over pairs of positions. -/
theorem coefficient_multiplication (f g : SpatialRing) (r : Position) :
    (f * g).coeff r =
      f.coeff.sum (fun p a => g.coeff.sum (fun q b => if p + q = r then a * b else 0)) := by
  classical
  exact AddMonoidAlgebra.coeff_mul f g r

/-- The multiplicative unit is the unit point mass at the origin. -/
theorem coefficient_one : (1 : SpatialRing).coeff = Finsupp.single 0 1 := by
  rfl

/-- The spatial equation and principal-ideal closure clauses on the actual convolution ring. -/
theorem spatial_convolution_equation_criterion (f h : SpatialRing) :
    ((∃ g : SpatialRing, f * g = h) ↔ h ∈ principalMultiples f) ∧
      (f ≠ 0 → ∀ {g₁ g₂ : SpatialRing}, f * g₁ = h → f * g₂ = h → g₁ = g₂) ∧
      ((0 : SpatialRing) ∈ principalMultiples f ∧
        (∀ a b : SpatialRing, a ∈ principalMultiples f → b ∈ principalMultiples f →
          a - b ∈ principalMultiples f) ∧
        (∀ a b : SpatialRing, a ∈ principalMultiples f → a * b ∈ principalMultiples f)) ∧
      (f = 0 → ((∃ g : SpatialRing, f * g = h) ↔ h = 0) ∧
        (h = 0 → ∀ g : SpatialRing, f * g = h)) := by
  obtain ⟨hexists, hunique, hzero⟩ := spatial_equation_criterion f h
  exact ⟨hexists, hunique,
    ⟨principalMultiples_zero f, fun a b => principalMultiples_sub f a b,
      fun a b => principalMultiples_mul f a b⟩, hzero⟩

end D5.S3.ConceptDynamics.Spacetime.SpatialConvolutionEquation
