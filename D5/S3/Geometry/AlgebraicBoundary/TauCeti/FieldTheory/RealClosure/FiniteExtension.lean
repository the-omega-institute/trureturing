/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/FieldTheory/RealClosure/FiniteExtension
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/FieldTheory/RealClosure/FiniteExtension
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/FieldTheory/RealClosure/FiniteExtension.lean.
Adaptation: ordinary D5 import routes; the original declarations and proofs are retained.
License: docs/reports/licenses/TauCeti-LICENSE.txt. Original copyright notices follow.
Retire each transplanted declaration when the actual pinned mathlib supplies an equivalent
statement, and replace its consumers by direct imports and applications of that pinned owner.
This adaptation contributes no independent mathematical novelty or escape credit. -/

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Algebra.QuadraticAlgebra.Discriminant
import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension
import Mathlib.Algebra.Field.Equiv

/-! # Finite extensions of an abstract real closed field

Odd-degree finite extensions of a real closed field are trivial. A field of
characteristic different from two in which every element is a square has no quadratic
extension. These are the degree reductions used by the Sylow argument in `Galois.lean`.

## References

The odd-degree and quadratic-extension steps of the Artin–Schreier argument; see
Salma Kuhlmann,
[Real Algebraic Geometry, Lecture 5](https://www.math.uni-konstanz.de/algebra/WS0910/Notes05.pdf),
Theorem 2.2.
-/

public section

namespace TauCeti.RealClosure

open Polynomial Module

variable {R E : Type*} [Field R] [IsRealClosed R] [Field E] [Algebra R E]
    [FiniteDimensional R E]

/-- An odd-degree finite extension of a real closed field is trivial. -/
theorem finrank_eq_one_of_odd (h : Odd (finrank R E)) : finrank R E = 1 := by
  obtain ⟨x, hx⟩ := Field.exists_primitive_element R E
  have hdeg := (Field.primitive_element_iff_minpoly_natDegree_eq R x).mp hx
  obtain ⟨a, ha⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree (hdeg ▸ h)
  rw [← hdeg]
  exact natDegree_eq_of_degree_eq_some
    (degree_eq_one_of_irreducible_of_root (minpoly.irreducible (IsIntegral.of_finite R x)) ha)

section Quadratic

variable {K L : Type*} [Field K] [NeZero (2 : K)]

/-- A square-closed field of characteristic different from two has no quadratic extension. -/
theorem finrank_ne_two_of_forall_isSquare [Field L] [Algebra K L]
    (hsq : ∀ x : K, IsSquare x) : finrank K L ≠ 2 := by
  intro htwo
  have : Algebra.IsQuadraticExtension K L := ⟨htwo⟩
  obtain ⟨a, b, ⟨e⟩⟩ :=
    Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra (R := K) (A := L)
  exact QuadraticAlgebra.not_isField_of_isSquare_discr (hsq _)
    (e.symm.toRingEquiv.toMulEquiv.isField (Field.toIsField L))

end Quadratic

end TauCeti.RealClosure
