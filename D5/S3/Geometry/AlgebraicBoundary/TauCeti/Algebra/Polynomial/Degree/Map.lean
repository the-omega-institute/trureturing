/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Polynomial/Degree/Map
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Polynomial/Degree/Map
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Algebra/Polynomial/Degree/Map.lean.
Adaptation: ordinary D5 import routes; the original declarations and proofs are retained.
License: docs/reports/licenses/TauCeti-LICENSE.txt. Original copyright notices follow.
Retire each transplanted declaration when the actual pinned mathlib supplies an equivalent
statement, and replace its consumers by direct imports and applications of that pinned owner.
This adaptation contributes no independent mathematical novelty or escape credit. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Degrees of a polynomial under two coefficient maps

If two ring homomorphisms `φ` and `ψ` send exactly the same coefficients of a polynomial `p` to
zero, then `p.map φ` vanishes exactly when `p.map ψ` does, and the two have the same degree. This
is how the zero pattern of finitely many coefficients fixes the degrees of specialized
polynomials, for instance at two points of a base set on which a projection set used in
cylindrical algebraic decomposition is sign-invariant.
-/

public section

namespace Polynomial

variable {R S T : Type*} [Semiring R] [Semiring S] [Semiring T] {φ : R →+* S} {ψ : R →+* T}
  {p : R[X]}

/-- If `φ` and `ψ` send the same coefficients of `p` to zero, then `p.map φ` and `p.map ψ` have
the same degree. Only the coefficients up to `p.natDegree` need to be checked. -/
theorem degree_map_eq_of_map_coeff_eq_zero_iff
    (h : ∀ i ≤ p.natDegree, φ (p.coeff i) = 0 ↔ ψ (p.coeff i) = 0) :
    (p.map φ).degree = (p.map ψ).degree := by
  have h' (i : ℕ) : φ (p.coeff i) = 0 ↔ ψ (p.coeff i) = 0 := by
    rcases le_or_gt i p.natDegree with hi | hi
    · exact h i hi
    · simp [coeff_eq_zero_of_natDegree_lt hi]
  have key (n : WithBot ℕ) : (p.map φ).degree ≤ n ↔ (p.map ψ).degree ≤ n := by
    simp only [degree_le_iff_coeff_zero, coeff_map, h']
  exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)

/-- If `φ` and `ψ` send the same coefficients of `p` to zero, then `p.map φ` vanishes exactly
when `p.map ψ` does. Only the coefficients up to `p.natDegree` need to be checked. -/
theorem map_eq_zero_iff_of_map_coeff_eq_zero_iff
    (h : ∀ i ≤ p.natDegree, φ (p.coeff i) = 0 ↔ ψ (p.coeff i) = 0) :
    p.map φ = 0 ↔ p.map ψ = 0 := by
  rw [← degree_eq_bot, ← degree_eq_bot, degree_map_eq_of_map_coeff_eq_zero_iff h]

/-- If `φ` and `ψ` send the same coefficients of `p` to zero, then `p.map φ` and `p.map ψ` have
the same `natDegree`. Only the coefficients up to `p.natDegree` need to be checked. -/
theorem natDegree_map_eq_of_map_coeff_eq_zero_iff
    (h : ∀ i ≤ p.natDegree, φ (p.coeff i) = 0 ↔ ψ (p.coeff i) = 0) :
    (p.map φ).natDegree = (p.map ψ).natDegree :=
  natDegree_eq_of_degree_eq (degree_map_eq_of_map_coeff_eq_zero_iff h)

end Polynomial
