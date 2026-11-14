/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/Polynomial/Reductum
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/Polynomial/Reductum
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/RingTheory/Polynomial/Reductum.lean.
Adaptation: ordinary D5 import routes; selected declarations retain their original proofs.
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

public import Mathlib.Algebra.Polynomial.EraseLead
public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Polynomial reducta

The reductum `p.reductum k` retains exactly the terms of `p` of degree strictly below `k`.
The finite set `p.reducta` contains the reducta at every cutoff through `p.natDegree + 1`, so it
includes both zero and `p` itself.  After any coefficient specialization, one member of this set
maps to the specialized polynomial: take the cutoff immediately above its new degree.  This is
the finite degree-case decomposition needed when polynomial degrees can drop under specialization.

The reductum is `PowerSeries.trunc` applied to `p` viewed as a power series.  Reducta also agree
with repeatedly deleting leading terms, connecting the fixed cutoffs used for specialization to
Mathlib's `eraseLead` API.

The retained source supplies the useful proof dependencies. Further exact applications,
including their assumptions and boundary cases, are developed in the owning Blueprint.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Chapters 4 and 11.
-/

public section

namespace Polynomial

open Polynomial

variable {R S : Type*} [Semiring R] [Semiring S]

/-- The part of `p` of degree strictly below `k`. -/
noncomputable def reductum (p : R[X]) (k : ℕ) : R[X] :=
  PowerSeries.trunc k (p : PowerSeries R)

/-- A reductum keeps the coefficients strictly below its cutoff and discards the rest. -/
@[simp, grind =]
theorem coeff_reductum (p : R[X]) (k i : ℕ) :
    (p.reductum k).coeff i = if i < k then p.coeff i else 0 := by
  simp [reductum, PowerSeries.coeff_trunc]

/-- The natural degree of a reductum at a positive cutoff is strictly below that cutoff. -/
theorem natDegree_reductum_lt (p : R[X]) (k : ℕ) :
    (p.reductum (k + 1)).natDegree < k + 1 := by
  exact PowerSeries.natDegree_trunc_lt (p : PowerSeries R) k

/-- A cutoff strictly above the degree does not change a polynomial. -/
theorem reductum_eq_self {p : R[X]} {k : ℕ} (h : p.natDegree < k) :
    p.reductum k = p := by
  ext i
  rw [coeff_reductum, ite_eq_left_iff]
  intro hi
  exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- Cutting off immediately above the degree returns the original polynomial, including for zero. -/
@[simp]
theorem reductum_natDegree_add_one (p : R[X]) :
    p.reductum (p.natDegree + 1) = p := by
  exact p.reductum_eq_self (Nat.lt_succ_self _)

/-- Reducta commute with coefficient maps, with no degree-preservation hypothesis. -/
@[simp]
theorem reductum_map (f : R →+* S) (p : R[X]) (k : ℕ) :
    (p.map f).reductum k = (p.reductum k).map f := by
  ext i
  simp [apply_ite f]

/-- The finite set of all reducta at cutoffs from zero through one above the degree. -/
noncomputable def reducta (p : R[X]) : Finset R[X] := by
  classical
  exact (Finset.range (p.natDegree + 2)).image p.reductum

/-- Membership in `reducta` is membership at one of its bounded cutoffs. -/
theorem mem_reducta {p q : R[X]} :
    q ∈ p.reducta ↔ ∃ k < p.natDegree + 2, p.reductum k = q := by
  classical
  simp [reducta]

/-- Every polynomial belongs to its own reducta. -/
@[simp]
theorem self_mem_reducta (p : R[X]) : p ∈ p.reducta := by
  rw [mem_reducta]
  exact ⟨p.natDegree + 1, by omega, p.reductum_natDegree_add_one⟩

/-- The reductum at every cutoff belongs to the reducta, including cutoffs past the degree. -/
@[simp]
theorem reductum_mem_reducta (p : R[X]) (k : ℕ) : p.reductum k ∈ p.reducta := by
  by_cases hk : k < p.natDegree + 2
  · exact mem_reducta.2 ⟨k, hk, rfl⟩
  · rw [p.reductum_eq_self (by omega)]
    exact p.self_mem_reducta

open scoped Classical in
/-- Coefficient maps carry all reducta exactly to the reducta of the mapped polynomial, with no
injectivity or degree-preservation hypothesis. -/
theorem reducta_map (f : R →+* S) (p : R[X]) :
    (p.map f).reducta = p.reducta.image (Polynomial.map f) := by
  classical
  have hdeg : (p.map f).natDegree ≤ p.natDegree := natDegree_map_le
  ext q
  rw [Finset.mem_image]
  constructor
  · rw [mem_reducta]
    rintro ⟨k, hk, rfl⟩
    exact ⟨p.reductum k, mem_reducta.2 ⟨k, by omega, rfl⟩, (p.reductum_map f k).symm⟩
  · rintro ⟨_, hq, rfl⟩
    obtain ⟨k, -, rfl⟩ := mem_reducta.1 hq
    rw [← reductum_map]
    by_cases hk : k < (p.map f).natDegree + 2
    · exact mem_reducta.2 ⟨k, hk, rfl⟩
    · rw [reductum_eq_self (by omega)]
      exact (p.map f).self_mem_reducta

/-- Cutting off immediately above the degree after specialization maps back to the specialized
polynomial.  This gives an explicit member of `p.reducta` witnessing
`exists_mem_reducta_map_eq`. -/
theorem map_reductum_natDegree_map_add_one (f : R →+* S) (p : R[X]) :
    (p.reductum ((p.map f).natDegree + 1)).map f = p.map f := by
  rw [← reductum_map, reductum_natDegree_add_one]

/-- Cutting off immediately above the degree after specialization gives a reductum whose own
degree is the specialized degree, so formal degree bounds taken at this reductum are the actual
degrees after specialization. -/
theorem natDegree_reductum_natDegree_map_add_one (f : R →+* S) (p : R[X]) :
    (p.reductum ((p.map f).natDegree + 1)).natDegree = (p.map f).natDegree := by
  refine Nat.le_antisymm (Nat.lt_succ_iff.mp (p.natDegree_reductum_lt _)) ?_
  conv_lhs => rw [← map_reductum_natDegree_map_add_one f p]
  exact natDegree_map_le

end Polynomial
