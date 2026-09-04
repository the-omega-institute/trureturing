/- GID: D5/S3/Observer/HiddenFlow/FiniteEditTailDiscontinuity
   generality: G
   mirror-B: D5/B/S3/Observer/HiddenFlow/FiniteEditTailDiscontinuity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonconstant Boolean tail observable on a product is continuous nowhere. -/

/- Library-search audit trail (2026-09-04):
   * Repository searches for finite-edit invariance and nowhere-continuous observables found no
     equivalent D5 declaration. The dense-orbit invariant theorem has a different carrier.
   * Pinned-Mathlib and public Loogle/LeanSearch queries found no exact theorem. Mathlib's
     `exists_finset_piecewise_mem_of_mem_nhds` supplies the finite-coordinate construction used
     below, and the discrete topology on `Bool` supplies an open singleton neighborhood.
-/

import Mathlib.Data.PNat.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order

namespace D5.S3.Observer.HiddenFlow.FiniteEditTailDiscontinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set
open scoped Topology

/-- A Boolean observable on a positive-naturally indexed product that is unchanged by every
finite coordinate edit is discontinuous at every point whenever it takes two different values. -/
theorem nonconstant_finite_edit_invariant_nowhere_continuous
    {X : ℕ+ -> Type*} [∀ n, TopologicalSpace (X n)]
    (F : (∀ n, X n) -> Bool)
    (finiteEditInvariant :
      ∀ x y, ({n : ℕ+ | x n ≠ y n} : Set ℕ+).Finite -> F x = F y)
    (nonconstant : ∃ a b, F a ≠ F b) :
    ∀ x, ¬ ContinuousAt F x := by
  intro x continuousAt
  obtain ⟨a, b, hab⟩ := nonconstant
  obtain ⟨y, hy⟩ : ∃ y, F y ≠ F x := by
    by_cases ha : F a = F x
    · exact ⟨b, fun hb => hab (ha.trans hb.symm)⟩
    · exact ⟨a, ha⟩
  have preimageNeighborhood : F ⁻¹' {F x} ∈ 𝓝 x :=
    continuousAt.preimage_mem_nhds ((isOpen_discrete {F x}).mem_nhds (by simp))
  obtain ⟨I, hI⟩ :=
    exists_finset_piecewise_mem_of_mem_nhds preimageNeighborhood y
  have finiteDifference :
      ({n : ℕ+ | I.piecewise x y n ≠ y n} : Set ℕ+).Finite := by
    refine I.finite_toSet.subset ?_
    intro n hn
    by_contra hnI
    exact hn (I.piecewise_eq_of_notMem x y hnI)
  have hFx : F (I.piecewise x y) = F x := by
    simpa using hI
  exact hy ((finiteEditInvariant (I.piecewise x y) y finiteDifference).symm.trans hFx)

#print axioms nonconstant_finite_edit_invariant_nowhere_continuous

end D5.S3.Observer.HiddenFlow.FiniteEditTailDiscontinuity
