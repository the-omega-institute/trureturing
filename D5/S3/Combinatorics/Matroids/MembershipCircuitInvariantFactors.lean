/- GID: D5/S3/Combinatorics/Matroids/MembershipCircuitInvariantFactors
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/MembershipCircuitInvariantFactors
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Independent cyclic factor replacement for omissions with separated membership and a common pivot. -/

import D5.S3.Combinatorics.Matroids.MembershipSeparatedOmissions
import D5.S3.Combinatorics.Matroids.MembershipCircuitResidueProduct
import D5.S3.Combinatorics.Matroids.CommonPivotCircuitInvariantFactors
import D5.S3.Combinatorics.Matroids.PuncturedCircuitInvariantFactors
import D5.S3.Combinatorics.Matroids.UniformCircuitInvariantFactors
import D5.S3.FiniteGroups.Modules.FiniteModuleProductCancellation

/-! Cyclic factors of the lifting obstruction for overlapping omissions with separated membership. -/

namespace D5.S3.Combinatorics.Matroids.MembershipCircuitInvariantFactors

open Finset SparsePavingCircuitCoordinates MembershipCircuitResidueProduct MembershipSeparatedOmissions
open PuncturedCircuitInvariantFactors UniformCircuitInvariantFactors
open ParallelCircuitObstruction (parallel_lifting_obstruction weightedCircuitResidues)
open JointCircuitLiftingObstruction (JointSaturatedImage JointImageInSaturation)
open D5.S3.FiniteGroups.FiniteModuleProductCancellation (finite_prod_cancel)
open scoped Matroid

set_option autoImplicit false

/-- For omissions with a common element and separated membership, each petal removes one
copy of each uniform cyclic order and adds its own gcd factor. -/
theorem membership_lifting_obstruction_invariant_factors {V : Type*} [Fintype V] [LinearOrder V]
    {k d : ℕ} {S : Matroid (Fin (k + 2))} (hd : 1 ≤ d) (hr : d < k)
    (root : Fin (k + 2)) (family : Finset (Finset (Fin (k + 2))))
    (hsize : ∀ H ∈ family, H.card = d + 2) (hroot : ∀ H ∈ family, root ∈ H)
    (hseparated : HasSeparatedMembership family)
    (hbases : ∀ B : Finset (Fin (k + 2)), S.IsBase (B : Set (Fin (k + 2))) ↔
      B.card = d + 2 ∧ B ∉ family)
    (p : V → Fin (k + 2)) (hp : Function.Surjective p) (horder : ∀ ⦃x y⦄, p x < p y → x < y) :
    let n := Fintype.card V
    let weight (i : Fin (k + 2)) := (univ.filter fun v => p v = i).card
    let g := univ.gcd weight
    let q (H : Finset (Fin (k + 2))) := n.gcd ((univ \ H).gcd weight)
    Nonempty ((JointSaturatedImage (S.comap p) ⧸ JointImageInSaturation (S.comap p)) ≃ₗ[ℤ]
      (((Fin (k.choose d - family.card) → ZMod g) × (Fin (k.choose (d + 1) - family.card) → ZMod n)) ×
        (∀ T : family, ZMod (q T.val)))) := by
  have hbound : ∀ T ∈ family, ∀ U ∈ family, T ≠ U →
      (T ∩ U).card + 2 ≤ d + 2 := by
    intro T hT U hU hne
    have bound := hseparated.inter_card_add_two_le hT hU hne
      ((hsize T hT).trans (hsize U hU).symm)
    exact bound.trans (hsize T hT).le
  exact (D5.S3.Combinatorics.Matroids.CommonPivotCircuitInvariantFactors.common_pivot_lifting_obstruction_invariant_factors hd hr root family hsize hroot
      hbound hbases p hp horder).2.2

end D5.S3.Combinatorics.Matroids.MembershipCircuitInvariantFactors
