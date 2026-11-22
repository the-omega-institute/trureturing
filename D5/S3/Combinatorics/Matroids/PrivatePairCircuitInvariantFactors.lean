/- GID: D5/S3/Combinatorics/Matroids/PrivatePairCircuitInvariantFactors
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/PrivatePairCircuitInvariantFactors
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Independent cyclic factor replacement for omissions with private pairs and a common pivot. -/

import D5.S3.Combinatorics.Matroids.MembershipCircuitInvariantFactors

/-! Cyclic factors of the lifting obstruction for overlapping omissions with private pairs. -/

namespace D5.S3.Combinatorics.Matroids.PrivatePairCircuitInvariantFactors

open Finset PrivatePairOmissionFamily MembershipSeparatedOmissions MembershipCircuitInvariantFactors
open JointCircuitLiftingObstruction (JointSaturatedImage JointImageInSaturation)
open scoped Matroid

set_option autoImplicit false

/-- For omissions with a common element and private pairs, each petal removes one
copy of each uniform cyclic order and adds its own gcd factor. -/
theorem private_pair_lifting_obstruction_invariant_factors {V : Type*} [Fintype V] [LinearOrder V]
    {k d : ℕ} {S : Matroid (Fin (k + 2))} (hd : 1 ≤ d) (hr : d < k)
    (root : Fin (k + 2)) (family : Finset (Finset (Fin (k + 2))))
    (hsize : ∀ H ∈ family, H.card = d + 2) (hroot : ∀ H ∈ family, root ∈ H)
    (hprivate : HasPrivatePairs family)
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
  exact membership_lifting_obstruction_invariant_factors hd hr root family hsize hroot
    (HasSeparatedMembership.of_private_pairs hprivate) hbases p hp horder

end D5.S3.Combinatorics.Matroids.PrivatePairCircuitInvariantFactors
