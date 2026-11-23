/- GID: D5/S3/Combinatorics/Matroids/SunflowerCircuitInvariantFactors
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/SunflowerCircuitInvariantFactors
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Independent cyclic factor replacement for a common-element sunflower of omitted bases. -/

import D5.S3.Combinatorics.Matroids.PrivatePairCircuitInvariantFactors
import D5.S3.Combinatorics.Matroids.SunflowerCircuitResidueProduct

/-! Cyclic factors of the lifting obstruction for omissions with disjoint petals. -/

namespace D5.S3.Combinatorics.Matroids.SunflowerCircuitInvariantFactors

open Finset PrivatePairCircuitInvariantFactors PrivatePairOmissionFamily
open JointCircuitLiftingObstruction (JointSaturatedImage JointImageInSaturation)
open scoped Matroid

set_option autoImplicit false

/-- For a common-element sunflower of omitted bases, each petal removes one
copy of each uniform cyclic order and adds its own gcd factor. -/
theorem sunflower_lifting_obstruction_invariant_factors {V : Type*} [Fintype V] [LinearOrder V]
    {k d : ℕ} {S : Matroid (Fin (k + 2))} (hd : 1 ≤ d) (hr : d < k)
    (root : Fin (k + 2)) (family : Finset (Finset (Fin (k + 2))))
    (hsize : ∀ H ∈ family, H.card = d + 2) (hroot : ∀ H ∈ family, root ∈ H)
    (hdisjoint : (↑family : Set (Finset (Fin (k + 2)))).Pairwise
      (fun H J => Disjoint (H.erase root) (J.erase root)))
    (ha : family.card ≤ k.choose d) (hb : family.card ≤ k.choose (d + 1))
    (hground : S.E = Set.univ)
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
  have hprivate := HasPrivatePairs.of_disjoint_petals family root
    (fun H hH => by rw [card_erase_of_mem (hroot H hH), hsize H hH]; omega) hdisjoint
  exact private_pair_lifting_obstruction_invariant_factors hd hr root family hsize hroot
    hprivate hbases p hp horder

end D5.S3.Combinatorics.Matroids.SunflowerCircuitInvariantFactors
