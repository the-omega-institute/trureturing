/- GID: D5/S3/Combinatorics/Matroids/PrivatePairCircuitResidueProduct
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/PrivatePairCircuitResidueProduct
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: The residue product for adding one omitted base to overlapping omissions with private pairs. -/

module

public import D5.S3.Combinatorics.Matroids.PrivatePairOmissionFamily
public import D5.S3.Combinatorics.Matroids.MembershipCircuitResidueProduct

/-! The residue product for omissions with two private indices per omitted set. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.PrivatePairCircuitResidueProduct

open Finset PrivatePairOmissionFamily MembershipSeparatedOmissions MembershipCircuitResidueProduct
open ParallelCircuitObstruction (weightedCircuitResidues)
open scoped Matroid

set_option autoImplicit false

/-- An omitted family with private pairs and the uniform core have the same
product as the residue modules for a subfamily and its one omitted petal. -/
theorem private_pair_residue_product {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V]
    (p : V → I) (hp : Function.Surjective p) {d : ℕ} (hd : 1 ≤ d)
    (hr : d + 2 < Fintype.card I) (root : I)
    (H : Finset I) (previous : Finset (Finset I)) (hnew : H ∉ previous)
    (hsize : ∀ T ∈ insert H previous, T.card = d + 2)
    (hroot : ∀ T ∈ insert H previous, root ∈ T)
    (hprivate : HasPrivatePairs (insert H previous))
    (M : Bool → Bool → Matroid I)
    (hbases : ∀ i j (B : Finset I), (M i j).IsBase (B : Set I) ↔
      B.card = d + 2 ∧ (i = true → B ∉ previous) ∧ (j = true → B ≠ H)) :
    Nonempty ((weightedCircuitResidues (M false false) p × weightedCircuitResidues (M true true) p) ≃ₗ[ℤ]
      (weightedCircuitResidues (M true false) p × weightedCircuitResidues (M false true) p)) := by
  exact membership_residue_product p hp hd hr root H previous hnew hsize hroot
    (HasSeparatedMembership.of_private_pairs hprivate) M hbases

end D5.S3.Combinatorics.Matroids.PrivatePairCircuitResidueProduct
