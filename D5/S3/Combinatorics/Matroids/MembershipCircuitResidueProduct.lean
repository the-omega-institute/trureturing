/- GID: D5/S3/Combinatorics/Matroids/MembershipCircuitResidueProduct
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/MembershipCircuitResidueProduct
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Common-pivot omitted bases distinguished by membership classes. -/

module

public import D5.S3.Combinatorics.Matroids.CircuitDifferenceBasis
public import D5.S3.Combinatorics.Matroids.SparsePavingCircuitCoordinates
public import D5.S3.Combinatorics.Matroids.SupportedPivotProduct
import D5.S3.Combinatorics.Matroids.MembershipCircuitWeightBasis
public import D5.S3.Combinatorics.Matroids.MembershipSeparatedOmissions
public import D5.S3.Combinatorics.Matroids.CommonPivotCircuitResidueProduct

/-! Residues in simultaneous difference coordinates around the common element. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.MembershipCircuitResidueProduct

open Finset UniformCircuitResidueForms UniformCircuitBasis SparsePavingCircuitCoordinates
open CircuitDifferenceBasis SupportedPivotProduct MembershipCircuitWeightBasis MembershipSeparatedOmissions
open ParallelCircuitObstruction (weightedCircuitResidues)
open RationalJointCircuitImage (RationalResidue)
open Set.powersetCard (ofFinEmbEquiv)
open scoped Matroid

set_option autoImplicit false

/-- An omitted family with separated membership and the uniform core have the same
product as the residue modules for a subfamily and its one omitted petal. -/
theorem membership_residue_product {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V]
    (p : V → I) (hp : Function.Surjective p) {d : ℕ} (hd : 1 ≤ d)
    (hr : d + 2 < Fintype.card I) (root : I)
    (H : Finset I) (previous : Finset (Finset I)) (hnew : H ∉ previous)
    (hsize : ∀ T ∈ insert H previous, T.card = d + 2)
    (hroot : ∀ T ∈ insert H previous, root ∈ T)
    (hseparated : HasSeparatedMembership (insert H previous))
    (M : Bool → Bool → Matroid I)
    (hbases : ∀ i j (B : Finset I), (M i j).IsBase (B : Set I) ↔
      B.card = d + 2 ∧ (i = true → B ∉ previous) ∧ (j = true → B ≠ H)) :
    Nonempty ((weightedCircuitResidues (M false false) p × weightedCircuitResidues (M true true) p) ≃ₗ[ℤ]
      (weightedCircuitResidues (M true false) p × weightedCircuitResidues (M false true) p)) := by
  refine D5.S3.Combinatorics.Matroids.CommonPivotCircuitResidueProduct.common_pivot_residue_product p hp hd hr root H previous hnew hsize hroot ?_ M hbases
  intro T hT U hU hne
  have bound := hseparated.inter_card_add_two_le hT hU hne
    ((hsize T hT).trans (hsize U hU).symm)
  exact bound.trans (hsize T hT).le

end D5.S3.Combinatorics.Matroids.MembershipCircuitResidueProduct
