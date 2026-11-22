/- GID: D5/S3/Combinatorics/Matroids/SunflowerCircuitResidueProduct
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/SunflowerCircuitResidueProduct
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: The residue product for adding one omitted base to a common-element sunflower. -/

module

public import D5.S3.Combinatorics.Matroids.PrivatePairCircuitResidueProduct
public import D5.S3.Combinatorics.Matroids.SunflowerPivotProduct

/-! Residues in simultaneous difference coordinates around the common element. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.SunflowerCircuitResidueProduct

open Finset PrivatePairCircuitResidueProduct PrivatePairOmissionFamily
open ParallelCircuitObstruction (weightedCircuitResidues)
open scoped Matroid

set_option autoImplicit false

/-- The residue modules for a sunflower and the uniform core have the same
product as the residue modules for a subfamily and its one omitted petal. -/
theorem sunflower_residue_product {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V]
    (p : V → I) (hp : Function.Surjective p) {d : ℕ} (hd : 1 ≤ d)
    (hr : d + 2 < Fintype.card I) (root : I)
    (H : Finset I) (previous : Finset (Finset I)) (hnew : H ∉ previous)
    (hsize : ∀ T ∈ insert H previous, T.card = d + 2)
    (hroot : ∀ T ∈ insert H previous, root ∈ T)
    (hdisjoint : (↑(insert H previous) : Set (Finset I)).Pairwise
      (fun F G => Disjoint (F.erase root) (G.erase root)))
    (M : Bool → Bool → Matroid I) (hground : ∀ i j, (M i j).E = Set.univ)
    (hbases : ∀ i j (B : Finset I), (M i j).IsBase (B : Set I) ↔
      B.card = d + 2 ∧ (i = true → B ∉ previous) ∧ (j = true → B ≠ H)) :
    Nonempty ((weightedCircuitResidues (M false false) p × weightedCircuitResidues (M true true) p) ≃ₗ[ℤ]
      (weightedCircuitResidues (M true false) p × weightedCircuitResidues (M false true) p)) := by
  have hprivate := HasPrivatePairs.of_disjoint_petals (insert H previous) root
    (fun T hT => by rw [card_erase_of_mem (hroot T hT), hsize T hT]; omega) hdisjoint
  exact private_pair_residue_product p hp hd hr root H previous hnew hsize hroot hprivate
    M hbases

end D5.S3.Combinatorics.Matroids.SunflowerCircuitResidueProduct
