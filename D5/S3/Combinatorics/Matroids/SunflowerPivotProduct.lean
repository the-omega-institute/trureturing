/- GID: D5/S3/Combinatorics/Matroids/SunflowerPivotProduct
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/SunflowerPivotProduct
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Adding a disjoint petal to a family exchanges an independent restriction. -/

module

public import D5.S3.Combinatorics.Matroids.SupportedPivotProduct
public import D5.S3.Combinatorics.Matroids.SunflowerCircuitWeightBasis

/-! Products of pivoted circuit forms with disjoint coefficient restrictions. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.SunflowerPivotProduct

open Finset UniformCircuitResidueForms CircuitWeightBlocks CircuitPassiveCoordinates
open SunflowerCircuitWeightBasis CircuitCoefficientExchange
open Set.powersetCard (ofFinEmbEquiv)

set_option autoImplicit false

/-- For disjoint petals of size at least two avoiding the pivot, the kernel
with one new coefficient condition satisfies the product identity against the
previous conditions and the new condition on its own. -/
theorem sunflower_pivot_product {I N : Type*} [Fintype I] [LinearOrder I] [AddCommGroup N]
    {d : ℕ} (hd : 1 ≤ d) (c : Module.Basis I ℤ (I → ℤ))
    (root : I) (weight : I → ℕ) (hweight : ∀ i, 0 < weight i) (n : ℤ)
    (F : Set.powersetCard I (d + 1)) (previous : Finset (Set.powersetCard I (d + 1)))
    (hnew : F ∉ previous)
    (hroot : ∀ G ∈ insert F previous, root ∉ G.val)
    (hdisjoint : (↑(insert F previous) : Set (Set.powersetCard I (d + 1))).Pairwise
      (fun G H => Disjoint G.val H.val)) :
    let y := ∑ i, weight i • c i
    let K := ((insertVector (n := d) (N := N) (c root)).ker ⊓ (insertVector y).ker) ⊓
      Submodule.torsionBy ℤ _ n
    let read := fun G : Set.powersetCard I (d + 1) =>
      (LinearMap.proj G).comp ((basisFormEquiv (N := N) c).symm.toLinearMap.comp K.subtype)
    let old := ⨅ G : previous, (read G.val).ker
    Nonempty ((↥K × ↥(old ⊓ (read F).ker)) ≃ₗ[ℤ] (↥old × ↥(read F).ker)) := by
  classical
  intro y K read old
  let family := insert F previous
  have hfamily : Pairwise (fun G H : family => Disjoint G.val.val H.val.val) := by
    intro G H hne
    exact hdisjoint G.prop H.prop (fun h => hne (Subtype.ext h))
  have hlarge (G : family) : 1 < G.val.val.card := by
    rw [G.val.prop]
    omega
  obtain ⟨B, w, A, hw, hzero, hrootA, hsep, hsupp, hpivot⟩ :=
    exists_sunflower_weight_basis (fun G : family => G.val.val) hfamily hlarge root
      (fun G => hroot G.val G.prop) weight hweight
  refine SupportedPivotProduct.pivot_product_of_supported_basis
    c root weight n F previous B w A hw hzero hrootA ?_ (fun G hG => hsupp ⟨G, hG⟩) hpivot
  intro G hG h
  have he : (⟨G, mem_insert_of_mem hG⟩ : family) = ⟨F, mem_insert_self _ _⟩ := hsep h
  have hGF : G = F := congrArg Subtype.val he
  exact hnew (hGF ▸ hG)

end D5.S3.Combinatorics.Matroids.SunflowerPivotProduct
