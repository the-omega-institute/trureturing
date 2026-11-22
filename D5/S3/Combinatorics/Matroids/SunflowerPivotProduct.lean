/- GID: D5/S3/Combinatorics/Matroids/SunflowerPivotProduct
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/SunflowerPivotProduct
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Adding a disjoint petal to a family exchanges an independent restriction. -/

module

public import D5.S3.Combinatorics.Matroids.CircuitCoefficientExchange
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
  let E := c.equivFun.symm
  let b := B.map E
  have hE (i : I) : E (Pi.single i 1) = c i := by
    apply c.equivFun.injective
    simp only [E, LinearEquiv.apply_symm_apply]
    funext j
    simp [Pi.single_apply, Module.Basis.equivFun_self, eq_comm]
  have hy : (∑ i, w i • b i) = y := by
    change (∑ i, w i • E (B i)) = y
    simp_rw [← map_nsmul E]
    rw [← map_sum]
    have hwSum : (∑ i, w i • B i) = fun i => (weight i : ℤ) := by
      simpa only [hw, natCast_zsmul] using B.sum_equivFun (fun i => (weight i : ℤ))
    rw [hwSum]
    simp only [E, Module.Basis.equivFun_symm_apply, natCast_zsmul, y]
  let t := B.equivFun (Pi.single root 1) root
  have hrootVector : c root = t • b root := by
    have h := B.sum_equivFun (Pi.single root 1)
    rw [Fintype.sum_eq_single root] at h
    · rw [← hE root, ← h, map_smul]
      rfl
    · intro i hi
      rw [hpivot i hi, zero_smul]
  let δ : I → ℕ := fun i => if i = root then 1 else 0
  have hδ : ∀ i ∈ A, δ i = 0 := fun i hi => by
    have hne : i ≠ root := fun h => hrootA (h ▸ hi)
    simp [δ, hne]
  have hδsum : ∑ i, δ i • b i = b root := by simp [δ]
  have hK (f : K) : project b A (F.val ∩ A) f.val ∈ K := by
    have hf : (f.val.curryLeft (c root) = 0 ∧ f.val.curryLeft y = 0) ∧ (n : ℤ) • f.val = 0 := f.prop
    let cut := project (d := d + 1) (N := N) b A (F.val ∩ A)
    change (((cut f.val).curryLeft (c root) = 0) ∧ ((cut f.val).curryLeft y = 0)) ∧
      n • cut f.val = 0
    have hr : (cut f.val).curryLeft (c root) =
        (project b A (F.val ∩ A)) (f.val.curryLeft (c root)) := by
      rw [hrootVector, ← hδsum]
      simp only [cut, map_zsmul, insertion_project b A (F.val ∩ A) δ hδ]
    rw [hr, ← hy]
    rw [show (cut f.val).curryLeft (∑ i, w i • b i) =
      (project b A (F.val ∩ A)) (f.val.curryLeft (∑ i, w i • b i)) from
      insertion_project b A (F.val ∩ A) w hzero f.val]
    rw [hy, hf.1.1, hf.1.2, _root_.map_zero, ← map_smul, hf.2, _root_.map_zero]
    exact ⟨⟨rfl, rfl⟩, rfl⟩
  let read' := fun G : Set.powersetCard I (d + 1) =>
    (LinearMap.proj G).comp ((basisFormEquiv (N := N) b).symm.toLinearMap.comp K.subtype)
  have compare (G : Set.powersetCard I (d + 1)) (hG : G ∈ family) : (read G).ker = (read' G).ker := by
    ext f
    change (basisFormEquiv c).symm f.val G = 0 ↔ (basisFormEquiv b).symm f.val G = 0
    rw [basisFormEquiv_symm_apply, basisFormEquiv_symm_apply]
    let labels := (G.val.orderIsoOfFin G.prop).toEquiv
    have hlabel (i : Fin (d + 1)) : (labels i : I) = ofFinEmbEquiv.symm G i := rfl
    have h := tuple_vanishing_iff_of_supported_change G.val B labels
      (fun i hi j hj => (hsupp ⟨G, hG⟩ i hi j hj).1)
      (fun i hi j hj => (hsupp ⟨G, hG⟩ i hi j hj).2)
      (f.val.compLinearMap E.toLinearMap)
    simpa only [AlternatingMap.compLinearMap_apply, LinearEquiv.coe_toLinearMap, hE, hlabel, b,
      Module.Basis.map_apply, Function.comp_def] using h
  have hold : old = ⨅ G : previous, (read' G.val).ker := by
    change (⨅ G : previous, (read G.val).ker) = _
    exact iInf_congr fun G => compare G.val (mem_insert_of_mem G.prop)
  have hsep' (G : Set.powersetCard I (d + 1)) (hG : G ∈ previous) : G.val ∩ A ≠ F.val ∩ A := by
    intro h
    have he : (⟨G, mem_insert_of_mem hG⟩ : family) = ⟨F, mem_insert_self _ _⟩ := hsep h
    have hGF : G = F := congrArg Subtype.val he
    exact hnew (hGF ▸ hG)
  rw [hold, compare F (mem_insert_self _ _)]
  exact coefficient_family_exchange b A K F previous hK hsep'

end D5.S3.Combinatorics.Matroids.SunflowerPivotProduct
