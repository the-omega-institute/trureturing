/- GID: D5/S3/Combinatorics/Matroids/SupportedPivotProduct
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/SupportedPivotProduct
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: A supported basis change transports the pivot coefficient product identity. -/

module

public import D5.S3.Combinatorics.Matroids.CircuitCoefficientExchange
public import D5.S3.Combinatorics.Matroids.PrivatePairCircuitWeightBasis

/-! Transport of coefficient products through supported integral bases. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.SupportedPivotProduct

open Finset UniformCircuitResidueForms CircuitWeightBlocks CircuitPassiveCoordinates
open CircuitCoefficientExchange PrivatePairCircuitWeightBasis
open Set.powersetCard (ofFinEmbEquiv)

set_option autoImplicit false

/-- A basis change preserving the pivot line and the omitted faces transports
the coefficient-exchange product whenever the new coefficient is separated
from every prior coefficient by zero-weight indices. -/
theorem pivot_product_of_supported_basis {I N : Type*}
    [Fintype I] [LinearOrder I] [AddCommGroup N] {d : ℕ}
    (c : Module.Basis I ℤ (I → ℤ)) (root : I) (weight : I → ℕ) (n : ℤ)
    (F : Set.powersetCard I (d + 1)) (previous : Finset (Set.powersetCard I (d + 1)))
    (B : Module.Basis I ℤ (I → ℤ)) (w : I → ℕ) (A : Finset I)
    (hw : ∀ i, B.equivFun (fun j => (weight j : ℤ)) i = (w i : ℤ))
    (hzero : ∀ i ∈ A, w i = 0) (hrootA : root ∉ A)
    (hsep : ∀ G ∈ previous, G.val ∩ A ≠ F.val ∩ A)
    (hsupp : ∀ G ∈ insert F previous, ∀ i ∈ G.val, ∀ j ∉ G.val,
      B i j = 0 ∧ B.equivFun (Pi.single i 1) j = 0)
    (hpivot : ∀ j ≠ root, B.equivFun (Pi.single root 1) j = 0) :
    let y := ∑ i, weight i • c i
    let K := ((insertVector (n := d) (N := N) (c root)).ker ⊓ (insertVector y).ker) ⊓
      Submodule.torsionBy ℤ _ n
    let read := fun G : Set.powersetCard I (d + 1) =>
      (LinearMap.proj G).comp ((basisFormEquiv (N := N) c).symm.toLinearMap.comp K.subtype)
    let old := ⨅ G : previous, (read G.val).ker
    Nonempty ((↥K × ↥(old ⊓ (read F).ker)) ≃ₗ[ℤ] (↥old × ↥(read F).ker)) := by
  classical
  intro y K read old
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
  have compare (G : Set.powersetCard I (d + 1)) (hG : G ∈ insert F previous) : (read G).ker = (read' G).ker := by
    ext f
    change (basisFormEquiv c).symm f.val G = 0 ↔ (basisFormEquiv b).symm f.val G = 0
    rw [basisFormEquiv_symm_apply, basisFormEquiv_symm_apply]
    let labels := (G.val.orderIsoOfFin G.prop).toEquiv
    have hlabel (i : Fin (d + 1)) : (labels i : I) = ofFinEmbEquiv.symm G i := rfl
    have h := tuple_vanishing_iff_of_supported_change G.val B labels
      (fun i hi j hj => (hsupp G hG i hi j hj).1)
      (fun i hi j hj => (hsupp G hG i hi j hj).2)
      (f.val.compLinearMap E.toLinearMap)
    simpa only [AlternatingMap.compLinearMap_apply, LinearEquiv.coe_toLinearMap, hE, hlabel, b,
      Module.Basis.map_apply, Function.comp_def] using h
  have hold : old = ⨅ G : previous, (read' G.val).ker := by
    change (⨅ G : previous, (read G.val).ker) = _
    exact iInf_congr fun G => compare G.val (mem_insert_of_mem G.prop)
  rw [hold, compare F (mem_insert_self _ _)]
  exact coefficient_family_exchange b A K F previous hK hsep

/-- Two private indices in each face suffice for the pivot product identity,
even when the faces overlap away from those indices. -/
theorem private_pair_pivot_product {I N : Type*} [Fintype I] [LinearOrder I] [AddCommGroup N]
    {d : ℕ} (c : Module.Basis I ℤ (I → ℤ)) (root : I) (weight : I → ℕ)
    (hweight : ∀ i, 0 < weight i) (n : ℤ)
    (F : Set.powersetCard I (d + 1)) (previous : Finset (Set.powersetCard I (d + 1)))
    (hnew : F ∉ previous)
    (hroot : ∀ G ∈ insert F previous, root ∉ G.val)
    (hprivate : ∀ G ∈ insert F previous, ∃ i ∈ G.val, ∃ j ∈ G.val, i ≠ j ∧
      ∀ H ∈ insert F previous, H ≠ G → i ∉ H.val ∧ j ∉ H.val) :
    let y := ∑ i, weight i • c i
    let K := ((insertVector (n := d) (N := N) (c root)).ker ⊓ (insertVector y).ker) ⊓
      Submodule.torsionBy ℤ _ n
    let read := fun G : Set.powersetCard I (d + 1) =>
      (LinearMap.proj G).comp ((basisFormEquiv (N := N) c).symm.toLinearMap.comp K.subtype)
    let old := ⨅ G : previous, (read G.val).ker
    Nonempty ((↥K × ↥(old ⊓ (read F).ker)) ≃ₗ[ℤ] (↥old × ↥(read F).ker)) := by
  classical
  let family := insert F previous
  have hp (G : family) : ∃ i ∈ G.val.val, ∃ j ∈ G.val.val, i ≠ j ∧
      ∀ H : family, H ≠ G → i ∉ H.val.val ∧ j ∉ H.val.val := by
    obtain ⟨i, hi, j, hj, hne, hother⟩ := hprivate G.val G.prop
    exact ⟨i, hi, j, hj, hne, fun H h => hother H.val H.prop fun he => h (Subtype.ext he)⟩
  obtain ⟨B, w, A, hw, hzero, hrootA, hsep, hsupp, hpivot⟩ :=
    exists_private_pair_weight_basis (fun G : family => G.val.val) root
      (fun G => hroot G.val G.prop) hp weight hweight
  refine pivot_product_of_supported_basis c root weight n F previous B w A hw hzero hrootA
    ?_ (fun G hG => hsupp ⟨G, hG⟩) hpivot
  intro G hG he
  have h : (⟨G, mem_insert_of_mem hG⟩ : family) = ⟨F, mem_insert_self _ _⟩ := hsep he
  have hGF : G = F := congrArg Subtype.val h
  exact hnew (hGF ▸ hG)

end D5.S3.Combinatorics.Matroids.SupportedPivotProduct
