/- GID: D5/S3/Combinatorics/Matroids/CircuitOmittedFaceProduct
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/CircuitOmittedFaceProduct
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Two separated face equations act on distinct factors of the pivoted weight kernel. -/

module

public import D5.S3.Combinatorics.Matroids.CircuitPassiveCoordinates
public import D5.S3.Combinatorics.Matroids.CircuitWeightBlocks

/-! The product identity for two face coefficients in a pivoted circuit form. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.CircuitOmittedFaceProduct

open Finset UniformCircuitResidueForms CircuitWeightBlocks CircuitPassiveCoordinates
open Set.powersetCard (ofFinEmbEquiv)

set_option autoImplicit false

variable {I N : Type*} [Fintype I] [LinearOrder I] [AddCommGroup N]
variable {d : ℕ}

private noncomputable def enumerate (F : Set.powersetCard I (d + 1)) : Fin (d + 1) ≃ F.val :=
  let labels := ofFinEmbEquiv.symm F
  Equiv.ofBijective
    (fun i => ⟨labels i, (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem F _).mp
      ⟨i, rfl⟩⟩)
    ⟨fun _ _ h => labels.injective (congrArg Subtype.val h),
      fun x => by
        obtain ⟨i, hi⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem F _).mpr x.prop
        exact ⟨i, Subtype.ext hi⟩⟩

/-- Two face equations in the pivoted weight kernel act on different
factors when one face has at least two indices outside the other. -/
theorem pivoted_face_product (c : Module.Basis I ℤ (I → ℤ))
    (root : I) (weight : I → ℕ) (hweight : ∀ i, 0 < weight i) (n : ℕ)
    (F G : Set.powersetCard I (d + 1)) (hroot : root ∉ F.val)
    (hFG : 1 < (F.val \ G.val).card) :
    let y := ∑ i, weight i • c i
    let K := ((insertVector (n := d) (N := N) (c root)).ker ⊓ (insertVector y).ker) ⊓
      Submodule.torsionBy ℤ _ (n : ℤ)
    let read := fun H : Set.powersetCard I (d + 1) =>
      (LinearMap.proj H).comp ((basisFormEquiv (N := N) c).symm.toLinearMap.comp K.subtype)
    Nonempty ((↥K × ↥((read F).ker ⊓ (read G).ker)) ≃ₗ[ℤ] (↥(read F).ker × ↥(read G).ker)) := by
  intro y K read
  obtain ⟨B, w, A, hw, hzero, hsep, hrootA, hsupp⟩ :=
    exists_basis_separating_faces F.val G.val hFG root hroot weight hweight
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
    have hsum : (∑ i, w i • B i) = fun i => (weight i : ℤ) := by
      simpa only [hw, natCast_zsmul] using B.sum_equivFun (fun i => (weight i : ℤ))
    rw [hsum]
    simp only [E, Module.Basis.equivFun_symm_apply, natCast_zsmul, y]
  let t := B.equivFun (Pi.single root 1) root
  have hrootVector : c root = t • b root := by
    have hv := B.sum_equivFun (Pi.single root 1)
    rw [Fintype.sum_eq_single root] at hv
    · rw [← hE root, ← hv, map_smul]
      rfl
    · intro i hi
      have h := (hsupp {root} (by simp) root (by simp) i (by simpa using hi)).2
      rw [h, zero_smul]
  let δ : I → ℕ := fun i => if i = root then 1 else 0
  have hδ : ∀ i ∈ A, δ i = 0 := fun i hi => by
    have hne : i ≠ root := fun h => hrootA (h ▸ hi)
    simp [δ, hne]
  have hδsum : ∑ i, δ i • b i = b root := by
    simp [δ]
  have hK (f : K) (S : A.powerset) : (project b A S.val) f.val ∈ K := by
    have hf : (f.val.curryLeft (c root) = 0 ∧ f.val.curryLeft y = 0) ∧ (n : ℤ) • f.val = 0 := f.prop
    change (((project b A S.val) f.val).curryLeft (c root) = 0 ∧
      ((project b A S.val) f.val).curryLeft y = 0) ∧ (n : ℤ) • (project b A S.val) f.val = 0
    have hr : ((project b A S.val) f.val).curryLeft (c root) =
        (project b A S.val) (f.val.curryLeft (c root)) := by
      rw [hrootVector, ← hδsum]
      simp only [map_zsmul, insertion_project b A S.val δ hδ]
    rw [hr, ← hy, insertion_project b A S.val w hzero, hy, hf.1.1, hf.1.2,
      _root_.map_zero, ← map_smul, hf.2, _root_.map_zero]
    exact ⟨⟨rfl, rfl⟩, rfl⟩
  let read' := fun H : Set.powersetCard I (d + 1) =>
    (LinearMap.proj H).comp ((basisFormEquiv (N := N) b).symm.toLinearMap.comp K.subtype)
  have compare (H : Set.powersetCard I (d + 1)) (hH : H.val ∈ ({F.val, G.val, {root}} : Finset (Finset I))) :
      (read H).ker = (read' H).ker := by
    ext f
    change (basisFormEquiv c).symm f.val H = 0 ↔ (basisFormEquiv b).symm f.val H = 0
    rw [basisFormEquiv_symm_apply, basisFormEquiv_symm_apply]
    have he (i : Fin (d + 1)) : ((enumerate H i : H.val) : I) = ofFinEmbEquiv.symm H i := rfl
    have h := tuple_vanishing_iff_of_supported_change H.val B (enumerate H)
      (fun i hi j hj => (hsupp H.val hH i hi j hj).1)
      (fun i hi j hj => (hsupp H.val hH i hi j hj).2)
      (f.val.compLinearMap E.toLinearMap)
    simpa only [AlternatingMap.compLinearMap_apply, LinearEquiv.coe_toLinearMap, hE, he, b,
      Module.Basis.map_apply, Function.comp_def] using h
  rw [compare F (by simp), compare G (by simp)]
  exact separated_coefficients_product b A K hK F G hsep

end D5.S3.Combinatorics.Matroids.CircuitOmittedFaceProduct
