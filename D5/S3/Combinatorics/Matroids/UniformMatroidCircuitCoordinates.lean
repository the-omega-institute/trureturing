/- GID: D5/S3/Combinatorics/Matroids/UniformMatroidCircuitCoordinates
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/UniformMatroidCircuitCoordinates
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Coordinate conversion between uniform matroid restrictions and alternating forms. -/

module

public import D5.S3.Combinatorics.Matroids.ParallelCircuitObstruction
public import D5.S3.Combinatorics.Matroids.UniformCircuitResidueForms

/-! Bases and circuit readouts in the uniform core. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.UniformMatroidCircuitCoordinates

open Finset
open scoped Matroid
set_option autoImplicit false

variable {I : Type*} [Fintype I] [LinearOrder I] {M : Matroid I} {r : ℕ}

omit [LinearOrder I] in
theorem indep_iff_card_le
    (hbases : ∀ B : Finset I, M.IsBase (B : Set I) ↔ B.card = r)
    (hr : r ≤ Fintype.card I) (F : Finset I) :
    M.Indep (F : Set I) ↔ F.card ≤ r := by
  constructor
  · intro hF
    obtain ⟨B, hB, hsub⟩ := hF.exists_isBase_superset
    let T := B.toFinite.toFinset
    have hT : (T : Set I) = B := Set.Finite.coe_toFinset _
    have hcard : T.card = r := (hbases T).mp (hT.symm ▸ hB)
    rw [← hcard]
    exact card_le_card (Finset.coe_subset.mp (hT.symm ▸ hsub))
  · intro hF
    obtain ⟨B, hFB, _, hcard⟩ :=
      exists_subsuperset_card_eq (subset_univ F) hF (by simpa using hr)
    exact ((hbases B).mpr hcard).indep.subset (Finset.coe_subset.mpr hFB)

lemma circuit_iff_card
    (hbases : ∀ B : Finset I, M.IsBase (B : Set I) ↔ B.card = r)
    (hground : M.E = Set.univ) (hr : r ≤ Fintype.card I) (C : Finset I) :
    M.IsCircuit (C : Set I) ↔ C.card = r + 1 := by
  rw [Matroid.isCircuit_iff_forall_ssubset, Matroid.dep_iff, indep_iff_card_le hbases hr,
    hground, and_iff_left (Set.subset_univ _)]
  constructor
  · rintro ⟨hdep, hminimal⟩
    obtain ⟨i, hi⟩ := card_pos.mp (by omega : 0 < C.card)
    have hs : ((C.erase i : Finset I) : Set I) ⊂ (C : Set I) :=
      Finset.coe_ssubset.mpr (erase_ssubset hi)
    have hle := (indep_iff_card_le hbases hr _).mp (hminimal hs)
    rw [card_erase_of_mem hi] at hle
    omega
  · intro hC
    refine ⟨by omega, fun F hF => ?_⟩
    let B := F.toFinite.toFinset
    have hB : (B : Set I) = F := Set.Finite.coe_toFinset _
    have hlt : B.card < C.card := card_lt_card (Finset.coe_ssubset.mp (hB.symm ▸ hF))
    rw [← hB]
    exact (indep_iff_card_le hbases hr _).mpr (by omega)

omit [Fintype I] in
lemma contracted_basis_eq_empty
    (hbases : ∀ B : Finset I, M.IsBase (B : Set I) ↔ B.card = r)
    {C T : Finset I} (hC : M.IsCircuit (C : Set I))
    (hcard : C.card = r + 1) :
    (M ／ (C : Set I)).IsBase (T : Set I) ↔ T = ∅ := by
  obtain ⟨i, hi⟩ := card_pos.mp (by omega : 0 < C.card)
  have hB : M.IsBase (↑(C.erase i) : Set I) := by
    apply (hbases _).mpr
    rw [card_erase_of_mem hi, hcard]
    omega
  have hJ : M.IsBasis (↑(C.erase i) : Set I) (C : Set I) :=
    Matroid.IsBase.isBasis_of_subset hC.subset_ground hB
      (Finset.coe_subset.mpr (erase_subset _ _))
  have hInd (U : Set I) (hU : (M ／ (C : Set I)).Indep U) : U = ∅ := by
    obtain ⟨hIU, hd⟩ := hJ.contract_indep_iff.mp hU
    have he := hB.eq_of_subset_indep hIU Set.subset_union_right
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have hmem : u ∈ U ∪ (↑(C.erase i) : Set I) := Or.inl hu
    rw [← he] at hmem
    exact (Set.disjoint_left.mp hd (mem_of_mem_erase hmem)) hu
  have hEmpty : (M ／ (C : Set I)).IsBase ∅ :=
    (Matroid.empty_indep _).isBase_of_maximal (fun U hU _ => (hInd U hU).symm)
  constructor
  · intro h
    exact Finset.coe_inj.mp (by simpa using hInd _ h.indep)
  · rintro rfl
    simpa using hEmpty

open UniformCircuitResidueForms
open Set.powersetCard (ofFinEmbEquiv)
open ParallelCircuitObstruction (circuitReadout weightedBoundary weightedCircuitResidues)
open ParallelCircuitCoordinates
open RationalJointCircuitImage (RationalResidue)
open CircuitCycleDecomposition (restrictionSign)
open OrderedCycleFactorization (shuffleSign)
open D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)

omit [Fintype I] in
private lemma formCoordinates_card_ne_zero {N : Type*} [AddCommGroup N] {n : ℕ}
    (b : Module.Basis I ℤ (I → ℤ)) (f : (I → ℤ) [⋀^Fin n]→ₗ[ℤ] N)
    (S : Finset I) (h : S.card ≠ n) : formCoordinates b f S = 0 := by
  rw [formCoordinates, dite_eq_right h]

private lemma weightedBoundary_formCoordinates {V : Type*} [Fintype V]
    (p : V → I) {n : ℕ} (b : Module.Basis I ℤ (I → ℤ))
    (f : (I → ℤ) [⋀^Fin (n + 1)]→ₗ[ℤ] RationalResidue) :
    (∀ T, weightedBoundary p (formCoordinates b f) T = 0) ↔
      f.curryLeft (∑ i, (univ.filter (fun x => p x = i)).card • b i) = 0 := by
  constructor
  · intro h
    apply (basisFormEquiv b).symm.injective
    rw [map_zero]
    funext S
    rw [basisFormEquiv_symm_apply, curryLeft_weighted_basis]
    simpa only [Equiv.apply_symm_apply, weightedBoundary, Pi.zero_apply] using h S.val
  · intro hf T
    by_cases hT : T.card = n
    · let e := ofFinEmbEquiv.symm (⟨T, hT⟩ : Set.powersetCard I n)
      have hS : (ofFinEmbEquiv e).val = T := congrArg Subtype.val (Equiv.apply_symm_apply _ _)
      have hz := congrArg (fun g : (I → ℤ) [⋀^Fin n]→ₗ[ℤ] RationalResidue =>
        g (b ∘ e)) hf
      rw [curryLeft_weighted_basis, hS] at hz
      exact hz
    · unfold weightedBoundary
      apply sum_eq_zero
      intro i hi
      have hnot : i ∉ T := (mem_sdiff.mp hi).2
      rw [formCoordinates_card_ne_zero b f _ (by rw [card_insert_of_notMem hnot]; omega),
        nsmul_zero, smul_zero]

omit [Fintype I] in
private lemma circuitReadout_empty (f : Finset I → RationalResidue) (C : Finset I) :
    circuitReadout f C ∅ = ∑ i ∈ C, insertionSign (C.erase i) i • f (C.erase i) := by
  simp [circuitReadout, restrictionSign, shuffleSign]

/-- For a uniform matroid, the circuit and weighted boundary equations are the
two vanishing exterior operations on the corresponding alternating form. -/
theorem form_mem_weighted_iff {V : Type*} [Fintype V] (p : V → I) {n : ℕ}
    (hbases : ∀ B : Finset I, M.IsBase (B : Set I) ↔ B.card = n + 1)
    (hground : M.E = Set.univ) (hr : n + 1 ≤ Fintype.card I)
    (b : Module.Basis I ℤ (I → ℤ)) (a : (I → ℤ) →ₗ[ℤ] ℤ) (ha : ∀ i, a (b i) = 1)
    (f : (I → ℤ) [⋀^Fin (n + 1)]→ₗ[ℤ] RationalResidue) :
    formCoordinates b f ∈ weightedCircuitResidues M p ↔
      covectorWedge a f = 0 ∧
        f.curryLeft (∑ i, (univ.filter (fun x => p x = i)).card • b i) = 0 := by
  have hread (C : Set.powersetCard I (n + 2)) :
      covectorWedge a f (b ∘ ofFinEmbEquiv.symm C) =
        circuitReadout (formCoordinates b f) C.val ∅ := by
    classical
    let e := ofFinEmbEquiv.symm C
    change covectorWedge a f (b ∘ e) = _
    rw [basis_covectorWedge_apply, circuitReadout_empty]
    have hC : C.val = univ.map e.toEmbedding := by
      apply Finset.ext
      intro i
      change i ∈ C ↔ i ∈ univ.map e.toEmbedding
      rw [← Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem C i, mem_map]
      exact ⟨fun ⟨j, hj⟩ => ⟨j, mem_univ _, hj⟩, fun ⟨j, _, hj⟩ => ⟨j, hj⟩⟩
    rw [hC, sum_map]
    apply Fintype.sum_congr
    intro i
    have hS : (ofFinEmbEquiv e).val = C.val := congrArg Subtype.val (Equiv.apply_symm_apply _ _)
    have he : (ofFinEmbEquiv ((Fin.succAboveOrderEmb i).trans e)).val =
        C.val.erase (e i) := by
      rw [face_embedding_erase, hS]
    have hcard : (C.val.erase (e i)).card = n + 1 := by
      rw [← he]
      exact (ofFinEmbEquiv _).prop
    have hcoord :
        (basisFormEquiv b).symm f (ofFinEmbEquiv ((Fin.succAboveOrderEmb i).trans e)) =
          formCoordinates b f (C.val.erase (e i)) := by
      rw [formCoordinates, dite_eq_left hcard]
      exact congrArg ((basisFormEquiv b).symm f) (Subtype.ext he)
    rw [ha, one_smul, hS, ← hC, hcoord]
    rfl
  constructor
  · intro h
    refine ⟨?_, (weightedBoundary_formCoordinates p b f).mp h.2.1⟩
    apply (basisFormEquiv b).symm.injective
    rw [map_zero]
    funext S
    rw [basisFormEquiv_symm_apply, hread]
    have hC : M.IsCircuit (↑S.val : Set I) :=
      (circuit_iff_card hbases hground hr S.val).mpr S.prop
    exact h.2.2 ⟨S.val, hC⟩ ∅ ((contracted_basis_eq_empty hbases hC S.prop).mpr rfl)
  · rintro ⟨hc, hw⟩
    refine ⟨fun F hF => formCoordinates_card_ne_zero b f F
      (fun h => hF ((hbases F).mpr h)),
      (weightedBoundary_formCoordinates p b f).mpr hw, ?_⟩
    intro C T hT
    have hcard := (circuit_iff_card hbases hground hr C.val).mp C.prop
    rw [(contracted_basis_eq_empty hbases C.prop hcard).mp hT]
    let S : Set.powersetCard I (n + 2) := ⟨C.val, hcard⟩
    exact (hread S).symm.trans (by rw [hc]; rfl)

/-- Translate the uniform core residue group into the common kernel of
covector multiplication and insertion of the class-size vector. -/
noncomputable def uniformWeightedFormsEquiv {V : Type*} [Fintype V] (p : V → I) {n : ℕ}
    (hbases : ∀ B : Finset I, M.IsBase (B : Set I) ↔ B.card = n + 1)
    (hground : M.E = Set.univ) (hr : n + 1 ≤ Fintype.card I)
    (b : Module.Basis I ℤ (I → ℤ)) (a : (I → ℤ) →ₗ[ℤ] ℤ) (ha : ∀ i, a (b i) = 1) :
    ↥((covectorWedgeLinear (N := RationalResidue) (n := n + 1) a).ker ⊓
      (insertVector (∑ i, (univ.filter (fun x => p x = i)).card • b i)).ker) ≃ₗ[ℤ]
      weightedCircuitResidues M p := by
  classical
  let L := basisFormEquiv (N := RationalResidue) (n := n + 1) b
  have hrepr (g : weightedCircuitResidues M p) :
      formCoordinates b (L fun S => g.val S.val) = g.val := by
    funext F
    by_cases hF : F.card = n + 1
    · rw [formCoordinates, dite_eq_left hF]
      exact congrFun (L.symm_apply_apply (fun S => g.val S.val)) ⟨F, hF⟩
    · rw [formCoordinates, dite_eq_right hF, g.prop.1 F (fun h => hF ((hbases F).mp h))]
  refine {
    toFun := fun f => ⟨formCoordinates b f.val,
      (form_mem_weighted_iff p hbases hground hr b a ha f.val).mpr f.prop⟩
    invFun := fun g => ⟨L (fun S => g.val S.val),
      (form_mem_weighted_iff p hbases hground hr b a ha _).mp (by
        rw [hrepr g]
        exact g.prop)⟩
    left_inv := fun f => Subtype.ext (L.symm.injective (by
      change L.symm (L fun S => formCoordinates b f.val S.val) = L.symm f.val
      rw [L.symm_apply_apply]
      funext S
      rw [formCoordinates, dite_eq_left (show S.val.card = n + 1 from S.prop)]))
    right_inv := fun g => Subtype.ext (hrepr g)
    map_add' := fun f g => Subtype.ext (funext fun S => by
      by_cases h : S.card = n + 1 <;> simp [formCoordinates, h])
    map_smul' := fun d f => Subtype.ext (funext fun S => by
      by_cases h : S.card = n + 1 <;> simp [formCoordinates, h]) }

end D5.S3.Combinatorics.Matroids.UniformMatroidCircuitCoordinates
