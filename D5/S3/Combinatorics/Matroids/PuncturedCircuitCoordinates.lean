/- GID: D5/S3/Combinatorics/Matroids/PuncturedCircuitCoordinates
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/PuncturedCircuitCoordinates
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: The circuit equations after omitting one basis of a uniform matroid. -/

module

public import D5.S3.Combinatorics.Matroids.UniformMatroidCircuitCoordinates

/-! Compare the signed circuit equations before and after deleting a uniform basis. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.PuncturedCircuitCoordinates

open Finset
open scoped Matroid
open RationalJointCircuitImage (RationalResidue)
open ParallelCircuitObstruction (weightedBoundary weightedCircuitResidues circuitReadout)
open CircuitCycleDecomposition (restrictionSign)
open OrderedCycleFactorization (shuffleSign sign_sq)
open D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)

set_option autoImplicit false

variable {I : Type*} [Fintype I] [LinearOrder I] {M : Matroid I} {H : Finset I} {r : ℕ}

lemma independent_iff
    (hH : H.card = r) (hr : r < Fintype.card I)
    (hbases : ∀ F : Finset I, M.IsBase (F : Set I) ↔ F.card = r ∧ F ≠ H)
    (F : Finset I) : M.Indep (F : Set I) ↔ F.card ≤ r ∧ F ≠ H := by
  constructor
  · intro hF
    obtain ⟨B, hB, hFB⟩ := hF.exists_isBase_superset
    let T := B.toFinite.toFinset
    have hT : (T : Set I) = B := Set.Finite.coe_toFinset _
    obtain ⟨hc, hne⟩ := (hbases T).mp (hT.symm ▸ hB)
    have hsub : F ⊆ T := Finset.coe_subset.mp (hT.symm ▸ hFB)
    refine ⟨(card_le_card hsub).trans_eq hc, fun heq => hne ?_⟩
    have hcard : T.card ≤ F.card := by rw [hc, heq, hH]
    exact (eq_of_subset_of_card_le hsub hcard).symm.trans heq
  · rintro ⟨hc, hne⟩
    rcases hc.eq_or_lt with heq | hlt
    · exact ((hbases F).mpr ⟨heq, hne⟩).indep
    · obtain ⟨B, hFB, _, hB⟩ :=
        exists_subsuperset_card_eq (subset_univ F) hlt.le (by simpa using hr.le)
      by_cases he : B = H
      · subst B
        obtain ⟨t, _, ht⟩ := exists_mem_notMem_of_card_lt_card
          (show H.card < (univ : Finset I).card by simpa [hH] using hr)
        obtain ⟨i, hi, hiF⟩ := exists_mem_notMem_of_card_lt_card (show F.card < H.card by omega)
        have hneB : insert t (H.erase i) ≠ H := fun heq => ht (heq ▸ mem_insert_self t _)
        have hcard : (insert t (H.erase i)).card = r := by
          rw [card_insert_of_notMem (fun hin => ht (mem_of_mem_erase hin)), card_erase_of_mem hi]
          have : 0 < H.card := card_pos.mpr ⟨i, hi⟩
          omega
        refine (((hbases _).mpr ⟨hcard, hneB⟩).indep.subset (Finset.coe_subset.mpr ?_))
        intro x hx
        exact mem_insert_of_mem (mem_erase.mpr ⟨fun heq => hiF (heq ▸ hx), hFB hx⟩)
      · exact (((hbases B).mpr ⟨hB, he⟩).indep.subset (Finset.coe_subset.mpr hFB))

private lemma circuits_iff
    (hH : H.card = r) (hr : r < Fintype.card I) (hground : M.E = Set.univ)
    (hbases : ∀ F : Finset I, M.IsBase (F : Set I) ↔ F.card = r ∧ F ≠ H)
    (C : Finset I) : M.IsCircuit (C : Set I) ↔ C = H ∨ (C.card = r + 1 ∧ ¬ H ⊆ C) := by
  have hInd := independent_iff hH hr hbases
  rw [Matroid.isCircuit_iff_forall_ssubset, Matroid.dep_iff, hground,
    and_iff_left (Set.subset_univ _), hInd]
  constructor
  · rintro ⟨hnot, hminimal⟩
    by_cases heq : C = H
    · exact Or.inl heq
    have hlt : r < C.card := by
      by_contra! hle
      exact hnot ⟨hle, heq⟩
    have hnotH : ¬ H ⊆ C := by
      intro hsub
      have hstrict : H ⊂ C := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm heq⟩
      exact ((hInd H).mp (hminimal (Finset.coe_ssubset.mpr hstrict))).2 rfl
    obtain ⟨i, hi⟩ := card_pos.mp (by omega : 0 < C.card)
    have hle := ((hInd _).mp (hminimal (Finset.coe_ssubset.mpr (erase_ssubset hi)))).1
    rw [card_erase_of_mem hi] at hle
    exact Or.inr ⟨by omega, hnotH⟩
  · intro h
    refine ⟨?_, ?_⟩
    · rcases h with rfl | ⟨hc, -⟩
      · exact fun hi => hi.2 rfl
      · exact fun hi => by have := hi.1; omega
    · intro B hB
      let F := B.toFinite.toFinset
      have hF : (F : Set I) = B := Set.Finite.coe_toFinset _
      have hsub := Finset.coe_ssubset.mp (hF.symm ▸ hB)
      have hlt := card_lt_card hsub
      rw [← hF, hInd]
      rcases h with rfl | ⟨hc, hnotH⟩
      · exact ⟨by omega, ne_of_lt hsub⟩
      · exact ⟨by omega, fun heq => hnotH (heq ▸ hsub.le)⟩

private lemma contracted_bases
    (hH : H.card = r) (hr : r < Fintype.card I) (hground : M.E = Set.univ)
    (hbases : ∀ F : Finset I, M.IsBase (F : Set I) ↔ F.card = r ∧ F ≠ H)
    {C : Finset I} (hC : M.IsCircuit (C : Set I)) (T : Finset I) :
    (M ／ (C : Set I)).IsBase (T : Set I) ↔
      (C = H ∧ ∃ t ∉ H, T = {t}) ∨ (C ≠ H ∧ T = ∅) := by
  obtain ⟨i, hi⟩ := hC.nonempty
  have hcBasis : M.IsBasis (↑(C.erase i) : Set I) (C : Set I) := by
    simpa only [coe_erase] using hC.sdiff_singleton_isBasis hi
  have hInd (F : Finset I) :
      (M ／ (C : Set I)).Indep (F : Set I) ↔
        (F ∪ C.erase i).card ≤ r ∧ F ∪ C.erase i ≠ H ∧ Disjoint C F := by
    rw [hcBasis.contract_indep_iff, ← coe_union, independent_iff hH hr hbases,
      disjoint_coe, and_assoc]
  have hsize (F : Finset I) (hd : Disjoint C F) :
      (F ∪ C.erase i).card = F.card + (C.card - 1) := by
    rw [card_union_of_disjoint (hd.symm.mono_right (erase_subset _ _)), card_erase_of_mem hi]
  have hIff := (circuits_iff hH hr hground hbases C).mp hC
  rcases hIff with hEq | ⟨hc, hnotH⟩
  · subst C
    have hsingle (t : I) (ht : t ∉ H) : (M ／ (H : Set I)).Indep ({t} : Set I) := by
      have hd : Disjoint H ({t} : Finset I) := disjoint_singleton_right.mpr ht
      rw [← coe_singleton, hInd, hsize _ hd, card_singleton, hH]
      refine ⟨by have := card_pos.mpr ⟨i, hi⟩; omega, ?_, hd⟩
      intro heq
      exact ht (heq ▸ mem_union_left _ (mem_singleton_self t))
    have hcard (F : Finset I) (hf : (M ／ (H : Set I)).Indep (F : Set I)) : F.card ≤ 1 := by
      obtain ⟨hc, -, hd⟩ := (hInd F).mp hf
      rw [hsize F hd, hH] at hc
      have hpos : 0 < r := hH ▸ card_pos.mpr ⟨i, hi⟩
      omega
    simp only [true_and, ne_eq, not_true_eq_false, false_and, or_false]
    constructor
    · intro hT
      have hne : T ≠ ∅ := by
        intro he
        obtain ⟨t, -, ht⟩ := exists_mem_notMem_of_card_lt_card
          (show H.card < (univ : Finset I).card by simpa [hH] using hr)
        have heq := hT.eq_of_subset_indep (hsingle t ht) (by simp [he])
        rw [he] at heq
        simp at heq
      have hpos : 0 < T.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hne)
      have hle := hcard T hT.indep
      obtain ⟨t, ht⟩ := card_eq_one.mp (show T.card = 1 by omega)
      have hd := ((hInd T).mp hT.indep).2.2
      exact ⟨t, disjoint_singleton_right.mp (ht ▸ hd), ht⟩
    · rintro ⟨t, ht, rfl⟩
      rw [coe_singleton]
      apply (hsingle t ht).isBase_of_maximal
      intro B hB hsub
      let F := B.toFinite.toFinset
      have hF : (F : Set I) = B := Set.Finite.coe_toFinset _
      have hs : ({t} : Finset I) ⊆ F := Finset.coe_subset.mp (hF.symm ▸ (by simpa using hsub))
      have he := eq_of_subset_of_card_le hs (by simpa using hcard F (hF.symm ▸ hB))
      rw [← hF, ← he, coe_singleton]
  · have hne : C ≠ H := fun he => hnotH (he ▸ Subset.rfl)
    simp only [ne_eq, hne, not_false_eq_true, false_and, true_and, false_or]
    have hempty (B : Set I) (hB : (M ／ (C : Set I)).Indep B) : B = ∅ := by
      let F := B.toFinite.toFinset
      have hF : (F : Set I) = B := Set.Finite.coe_toFinset _
      obtain ⟨hLe, -, hd⟩ := (hInd F).mp (hF.symm ▸ hB)
      rw [hsize F hd, hc] at hLe
      have hf : F = ∅ := card_eq_zero.mp (by omega)
      rw [← hF, hf, coe_empty]
    constructor
    · intro hT
      exact Finset.coe_inj.mp (by simpa using hempty _ hT.indep)
    · rintro rfl
      simpa using (Matroid.empty_indep (M ／ (C : Set I))).isBase_of_maximal
        (fun B hB _ => (hempty B hB).symm)

omit [Fintype I] in
private lemma joined_sign (H : Finset I) {t i : I} (ht : t ∉ H) (hi : i ∈ H) :
    insertionSign ((insert t H).erase i) i =
      (-1) ^ (H.filter (t < ·)).card * restrictionSign H i {t} := by
  have hne : i ≠ t := fun he => ht (he ▸ hi)
  rw [erase_insert_of_ne hne.symm]
  unfold restrictionSign shuffleSign insertionSign
  simp_rw [filter_singleton]
  have hs : (∑ a ∈ H.erase i, (if t < a then ({t} : Finset I) else ∅).card) =
      ((H.erase i).filter (t < ·)).card := by
    calc
      _ = ∑ a ∈ H.erase i, if t < a then (1 : ℕ) else 0 := by
        apply sum_congr rfl
        intro a _
        by_cases h : t < a <;> simp [h]
      _ = _ := by exact_mod_cast (Finset.sum_boole (R := ℕ) (t < ·) (H.erase i))
  rw [hs, filter_insert, ← pow_add, ← pow_add]
  have he : i ∉ H.erase i := notMem_erase _ _
  have ht' : t ∉ H.erase i := fun h => ht (mem_of_mem_erase h)
  split_ifs with hti
  · have hf : H.filter (t < ·) = insert i ((H.erase i).filter (t < ·)) := by
      conv_lhs => rw [← insert_erase hi]
      rw [filter_insert, ite_eq_left hti]
    rw [hf, card_insert_of_notMem (fun h => he (mem_filter.mp h).1),
      card_insert_of_notMem (fun h => ht' (mem_filter.mp h).1)]
    have hsum : (((H.erase i).filter (t < ·)).card + 1) +
        (((H.erase i).filter (· < i)).card + ((H.erase i).filter (t < ·)).card) =
        (((H.erase i).filter (· < i)).card + 1) + 2 * ((H.erase i).filter (t < ·)).card := by omega
    rw [hsum]
    simp only [pow_add, pow_mul]
    norm_num
  · have hf : H.filter (t < ·) = (H.erase i).filter (t < ·) := by
      conv_lhs => rw [← insert_erase hi]
      rw [filter_insert, ite_eq_right hti]
    rw [hf]
    have hsum : ((H.erase i).filter (t < ·)).card +
        (((H.erase i).filter (· < i)).card + ((H.erase i).filter (t < ·)).card) =
        ((H.erase i).filter (· < i)).card + 2 * ((H.erase i).filter (t < ·)).card := by omega
    rw [hsum]
    simp only [pow_add, pow_mul]
    norm_num

omit [Fintype I] in
lemma joined_readout (f : Finset I → RationalResidue) (hf : f H = 0)
    {t : I} (ht : t ∉ H) :
    circuitReadout f (insert t H) ∅ =
      (-1 : ℤ) ^ (H.filter (t < ·)).card • circuitReadout f H {t} := by
  unfold circuitReadout
  simp only [empty_union, restrictionSign, shuffleSign, filter_empty, card_empty,
    sum_const_zero, pow_zero, mul_one] at ⊢
  rw [sum_insert ht, erase_insert ht, hf, smul_zero, zero_add, smul_sum]
  apply sum_congr rfl
  intro i hi
  have hne : i ≠ t := fun h => ht (h ▸ hi)
  rw [singleton_union, smul_smul]
  change insertionSign ((insert t H).erase i) i • f ((insert t H).erase i) =
    ((-1) ^ (H.filter (t < ·)).card * restrictionSign H i {t}) • f (insert t (H.erase i))
  rw [← joined_sign H ht hi, erase_insert_of_ne hne.symm]

/-- Omitting the basis `H` adds precisely the condition `f H = 0` to the
uniform support, weighted boundary, and signed circuit equations. -/
theorem mem_weightedCircuitResidues_iff {V : Type*} [Fintype V] (p : V → I)
    (hH : H.card = r) (hr : r < Fintype.card I) (hground : M.E = Set.univ)
    (hbases : ∀ F : Finset I, M.IsBase (F : Set I) ↔ F.card = r ∧ F ≠ H)
    (f : Finset I → RationalResidue) :
    f ∈ weightedCircuitResidues M p ↔
      (∀ F : Finset I, F.card ≠ r → f F = 0) ∧ f H = 0 ∧
      (∀ R : Finset I, weightedBoundary p f R = 0) ∧
      ∀ C : Finset I, C.card = r + 1 → circuitReadout f C ∅ = 0 := by
  have hcir := circuits_iff hH hr hground hbases
  have hbase {C : Finset I} (hC : M.IsCircuit (C : Set I)) :=
    contracted_bases hH hr hground hbases hC
  constructor
  · intro hf
    have hvanish : f H = 0 := hf.1 H (fun h => ((hbases H).mp h).2 rfl)
    refine ⟨fun F h => hf.1 F (fun hF => h ((hbases F).mp hF).1), hvanish, hf.2.1, ?_⟩
    intro C hc
    by_cases hsub : H ⊆ C
    · obtain ⟨t, htC, htH⟩ := exists_mem_notMem_of_card_lt_card (show H.card < C.card by omega)
      have hC : C = insert t H :=
        (eq_of_subset_of_card_le (insert_subset htC hsub)
          (by rw [card_insert_of_notMem htH, hH, hc])).symm
      have hHC : M.IsCircuit (H : Set I) := (hcir H).mpr (Or.inl rfl)
      rw [hC, joined_readout f hvanish htH,
        hf.2.2 ⟨H, hHC⟩ {t} ((hbase hHC {t}).mpr (Or.inl ⟨rfl, t, htH, rfl⟩)), smul_zero]
    · have hC : M.IsCircuit (C : Set I) := (hcir C).mpr (Or.inr ⟨hc, hsub⟩)
      have hne : C ≠ H := fun heq => hsub (heq ▸ Subset.rfl)
      exact hf.2.2 ⟨C, hC⟩ ∅ ((hbase hC ∅).mpr (Or.inr ⟨hne, rfl⟩))
  · rintro ⟨hs, hHf, hw, hc⟩
    refine ⟨?_, hw, ?_⟩
    · intro F hF
      by_cases he : F = H
      · exact he.symm ▸ hHf
      · exact hs F (fun h => hF ((hbases F).mpr ⟨h, he⟩))
    · intro C T hT
      rcases (hbase C.prop T).mp hT with ⟨he, t, ht, rfl⟩ | ⟨hne, rfl⟩
      · rw [he]
        have hrw := joined_readout f hHf ht
        rw [hc _ (by rw [card_insert_of_notMem ht, hH])] at hrw
        let s : ℤ := (-1) ^ (H.filter (t < ·)).card
        calc
          circuitReadout f H {t} = s • (s • circuitReadout f H {t}) := by
            rw [smul_smul, sign_sq, one_smul]
          _ = 0 := by rw [← hrw, smul_zero]
      · rcases (hcir C.val).mp C.prop with he | ⟨hca, -⟩
        · exact (hne he).elim
        · exact hc C.val hca

open UniformMatroidCircuitCoordinates (circuit_iff_card contracted_basis_eq_empty
  uniformWeightedFormsEquiv)
open UniformCircuitResidueForms (covectorWedgeLinear insertVector formCoordinates)

private noncomputable def uniformCore (hH : H.card = r) : Matroid I := by
  refine Matroid.ofExistsFiniteIsBase Set.univ (fun S : Set I => S.ncard = r)
    ⟨(H : Set I), by simpa using hH, H.finite_toSet⟩ ?_ (fun _ _ => Set.subset_univ _)
  intro B C hB hC i hi
  have hnot : ¬ C ⊆ B := fun hsub => by
    have heq := Set.eq_of_subset_of_ncard_le hsub (hB.trans hC.symm).le
    exact hi.2 (heq.symm ▸ hi.1)
  obtain ⟨t, htC, htB⟩ := Set.not_subset.mp hnot
  exact ⟨t, ⟨htC, htB⟩, (Set.ncard_exchange htB hi.1).trans hB⟩

private lemma uniform_support_and_readout (hH : H.card = r) (hr : r < Fintype.card I)
    {V : Type*} [Fintype V] (p : V → I) (f : Finset I → RationalResidue) :
    f ∈ weightedCircuitResidues (uniformCore (H := H) hH) p ↔
      (∀ F : Finset I, F.card ≠ r → f F = 0) ∧
      (∀ R : Finset I, weightedBoundary p f R = 0) ∧
      ∀ C : Finset I, C.card = r + 1 → circuitReadout f C ∅ = 0 := by
  let U := uniformCore (H := H) hH
  have hbases (F : Finset I) : U.IsBase (F : Set I) ↔ F.card = r := by
    change (F : Set I).ncard = r ↔ F.card = r
    rw [Set.ncard_coe_finset]
  have hground : U.E = Set.univ := rfl
  have hcir := circuit_iff_card hbases hground hr.le
  have hcon {C : Finset I} (hC : U.IsCircuit (C : Set I)) (T : Finset I) :=
    contracted_basis_eq_empty (T := T) hbases hC ((hcir C).mp hC)
  constructor
  · intro hf
    refine ⟨fun F hF => hf.1 F (fun h => hF ((hbases F).mp h)), hf.2.1, ?_⟩
    intro C hC
    have h := (hcir C).mpr hC
    exact hf.2.2 ⟨C, h⟩ ∅ ((hcon h ∅).mpr rfl)
  · rintro ⟨hs, hw, hc⟩
    refine ⟨fun F hF => hs F (fun h => hF ((hbases F).mpr h)), hw, ?_⟩
    intro C T hT
    rw [(hcon C.prop T).mp hT]
    exact hc C.val ((hcir C.val).mp C.prop)

/-- Transport the punctured residue equations to uniform alternating forms with
one specified coordinate set to zero. -/
theorem punctured_weighted_forms_equiv {V : Type*} [Fintype V] (p : V → I) {n : ℕ}
    (hH : H.card = n + 1) (hr : n + 1 < Fintype.card I) (hground : M.E = Set.univ)
    (hbases : ∀ F : Finset I, M.IsBase (F : Set I) ↔ F.card = n + 1 ∧ F ≠ H)
    (b : Module.Basis I ℤ (I → ℤ)) (a : (I → ℤ) →ₗ[ℤ] ℤ) (ha : ∀ i, a (b i) = 1) :
    Nonempty (weightedCircuitResidues M p ≃ₗ[ℤ]
      ↥(LinearMap.ker
        (show ↥((covectorWedgeLinear (N := RationalResidue) (n := n + 1) a).ker ⊓
          (insertVector (∑ i, (univ.filter fun x => p x = i).card • b i)).ker) →ₗ[ℤ]
              RationalResidue from
          { toFun := fun f => formCoordinates b f.val H
            map_add' := fun f g => by simp [formCoordinates, hH]
            map_smul' := fun d f => by simp [formCoordinates, hH] }))) := by
  let U := uniformCore (H := H) hH
  have hUbase (F : Finset I) : U.IsBase (F : Set I) ↔ F.card = n + 1 := by
    change (F : Set I).ncard = n + 1 ↔ F.card = n + 1
    rw [Set.ncard_coe_finset]
  let forms := uniformWeightedFormsEquiv (M := U) p hUbase rfl hr.le b a ha
  have hmem (f : Finset I → RationalResidue) :
      f ∈ weightedCircuitResidues M p ↔ f ∈ weightedCircuitResidues U p ∧ f H = 0 := by
    rw [mem_weightedCircuitResidues_iff p hH hr hground hbases,
      uniform_support_and_readout hH hr p f]
    tauto
  let K : Submodule ℤ (weightedCircuitResidues U p) :=
    (LinearMap.proj (R := ℤ) H).comp (weightedCircuitResidues U p).subtype |>.ker
  let lift := (weightedCircuitResidues M p).subtype.codRestrict
    (weightedCircuitResidues U p) (fun f => ((hmem f.val).mp f.prop).1)
  let liftK := lift.codRestrict K (fun f => ((hmem f.val).mp f.prop).2)
  have hBij : Function.Bijective liftK := by
    refine ⟨fun f g h => Subtype.ext (congrArg (fun z : K => z.val.val) h), ?_⟩
    intro f
    exact ⟨⟨f.val.val, (hmem f.val.val).mpr ⟨f.val.prop, f.prop⟩⟩, rfl⟩
  refine ⟨(LinearEquiv.ofBijective liftK hBij).trans (forms.symm.ofSubmodules K _ ?_)⟩
  ext f
  change (∃ g : weightedCircuitResidues U p, g.val H = 0 ∧ forms.symm g = f) ↔
    formCoordinates b f.val H = 0
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (congrArg (fun z : weightedCircuitResidues U p => z.val H)
      (forms.apply_symm_apply g)).trans hg
  · intro hf
    exact ⟨forms f, hf, forms.symm_apply_apply f⟩

open UniformCircuitResidueForms (basisFormEquiv basisFormEquiv_symm_apply
  curryLeft_basis_insert pivotFormEquiv)
open Set.powersetCard (ofFinEmbEquiv)

omit [Fintype I] in
private lemma pivot_coordinate_zero_iff {n : ℕ} (hH : H.card = n + 1) {j : I} (hj : j ∈ H)
    (b : Module.Basis I ℤ (I → ℤ))
    (f : (I → ℤ) [⋀^Fin (n + 1)]→ₗ[ℤ] RationalResidue) :
    formCoordinates b f H = 0 ↔
      formCoordinates b (f.curryLeft (b j)) (H.erase j) = 0 := by
  have hs : (H.erase j).card = n := by rw [card_erase_of_mem hj, hH, Nat.add_sub_cancel]
  let S : Set.powersetCard I n := ⟨H.erase j, hs⟩
  let e := ofFinEmbEquiv.symm S
  have he : ofFinEmbEquiv e = S := Equiv.apply_symm_apply _ _
  have hj' : j ∉ ofFinEmbEquiv e := by rw [he]; exact notMem_erase _ _
  have hv := curryLeft_basis_insert b f j e hj'
  rw [← basisFormEquiv_symm_apply] at hv
  have hinsert : (⟨insert j (ofFinEmbEquiv e).val, by
      change (insert j (ofFinEmbEquiv e).val).card = n + 1
      rw [card_insert_of_notMem hj', (ofFinEmbEquiv e).prop]⟩ :
        Set.powersetCard I (n + 1)) = ⟨H, hH⟩ := by
    apply Subtype.ext
    change insert j (ofFinEmbEquiv e).val = H
    rw [he]
    exact insert_erase hj
  rw [hinsert] at hv
  rw [he] at hv
  let sign := insertionSign (H.erase j) j
  have hval : formCoordinates b (f.curryLeft (b j)) (H.erase j) =
      sign • formCoordinates b f H := by
    rw [formCoordinates, dite_eq_left hs, formCoordinates, dite_eq_left hH]
    exact hv
  rw [hval]
  constructor
  · intro h
    rw [h, smul_zero]
  · intro h
    change ((-1 : ℤ) ^ ((H.erase j).filter (· < j)).card) •
      formCoordinates b f H = 0 at h
    have h' := congrArg (((-1 : ℤ) ^ ((H.erase j).filter (· < j)).card) • ·) h
    rwa [smul_smul, sign_sq, one_smul, smul_zero] at h'

/-- With the pivot in the omitted basis, the missing coefficient becomes a
specified coefficient of the form of degree one lower. -/
theorem punctured_pivot_forms_equiv {V : Type*} [Fintype V] (p : V → I) {n : ℕ}
    (hH : H.card = n + 2) (hr : n + 2 < Fintype.card I) (hground : M.E = Set.univ)
    (hbases : ∀ F : Finset I, M.IsBase (F : Set I) ↔ F.card = n + 2 ∧ F ≠ H)
    (b : Module.Basis I ℤ (I → ℤ)) (a : (I → ℤ) →ₗ[ℤ] ℤ) (ha : ∀ i, a (b i) = 1)
    (j : I) (hj : j ∈ H) :
    let y := ∑ i, (univ.filter fun x => p x = i).card • b i
    let P := ((insertVector (N := RationalResidue) (n := n) (b j)).ker ⊓
      (insertVector y).ker) ⊓
      Submodule.torsionBy ℤ ((I → ℤ) [⋀^Fin (n + 1)]→ₗ[ℤ] RationalResidue) (a y)
    Nonempty (weightedCircuitResidues M p ≃ₗ[ℤ] ↥(LinearMap.ker
      (show P →ₗ[ℤ] RationalResidue from
        { toFun := fun f => formCoordinates b f.val (H.erase j)
          map_add' := fun f g => by
            have hs : (H.erase j).card = n + 1 := by rw [card_erase_of_mem hj, hH]; omega
            simp [formCoordinates, hs]
          map_smul' := fun d f => by
            have hs : (H.erase j).card = n + 1 := by rw [card_erase_of_mem hj, hH]; omega
            simp [formCoordinates, hs] }))) := by
  dsimp only
  obtain ⟨forms⟩ := punctured_weighted_forms_equiv p hH hr hground hbases b a ha
  let y := ∑ i, (univ.filter fun x => p x = i).card • b i
  let P := (((insertVector (N := RationalResidue) (n := n) (b j)).ker ⊓
    (insertVector y).ker) ⊓
    Submodule.torsionBy ℤ ((I → ℤ) [⋀^Fin (n + 1)]→ₗ[ℤ] RationalResidue) (a y))
  let pivot := pivotFormEquiv (N := RationalResidue) (n := n) a (b j) y (ha j)
  refine ⟨forms.trans (pivot.ofSubmodules _ _ ?_)⟩
  rw [Submodule.map_equiv_eq_comap_symm]
  apply Submodule.ext
  intro f
  change formCoordinates b (pivot.symm f).val H = 0 ↔
    formCoordinates b f.val (H.erase j) = 0
  have h := pivot_coordinate_zero_iff hH hj b (pivot.symm f).val
  have hf : (pivot.symm f).val.curryLeft (b j) = f.val :=
    congrArg (fun z : P => z.val) (pivot.apply_symm_apply f)
  rw [hf] at h
  exact h

end D5.S3.Combinatorics.Matroids.PuncturedCircuitCoordinates
