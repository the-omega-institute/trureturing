/- GID: D5/S3/Combinatorics/Matroids/PuncturedCircuitCoordinates
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/PuncturedCircuitCoordinates
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: The circuit equations after omitting one basis of a uniform matroid. -/

module

public import D5.S3.Combinatorics.Matroids.ParallelCircuitObstruction

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

private lemma independent_iff
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
private lemma joined_readout (f : Finset I → RationalResidue) (hf : f H = 0)
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

end D5.S3.Combinatorics.Matroids.PuncturedCircuitCoordinates
