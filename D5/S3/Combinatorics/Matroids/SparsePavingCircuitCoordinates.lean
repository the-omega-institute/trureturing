/- GID: D5/S3/Combinatorics/Matroids/SparsePavingCircuitCoordinates
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/SparsePavingCircuitCoordinates
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Circuit equations with a family of omitted uniform bases. -/

module

public import D5.S3.Combinatorics.Matroids.PuncturedCircuitCoordinates
public import D5.S3.Combinatorics.Matroids.PuncturedCircuitSplit

/-! Separation of the omitted bases in the signed circuit comparison. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.SparsePavingCircuitCoordinates

open Finset
open scoped Matroid

set_option autoImplicit false

variable {I : Type*} [Fintype I] [LinearOrder I] {M : Matroid I}
variable {holes : Set (Finset I)} {r : ℕ}

private lemma extending_base_exists (hr : r < Fintype.card I)
    (hsparse : holes.Pairwise (fun H K => (H ∩ K).card + 2 ≤ r))
    (F : Finset I) (hf : F.card < r) :
    ∃ B : Finset I, F ⊆ B ∧ B.card = r ∧ B ∉ holes := by
  obtain ⟨B, hFB, _, hBc⟩ :=
    exists_subsuperset_card_eq (subset_univ F) hf.le (by simpa using hr.le)
  by_cases hB : B ∈ holes
  · obtain ⟨t, _, ht⟩ := exists_mem_notMem_of_card_lt_card
      (show B.card < (univ : Finset I).card by simpa [hBc] using hr)
    obtain ⟨j, hj, hjF⟩ := exists_mem_notMem_of_card_lt_card (show F.card < B.card by omega)
    let K := insert t (B.erase j)
    have hBK : B ≠ K := fun he => ht (he.symm ▸ mem_insert_self t _)
    have hsub : F ⊆ K := by
      intro i hi
      exact mem_insert_of_mem (mem_erase.mpr ⟨fun h => hjF (h ▸ hi), hFB hi⟩)
    have hcardK : K.card = r := by
      change (insert t (B.erase j)).card = r
      rw [card_insert_of_notMem (fun h => ht (mem_of_mem_erase h)), card_erase_of_mem hj, hBc]
      omega
    refine ⟨K, hsub, hcardK, fun hK => ?_⟩
    have hlarge := hsparse hB hK hBK
    have hsmall := card_le_card (subset_inter (erase_subset j B)
      (show B.erase j ⊆ K from subset_insert _ _))
    rw [card_erase_of_mem hj, hBc] at hsmall
    omega
  · exact ⟨B, hFB, hBc, hB⟩

private lemma indep_iff_card_and_allowed (hr : r < Fintype.card I)
    (hsize : ∀ H ∈ holes, H.card = r)
    (hsparse : holes.Pairwise (fun H K => (H ∩ K).card + 2 ≤ r))
    (hB : ∀ B : Finset I, M.IsBase (B : Set I) ↔ B.card = r ∧ B ∉ holes)
    (F : Finset I) : M.Indep (F : Set I) ↔ F.card ≤ r ∧ F ∉ holes := by
  constructor
  · intro hf
    obtain ⟨B, hbase, hsub⟩ := hf.exists_isBase_superset
    let T := B.toFinite.toFinset
    have hT : (T : Set I) = B := Set.Finite.coe_toFinset _
    obtain ⟨hcard, hallowed⟩ := (hB T).mp (hT.symm ▸ hbase)
    have hFT : F ⊆ T := Finset.coe_subset.mp (hT.symm ▸ hsub)
    refine ⟨(card_le_card hFT).trans_eq hcard, fun h => ?_⟩
    have he := eq_of_subset_of_card_le hFT (hcard.trans (hsize F h).symm).le
    exact hallowed (he ▸ h)
  · rintro ⟨hcard, hF⟩
    rcases hcard.eq_or_lt with he | hlt
    · exact ((hB F).mpr ⟨he, hF⟩).indep
    · obtain ⟨B, hsub, hsize, hallowed⟩ := extending_base_exists hr hsparse F hlt
      exact ((hB B).mpr ⟨hsize, hallowed⟩).indep.subset (Finset.coe_subset.mpr hsub)

omit [Fintype I] in
private lemma hole_unique_in_succ (hsize : ∀ H ∈ holes, H.card = r)
    (hsparse : holes.Pairwise (fun H K => (H ∩ K).card + 2 ≤ r))
    {C H K : Finset I} (hC : C.card = r + 1) (hH : H ∈ holes) (hK : K ∈ holes)
    (hHC : H ⊆ C) (hKC : K ⊆ C) : H = K := by
  by_contra hne
  have hsep := hsparse hH hK hne
  have hunion := card_le_card (union_subset hHC hKC)
  have hcount := card_union_add_card_inter H K
  rw [hsize H hH, hsize K hK] at hcount
  omega

private lemma circuits_iff_omitted_or_large (hr : r < Fintype.card I)
    (hsize : ∀ H ∈ holes, H.card = r)
    (hsparse : holes.Pairwise (fun H K => (H ∩ K).card + 2 ≤ r))
    (hground : M.E = Set.univ)
    (hB : ∀ B : Finset I, M.IsBase (B : Set I) ↔ B.card = r ∧ B ∉ holes)
    (C : Finset I) :
    M.IsCircuit (C : Set I) ↔ C ∈ holes ∨ (C.card = r + 1 ∧ ∀ H ∈ holes, ¬ H ⊆ C) := by
  have hind := indep_iff_card_and_allowed hr hsize hsparse hB
  rw [Matroid.isCircuit_iff_forall_ssubset, Matroid.dep_iff, hground,
    and_iff_left (Set.subset_univ _), hind]
  constructor
  · rintro ⟨hdep, hminimal⟩
    by_cases hC : C ∈ holes
    · exact Or.inl hC
    have hlt : r < C.card := by
      by_contra! hcr
      exact hdep ⟨hcr, hC⟩
    have hav (H : Finset I) (hH : H ∈ holes) : ¬ H ⊆ C := by
      intro hsub
      have hne : H ≠ C := fun h => hC (h ▸ hH)
      have hs := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
      exact ((hind H).mp (hminimal (Finset.coe_ssubset.mpr hs))).2 hH
    obtain ⟨i, hi⟩ := card_pos.mp (by omega : 0 < C.card)
    have hle := ((hind _).mp (hminimal (Finset.coe_ssubset.mpr (erase_ssubset hi)))).1
    rw [card_erase_of_mem hi] at hle
    exact Or.inr ⟨by omega, hav⟩
  · intro h
    refine ⟨?_, ?_⟩
    · rcases h with hC | ⟨hC, -⟩
      · exact fun hi => hi.2 hC
      · exact fun hi => by have := hi.1; omega
    · intro B hproper
      let F := B.toFinite.toFinset
      have hF : (F : Set I) = B := Set.Finite.coe_toFinset _
      have hsub := Finset.coe_ssubset.mp (hF.symm ▸ hproper)
      have hlt := card_lt_card hsub
      rw [← hF, hind]
      rcases h with hC | ⟨hC, hav⟩
      · have hc := hsize C hC
        exact ⟨by omega, fun h => by have := hsize F h; omega⟩
      · exact ⟨by omega, fun h => hav F h hsub.le⟩

private lemma contracted_bases
    (hr : r < Fintype.card I) (hsize : ∀ H ∈ holes, H.card = r)
    (hsparse : holes.Pairwise (fun H K => (H ∩ K).card + 2 ≤ r))
    (hground : M.E = Set.univ)
    (hB : ∀ B : Finset I, M.IsBase (B : Set I) ↔ B.card = r ∧ B ∉ holes)
    {C : Finset I} (hC : M.IsCircuit (C : Set I)) (T : Finset I) :
    (M ／ (C : Set I)).IsBase (T : Set I) ↔
      (C ∈ holes ∧ ∃ t ∉ C, T = {t}) ∨ (C ∉ holes ∧ T = ∅) := by
  obtain ⟨j, hj⟩ := hC.nonempty
  have hJ : M.IsBasis (↑(C.erase j) : Set I) (C : Set I) := by
    simpa only [coe_erase] using hC.sdiff_singleton_isBasis hj
  have hind (F : Finset I) :
      (M ／ (C : Set I)).Indep (F : Set I) ↔
        (F ∪ C.erase j).card ≤ r ∧ F ∪ C.erase j ∉ holes ∧ Disjoint C F := by
    rw [hJ.contract_indep_iff, ← coe_union, indep_iff_card_and_allowed hr hsize hsparse hB,
      disjoint_coe, and_assoc]
  have hcard (F : Finset I) (hd : Disjoint C F) :
      (F ∪ C.erase j).card = F.card + (C.card - 1) := by
    rw [card_union_of_disjoint (hd.symm.mono_right (erase_subset _ _)), card_erase_of_mem hj]
  rcases (circuits_iff_omitted_or_large hr hsize hsparse hground hB C).mp hC with h | ⟨hc, hav⟩
  · have hc := hsize C h
    have hsingle (t : I) (ht : t ∉ C) : (M ／ (C : Set I)).Indep ({t} : Set I) := by
      have hd : Disjoint C ({t} : Finset I) := disjoint_singleton_right.mpr ht
      rw [← coe_singleton, hind, hcard _ hd, card_singleton, hc]
      refine ⟨by have := card_pos.mpr ⟨j, hj⟩; omega, ?_, hd⟩
      intro hK
      let K := ({t} : Finset I) ∪ C.erase j
      have hKC : K ⊆ insert t C := by
        change ({t} : Finset I) ∪ C.erase j ⊆ insert t C
        rw [singleton_union]
        exact insert_subset (mem_insert_self _ _) ((erase_subset _ _).trans (subset_insert _ _))
      have hcen : (insert t C).card = r + 1 := by rw [card_insert_of_notMem ht, hc]
      have he := hole_unique_in_succ hsize hsparse hcen h hK (subset_insert _ _) hKC
      exact ht (he ▸ mem_union_left (C.erase j) (mem_singleton_self t))
    have hle (F : Finset I) (hF : (M ／ (C : Set I)).Indep (F : Set I)) : F.card ≤ 1 := by
      obtain ⟨hLe, _, hd⟩ := (hind F).mp hF
      rw [hcard F hd, hc] at hLe
      have hpos : 0 < r := hc ▸ card_pos.mpr ⟨j, hj⟩
      omega
    simp only [h, true_and, not_true_eq_false, false_and, or_false]
    constructor
    · intro hT
      have hne : T ≠ ∅ := by
        intro he
        obtain ⟨t, -, ht⟩ := exists_mem_notMem_of_card_lt_card
          (show C.card < (univ : Finset I).card by simpa [hc] using hr)
        have heq := hT.eq_of_subset_indep (hsingle t ht) (by simp [he])
        rw [he] at heq
        simp at heq
      have hpos : 0 < T.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hne)
      obtain ⟨t, ht⟩ := card_eq_one.mp (show T.card = 1 by have := hle T hT.indep; omega)
      have hd := ((hind T).mp hT.indep).2.2
      exact ⟨t, disjoint_singleton_right.mp (ht ▸ hd), ht⟩
    · rintro ⟨t, ht, rfl⟩
      rw [coe_singleton]
      apply (hsingle t ht).isBase_of_maximal
      intro B hB hsub
      let F := B.toFinite.toFinset
      have hF : (F : Set I) = B := Set.Finite.coe_toFinset _
      have hs : ({t} : Finset I) ⊆ F := Finset.coe_subset.mp (hF.symm ▸ (by simpa using hsub))
      have he := eq_of_subset_of_card_le hs (by simpa using hle F (hF.symm ▸ hB))
      rw [← hF, ← he, coe_singleton]
  · have h : C ∉ holes := fun hm => by have := hsize C hm; omega
    simp only [h, false_and, not_false_eq_true, true_and, false_or]
    have hempty (B : Set I) (hB : (M ／ (C : Set I)).Indep B) : B = ∅ := by
      let F := B.toFinite.toFinset
      have hF : (F : Set I) = B := Set.Finite.coe_toFinset _
      obtain ⟨hl, _, hd⟩ := (hind F).mp (hF.symm ▸ hB)
      rw [hcard F hd, hc] at hl
      have hf : F = ∅ := card_eq_zero.mp (by omega)
      rw [← hF, hf, coe_empty]
    constructor
    · intro hT
      exact Finset.coe_inj.mp (by simpa using hempty _ hT.indep)
    · rintro rfl
      simpa using (Matroid.empty_indep (M ／ (C : Set I))).isBase_of_maximal
        (fun B hB _ => (hempty B hB).symm)

open RationalJointCircuitImage (RationalResidue)
open ParallelCircuitObstruction (weightedBoundary weightedCircuitResidues circuitReadout)
open PuncturedCircuitCoordinates (joined_readout)
open OrderedCycleFactorization (sign_sq)

/-- For pairwise separated omitted bases, the circuit equations are the
uniform deletion rows with the coefficient of each omitted basis set to zero. -/
theorem mem_weightedCircuitResidues_iff {V : Type*} [Fintype V] (p : V → I)
    (hr : r < Fintype.card I) (hsize : ∀ H ∈ holes, H.card = r)
    (hsparse : holes.Pairwise (fun H K => (H ∩ K).card + 2 ≤ r)) (hground : M.E = Set.univ)
    (hB : ∀ B : Finset I, M.IsBase (B : Set I) ↔ B.card = r ∧ B ∉ holes)
    (f : Finset I → RationalResidue) :
    f ∈ weightedCircuitResidues M p ↔
      (∀ F : Finset I, F.card ≠ r → f F = 0) ∧ (∀ H ∈ holes, f H = 0) ∧
      (∀ R : Finset I, weightedBoundary p f R = 0) ∧
      ∀ C : Finset I, C.card = r + 1 → circuitReadout f C ∅ = 0 := by
  classical
  have hcir := circuits_iff_omitted_or_large hr hsize hsparse hground hB
  have hbase {C : Finset I} (hC : M.IsCircuit (C : Set I)) :=
    contracted_bases hr hsize hsparse hground hB hC
  constructor
  · intro hf
    have hvanish (H : Finset I) (hH : H ∈ holes) : f H = 0 :=
      hf.1 H (fun h => ((hB H).mp h).2 hH)
    refine ⟨fun F h => hf.1 F (fun hF => h ((hB F).mp hF).1), hvanish, hf.2.1, ?_⟩
    intro C hC
    by_cases hav : ∀ H ∈ holes, ¬ H ⊆ C
    · have hc := (hcir C).mpr (Or.inr ⟨hC, hav⟩)
      have hnot : C ∉ holes := fun h => by have := hsize C h; omega
      exact hf.2.2 ⟨C, hc⟩ ∅ ((hbase hc ∅).mpr (Or.inr ⟨hnot, rfl⟩))
    · push Not at hav
      obtain ⟨H, hH, hsub⟩ := hav
      obtain ⟨t, htC, htH⟩ := exists_mem_notMem_of_card_lt_card
        (show H.card < C.card by rw [hsize H hH, hC]; omega)
      have he : C = insert t H := (eq_of_subset_of_card_le (insert_subset htC hsub)
        (by rw [card_insert_of_notMem htH, hsize H hH, hC])).symm
      have hHC := (hcir H).mpr (Or.inl hH)
      rw [he, joined_readout f (hvanish H hH) htH,
        hf.2.2 ⟨H, hHC⟩ {t} ((hbase hHC {t}).mpr (Or.inl ⟨hH, t, htH, rfl⟩)), smul_zero]
  · rintro ⟨hs, hz, hw, hc⟩
    refine ⟨?_, hw, ?_⟩
    · intro F hF
      by_cases h : F ∈ holes
      · exact hz F h
      · exact hs F (fun he => hF ((hB F).mpr ⟨he, h⟩))
    · intro C T hT
      rcases (hbase C.prop T).mp hT with ⟨hmem, t, ht, rfl⟩ | ⟨hnot, rfl⟩
      · have hrow := joined_readout f (hz C.val hmem) ht
        rw [hc _ (by rw [card_insert_of_notMem ht, hsize C.val hmem])] at hrow
        let s : ℤ := (-1) ^ (C.val.filter (t < ·)).card
        calc
          circuitReadout f C.val {t} = s • (s • circuitReadout f C.val {t}) := by
            rw [smul_smul, sign_sq, one_smul]
          _ = 0 := by rw [← hrow, smul_zero]
      · rcases (hcir C.val).mp C.prop with h | ⟨hcard, _⟩
        · exact (hnot h).elim
        · exact hc C.val hcard

open PuncturedCircuitCoordinates (uniformCore uniform_support_and_readout)
open UniformCircuitResidueForms (covectorWedgeLinear insertVector formCoordinates)
open UniformMatroidCircuitCoordinates (uniformWeightedFormsEquiv)
open PuncturedCircuitSplit (coefficient)

/-- The conditions that all coefficients at the omitted bases vanish. -/
noncomputable def omitCoefficients (b : Module.Basis I ℤ (I → ℤ))
    (holes : Set (Finset I)) (rank : ℕ) :
    Submodule ℤ ((I → ℤ) [⋀^Fin rank]→ₗ[ℤ] RationalResidue) :=
  ⨅ H : holes, (coefficient b (H : Finset I)).ker

/-- The residue group is the common kernel of the two exterior operations with
one vanishing coefficient for each omitted basis. -/
theorem sparse_paving_weighted_forms_equiv {V : Type*} [Fintype V] (p : V → I)
    {d : ℕ}
    (hd : d + 1 < Fintype.card I)
    (hsize : ∀ H ∈ holes, H.card = d + 1)
    (hsparse : holes.Pairwise (fun H K => (H ∩ K).card + 2 ≤ d + 1))
    (hground : M.E = Set.univ)
    (hB : ∀ B : Finset I, M.IsBase (B : Set I) ↔ B.card = d + 1 ∧ B ∉ holes)
    (b : Module.Basis I ℤ (I → ℤ)) (a : (I → ℤ) →ₗ[ℤ] ℤ) (ha : ∀ i, a (b i) = 1) :
    Nonempty (weightedCircuitResidues M p ≃ₗ[ℤ]
      ↥(((covectorWedgeLinear (N := RationalResidue) (n := d + 1) a).ker ⊓
        (insertVector (∑ i, (univ.filter fun x => p x = i).card • b i)).ker) ⊓
        omitCoefficients b holes (d + 1))) := by
  classical
  obtain ⟨H, _, hH⟩ := exists_subset_card_eq (s := (univ : Finset I))
    (n := d + 1) (by simpa using hd.le)
  let U := uniformCore (H := H) hH
  have hUbase (F : Finset I) : U.IsBase (F : Set I) ↔ F.card = d + 1 := by
    change (F : Set I).ncard = d + 1 ↔ F.card = d + 1
    rw [Set.ncard_coe_finset]
  have hread (f : Finset I → RationalResidue) :
      f ∈ weightedCircuitResidues M p ↔
        f ∈ weightedCircuitResidues U p ∧ (∀ H ∈ holes, f H = 0) := by
    rw [mem_weightedCircuitResidues_iff p hd hsize hsparse hground hB,
      uniform_support_and_readout hH hd p f]
    tauto
  let P := ((covectorWedgeLinear (N := RationalResidue) (n := d + 1) a).ker ⊓
    (insertVector (∑ i, (univ.filter fun x => p x = i).card • b i)).ker)
  let formEq : P ≃ₗ[ℤ] weightedCircuitResidues U p :=
    uniformWeightedFormsEquiv (M := U) p hUbase rfl hd.le b a ha
  let K := P ⊓ omitCoefficients b holes (d + 1)
  have hcoeff (f : _) : f ∈ omitCoefficients b holes (d + 1) ↔
      ∀ H ∈ holes, formCoordinates b f H = 0 := by
    rw [omitCoefficients, Submodule.mem_iInf]
    exact ⟨fun h H hh => h ⟨H, hh⟩, fun h H => h H.val H.prop⟩
  let read (f : weightedCircuitResidues M p) : weightedCircuitResidues U p :=
    ⟨f.val, ((hread f.val).mp f.prop).1⟩
  let into (f : weightedCircuitResidues M p) : K := ⟨(formEq.symm (read f)).val, by
    refine ⟨(formEq.symm (read f)).prop, (hcoeff _).mpr ?_⟩
    intro H hH
    have he := congrArg (fun g : weightedCircuitResidues U p => g.val H)
      (formEq.apply_symm_apply (read f))
    exact he.trans (((hread f.val).mp f.prop).2 H hH)⟩
  let out (f : K) : weightedCircuitResidues M p := by
    let y := formEq ⟨f.val, f.prop.1⟩
    exact ⟨y.val, (hread y.val).mpr ⟨y.prop, (hcoeff _).mp f.prop.2⟩⟩
  refine ⟨{
    toFun := into
    invFun := out
    left_inv := fun f => Subtype.ext (congrArg
      (fun g : weightedCircuitResidues U p => g.val) (formEq.apply_symm_apply (read f)))
    right_inv := fun f => Subtype.ext (congrArg
      (fun g : P => g.val) (formEq.symm_apply_apply ⟨f.val, f.prop.1⟩))
    map_add' := by
      intro f g
      apply Subtype.ext
      exact congrArg (fun g : P => g.val) (map_add formEq.symm (read f) (read g))
    map_smul' := by
      intro t f
      apply Subtype.ext
      exact congrArg (fun g : P => g.val) (map_smul formEq.symm t (read f)) }⟩

open UniformCircuitResidueForms (basisFormEquiv_symm_apply covectorWedge curry_covectorWedge)
open PuncturedCircuitCoordinates (pivot_coordinate_zero_iff)
open Set.powersetCard (ofFinEmbEquiv)

private lemma cons_sub_eq {A B : Type*} [AddCommGroup A] [AddCommGroup B] {n : ℕ}
    (f : A [⋀^Fin (n + 1)]→ₗ[ℤ] B) (x : A) (t : Fin n → A) :
    f (Fin.cons x t) = f (Fin.cons x (fun i => t i - x)) := by
  let u : Fin (n + 1) → A := Fin.cons x (fun i => t i - x)
  let v : Fin (n + 1) → A := Fin.cons 0 (fun _ => x)
  have hs : (Fin.cons x t : Fin (n + 1) → A) = u + v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [u, v]
    · simp [u, v]
  rw [hs, f.map_add_univ, Fintype.sum_eq_single univ]
  · simp [u]
  · intro S hS
    by_cases h0 : (0 : Fin (n + 1)) ∈ S
    · have houter : ∃ j : Fin (n + 1), j ∉ S := by
        by_contra! h
        exact hS (eq_univ_of_forall h)
      obtain ⟨j, hj'⟩ := houter
      have hj0 : j ≠ 0 := fun he => hj' (he ▸ h0)
      apply f.map_eq_zero_of_eq (i := 0) (j := j) _ _ hj0.symm
      change S.piecewise u v 0 = S.piecewise u v j
      have hv : v j = x := by
        obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj0
        simp [v, Fin.zero_succAbove]
      simp [Finset.piecewise, h0, hj', u, hv]
    · apply f.map_coord_zero 0
      simp [h0, v]

omit [Fintype I] in
/-- A coefficient of a covector product vanishes exactly when the lower form
vanishes on the differences from any representative of that face. -/
theorem wedge_coordinate_zero_iff_differences {n : ℕ} (H : Finset I)
    (hH : H.card = n + 2) (j : I) (hj : j ∈ H)
    (b : Module.Basis I ℤ (I → ℤ)) (a : (I → ℤ) →ₗ[ℤ] ℤ) (ha : ∀ i, a (b i) = 1)
    (f : (I → ℤ) [⋀^Fin (n + 1)]→ₗ[ℤ] RationalResidue) :
    let hcard : (H.erase j).card = n + 1 := by rw [card_erase_of_mem hj, hH]; omega
    let S : Set.powersetCard I (n + 1) := ⟨H.erase j, hcard⟩
    formCoordinates b (covectorWedge a f) H = 0 ↔
      f (fun i => b (ofFinEmbEquiv.symm S i) - b j) = 0 := by
  dsimp only
  rw [pivot_coordinate_zero_iff hH hj b (covectorWedge a f)]
  have hc : (H.erase j).card = n + 1 := by rw [card_erase_of_mem hj, hH]; omega
  rw [formCoordinates, dite_eq_left hc, basisFormEquiv_symm_apply]
  let S : Set.powersetCard I (n + 1) := ⟨H.erase j, hc⟩
  let t : Fin (n + 1) → I → ℤ := b ∘ ofFinEmbEquiv.symm S
  let diff : Fin (n + 1) → I → ℤ := fun i => t i - b j
  have haDiff (i : Fin (n + 1)) : a (diff i) = 0 := by
    simp [diff, t, ha]
  have hz :
      covectorWedge a (f.curryLeft (b j)) diff = 0 := by
    rw [covectorWedge, AlternatingMap.alternatizeUncurryFin_apply]
    apply sum_eq_zero
    intro i _
    rw [LinearMap.smulRight_apply, haDiff, zero_smul]
    simp
  have ht : (covectorWedge a f).curryLeft (b j) t =
      (covectorWedge a f).curryLeft (b j) diff := by
    simpa only [AlternatingMap.curryLeft_apply_apply, Matrix.vecCons, diff]
      using cons_sub_eq (covectorWedge a f) (b j) t
  change (covectorWedge a f).curryLeft (b j) t = 0 ↔ f diff = 0
  rw [ht, curry_covectorWedge, sub_apply, smul_apply,
    ha, one_smul, hz, sub_zero]

end D5.S3.Combinatorics.Matroids.SparsePavingCircuitCoordinates
