/- GID: D5/S3/Combinatorics/Matroids/DirectSumCircuitTorsion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/DirectSumCircuitTorsion
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Integral cycle joins and signed circuit restrictions for a matroid direct sum. -/

module

public import D5.S3.Combinatorics.Matroids.JointCircuitGramCertificate
public import Mathlib.Combinatorics.Matroid.Sum
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Joint circuit restrictions of a direct sum -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matroid

namespace D5.S3.Combinatorics.Matroids.DirectSumCircuitTorsion

variable {V : Type*} {M N : Matroid V} {K I : Set V}

private lemma indep_disjointSum_left (h : Disjoint M.E N.E) (hK : K ⊆ M.E) :
    (M.disjointSum N h).Indep K ↔ M.Indep K := by
  rw [Matroid.disjointSum_indep_iff, Set.inter_eq_left.2 hK,
    Set.disjoint_iff_inter_eq_empty.mp (h.mono_left hK)]
  simp [hK.trans Set.subset_union_left]

private lemma indep_disjointSum_right (h : Disjoint M.E N.E) (hK : K ⊆ N.E) :
    (M.disjointSum N h).Indep K ↔ N.Indep K := by
  rw [Matroid.disjointSum_indep_iff, Set.inter_eq_left.2 hK,
    Set.disjoint_iff_inter_eq_empty.mp (h.symm.mono_left hK)]
  simp [hK.trans Set.subset_union_right]

private lemma isCircuit_disjointSum_iff (h : Disjoint M.E N.E) :
    (M.disjointSum N h).IsCircuit K ↔ M.IsCircuit K ∨ N.IsCircuit K := by
  constructor
  · intro hC
    have hground : K ⊆ M.E ∪ N.E := by simpa using hC.subset_ground
    have hside : ¬ M.Indep (K ∩ M.E) ∨ ¬ N.Indep (K ∩ N.E) := by
      simpa only [Matroid.disjointSum_indep_iff, hground, and_true, not_and_or] using hC.not_indep
    rcases hside with hm | hn
    · have hleft : ¬ (M.disjointSum N h).Indep (K ∩ M.E) :=
        fun hj => hm ((indep_disjointSum_left h Set.inter_subset_right).mp hj)
      have hEq := hC.minimal_not_indep.eq_of_subset hleft Set.inter_subset_left
      have hK : K ⊆ M.E := hEq ▸ Set.inter_subset_right
      exact Or.inl ((Matroid.isCircuit_iff_minimal_not_indep hK).2
        ⟨fun hmK => hC.not_indep ((indep_disjointSum_left h hK).mpr hmK),
          fun J hJ hKJ => hC.minimal_not_indep.2
            (fun hj => hJ ((indep_disjointSum_left h (hKJ.trans hK)).mp hj)) hKJ⟩)
    · have hright : ¬ (M.disjointSum N h).Indep (K ∩ N.E) :=
        fun hj => hn ((indep_disjointSum_right h Set.inter_subset_right).mp hj)
      have hEq := hC.minimal_not_indep.eq_of_subset hright Set.inter_subset_left
      have hK : K ⊆ N.E := hEq ▸ Set.inter_subset_right
      exact Or.inr ((Matroid.isCircuit_iff_minimal_not_indep hK).2
        ⟨fun hnK => hC.not_indep ((indep_disjointSum_right h hK).mpr hnK),
          fun J hJ hKJ => hC.minimal_not_indep.2
            (fun hj => hJ ((indep_disjointSum_right h (hKJ.trans hK)).mp hj)) hKJ⟩)
  · rintro (hm | hn)
    · have hK := hm.subset_ground
      apply (Matroid.isCircuit_iff_minimal_not_indep _).2
      · exact ⟨fun hj => hm.not_indep ((indep_disjointSum_left h hK).mp hj),
          fun J hJ hKJ => hm.minimal_not_indep.2
            (fun hj => hJ ((indep_disjointSum_left h (hKJ.trans hK)).mpr hj)) hKJ⟩
      · simpa using hK.trans (Set.subset_union_left (t := N.E))
    · have hK := hn.subset_ground
      apply (Matroid.isCircuit_iff_minimal_not_indep _).2
      · exact ⟨fun hj => hn.not_indep ((indep_disjointSum_right h hK).mp hj),
          fun J hJ hKJ => hn.minimal_not_indep.2
            (fun hj => hJ ((indep_disjointSum_right h (hKJ.trans hK)).mpr hj)) hKJ⟩
      · simpa using hK.trans (Set.subset_union_right (s := M.E))

private lemma contract_disjointSum_left (h : Disjoint M.E N.E) (hI : M.IsBasis I K) :
    (M.disjointSum N h) ／ K =
      (M ／ K).disjointSum N (h.mono_left (by
        rw [Matroid.contract_ground]
        exact Set.sdiff_subset)) := by
  have hK := hI.subset_ground
  have hIN : Disjoint I N.E := h.mono_left hI.indep.subset_ground
  have hKN : Disjoint K N.E := h.mono_left hK
  have hsum : (M.disjointSum N h).IsBasis I K := by
    rw [Matroid.disjointSum_isBasis_iff, Set.inter_eq_left.2 hI.indep.subset_ground,
      Set.inter_eq_left.2 hK, Set.disjoint_iff_inter_eq_empty.mp hIN,
      Set.disjoint_iff_inter_eq_empty.mp hKN]
    exact ⟨hI, by simp, hI.subset, hK.trans Set.subset_union_left⟩
  apply Matroid.ext_indep
  · rw [Matroid.contract_ground, Matroid.disjointSum_ground_eq,
      Matroid.disjointSum_ground_eq, Matroid.contract_ground]
    ext x
    have hx : x ∈ K → x ∉ N.E := fun hxK hxN => Set.disjoint_left.mp hKN hxK hxN
    simp only [Set.mem_sdiff, Set.mem_union]
    tauto
  intro J hJ
  have hJ' : J ⊆ (M.E ∪ N.E) \ K := by
    simpa only [Matroid.contract_ground, Matroid.disjointSum_ground_eq] using hJ
  have hKJ : Disjoint K J := Set.disjoint_left.2 fun _ hxK hxJ => (hJ' hxJ).2 hxK
  have hKMJ : Disjoint K (J ∩ M.E) := hKJ.mono_right Set.inter_subset_left
  have hJM : J ∩ (M.E \ K) = J ∩ M.E := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_sdiff]
    exact ⟨fun hx => ⟨hx.1, hx.2.1⟩, fun hx => ⟨hx.1, hx.2, (hJ' hx.1).2⟩⟩
  have hsub : J ⊆ (M.E \ K) ∪ N.E := by
    intro x hx
    rcases (hJ' hx).1 with hxM | hxN
    · exact Or.inl ⟨hxM, (hJ' hx).2⟩
    · exact Or.inr hxN
  have hsub' : J ∪ I ⊆ M.E ∪ N.E :=
    Set.union_subset (fun _ hx => (hJ' hx).1) (hI.indep.subset_ground.trans Set.subset_union_left)
  simp only [hsum.contract_indep_iff, Matroid.disjointSum_indep_iff,
    Matroid.contract_ground, hI.contract_indep_iff, Set.union_inter_distrib_right,
    Set.inter_eq_left.2 hI.indep.subset_ground, Set.disjoint_iff_inter_eq_empty.mp hIN,
    Set.union_empty, hKMJ, hKJ, hsub, hsub', hJM, and_true]

private lemma contract_disjointSum_right (h : Disjoint M.E N.E) (hI : N.IsBasis I K) :
    (M.disjointSum N h) ／ K =
      M.disjointSum (N ／ K) (h.mono_right (by
        rw [Matroid.contract_ground]
        exact Set.sdiff_subset)) := by
  calc
    (M.disjointSum N h) ／ K = (N.disjointSum M h.symm) ／ K :=
      congrArg (fun P => P ／ K) Matroid.disjointSum_comm
    _ = (N ／ K).disjointSum M _ := contract_disjointSum_left h.symm hI
    _ = _ := Matroid.disjointSum_comm

open Finset
open OrderedCycleFactorization
  (Chain PassiveBase TopCycle boundaryOn boundaryOn_signedJoin signedJoin shuffleSign topCycle_ext)
open CircuitCycleDecomposition (restrictChain restrictionSign topCycles)
open IntegralCircuitImage (aggregateRestrict)
open JointCircuitGramCertificate
  (Passive normalizedCycle normalizedCycle_coord fromCoordinates fromCoordinates_coord
    fromCoordinates_cycle)

variable [LinearOrder V] {A B L R : Finset V}

private lemma shuffleSign_union_right_of_left
    (horder : ∀ x ∈ L, ∀ y ∈ R, x < y) (hA : A ⊆ L) {T : Finset V} (hB : B ⊆ R) :
    shuffleSign A (T ∪ B) = shuffleSign A T := by
  unfold shuffleSign
  congr 1
  apply sum_congr rfl
  intro x hx
  have hfilter : B.filter (· < x) = ∅ :=
    filter_eq_empty_iff.2 fun y hy => (horder x (hA hx) y (hB hy)).not_gt
  simp [filter_union, hfilter]

private lemma shuffleSign_union_left_of_right
    (horder : ∀ x ∈ L, ∀ y ∈ R, x < y) (hA : A ⊆ R) {T : Finset V}
    (hB : B ⊆ L) (hBT : Disjoint B T) :
    shuffleSign A (B ∪ T) = (-1 : ℤ) ^ (A.card * B.card) * shuffleSign A T := by
  unfold shuffleSign
  rw [← pow_add]
  congr 1
  calc
    ∑ x ∈ A, ((B ∪ T).filter (· < x)).card =
        ∑ x ∈ A, (B.card + (T.filter (· < x)).card) := by
      apply sum_congr rfl
      intro x hx
      have hfilter : B.filter (· < x) = B :=
        filter_eq_self.2 fun y hy => horder y (hB hy) x (hA hx)
      rw [filter_union, hfilter, card_union_of_disjoint]
      exact hBT.mono_right (filter_subset _ _)
    _ = _ := by simp [sum_add_distrib]

private lemma boundaryOn_eq_ground [Fintype V] {P : Matroid V} {u : Chain V}
    (hu : TopCycle P u) {S U : Finset V} (hS : (S : Set V) = P.E)
    (hSU : S ⊆ U) (F : Finset V) :
    boundaryOn U u F = boundaryOn S u F := by
  unfold boundaryOn
  symm
  apply sum_subset
  · intro x hx
    exact mem_sdiff.2 ⟨hSU (mem_sdiff.mp hx).1, (mem_sdiff.mp hx).2⟩
  · intro x hx hnot
    have hxS : x ∉ S := fun hm => hnot (mem_sdiff.2 ⟨hm, (mem_sdiff.mp hx).2⟩)
    have hzero : u (insert x F) = 0 := hu.vanishes _ fun hb =>
      hxS (show x ∈ (S : Set V) by
        rw [hS]
        exact hb.subset_ground (mem_insert_self x F))
    rw [hzero, mul_zero]

private lemma sdiff_eq_inter_right (hsep : Disjoint L R) {F : Finset V}
    (hF : F ⊆ L ∪ R) : F \ L = F ∩ R := by
  ext x
  simp only [mem_sdiff, mem_inter]
  exact ⟨fun ⟨hxF, hxL⟩ => ⟨hxF, (mem_union.mp (hF hxF)).resolve_left hxL⟩,
    fun ⟨hxF, hxR⟩ => ⟨hxF, disjoint_right.mp hsep hxR⟩⟩

private lemma signedJoin_topCycle [Fintype V] (h : Disjoint M.E N.E)
    (hL : (L : Set V) = M.E) (hR : (R : Set V) = N.E)
    {u v : Chain V} (hu : TopCycle M u) (hv : TopCycle N v) :
    TopCycle (M.disjointSum N h) (signedJoin L u v) := by
  have hsep : Disjoint L R := by
    have hd : Disjoint (L : Set V) (R : Set V) := by simpa only [hL, hR] using h
    exact disjoint_left.2 (fun _ hx hy => Set.disjoint_left.mp hd hx hy)
  refine ⟨?_, ?_⟩
  · intro F hF
    by_contra hnonzero
    have hA : M.IsBase (↑(F ∩ L) : Set V) := by
      by_contra hn
      exact hnonzero (by simp [signedJoin, hu.vanishes _ hn])
    have hB : N.IsBase (↑(F \ L) : Set V) := by
      by_contra hn
      exact hnonzero (by simp [signedJoin, hv.vanishes _ hn])
    have hsub : F ⊆ L ∪ R := by
      intro x hx
      by_cases hxL : x ∈ L
      · exact mem_union_left _ hxL
      · apply mem_union_right
        have hxR := hB.subset_ground (show x ∈ (↑(F \ L) : Set V) from mem_sdiff.2 ⟨hx, hxL⟩)
        exact show x ∈ (R : Set V) by simpa only [hR] using hxR
    apply hF
    rw [Matroid.disjointSum_isBase_iff, ← hL, ← hR, ← coe_inter, ← coe_inter,
      ← sdiff_eq_inter_right hsep hsub, ← coe_union]
    exact ⟨hA, hB, hsub⟩
  · intro F
    have hRU : R ⊆ univ \ L := fun x hx => mem_sdiff.2
      ⟨mem_univ _, disjoint_right.mp hsep hx⟩
    rw [boundaryOn_signedJoin,
      boundaryOn_eq_ground hv hR hRU, ← boundaryOn_eq_ground hv hR (subset_univ R),
      ← boundaryOn_eq_ground hu hL (subset_univ L), hu.cycle, hv.cycle]
    simp

omit [LinearOrder V] in
private lemma isBase_disjointSum_split {P Q : Matroid V}
    (h : Disjoint P.E Q.E) {S T : Set V}
    (hP : P.E ⊆ S) (hQ : Disjoint S Q.E) :
    (P.disjointSum Q h).IsBase T ↔ P.IsBase (T ∩ S) ∧ Q.IsBase (T \ S) := by
  have hparts (hT : T ⊆ P.E ∪ Q.E) :
      T ∩ S = T ∩ P.E ∧ T \ S = T ∩ Q.E := by
    constructor
    · ext x
      simp only [Set.mem_inter_iff]
      exact ⟨fun ⟨hxT, hxS⟩ =>
        ⟨hxT, (hT hxT).resolve_right (Set.disjoint_left.mp hQ hxS)⟩,
        fun ⟨hxT, hxP⟩ => ⟨hxT, hP hxP⟩⟩
    · ext x
      simp only [Set.mem_inter_iff, Set.mem_sdiff]
      exact ⟨fun ⟨hxT, hxS⟩ => ⟨hxT, (hT hxT).resolve_left (fun hx => hxS (hP hx))⟩,
        fun ⟨hxT, hxQ⟩ => ⟨hxT, fun hxS => Set.disjoint_left.mp hQ hxS hxQ⟩⟩
  rw [Matroid.disjointSum_isBase_iff]
  constructor
  · rintro ⟨hA, hB, hT⟩
    rw [(hparts hT).1, (hparts hT).2]
    exact ⟨hA, hB⟩
  · rintro ⟨hA, hB⟩
    have hT : T ⊆ P.E ∪ Q.E := by
      intro x hx
      by_cases hxS : x ∈ S
      · exact Or.inl (hA.subset_ground ⟨hx, hxS⟩)
      · exact Or.inr (hB.subset_ground ⟨hx, hxS⟩)
    rw [← (hparts hT).1, ← (hparts hT).2]
    exact ⟨hA, hB, hT⟩

private lemma shuffleSign_separated
    (horder : ∀ x ∈ L, ∀ y ∈ R, x < y) (hA : A ⊆ L) (hB : B ⊆ R) :
    shuffleSign A B = 1 := by
  simpa [shuffleSign] using shuffleSign_union_right_of_left (T := ∅) horder hA hB

private lemma restrictChain_disjointSum_left [Fintype V]
    (h : Disjoint M.E N.E) (hL : (L : Set V) = M.E) (hR : (R : Set V) = N.E)
    (horder : ∀ x ∈ L, ∀ y ∈ R, x < y) {C : Finset V}
    (hC : M.IsCircuit (C : Set V)) {a : V} (ha : a ∈ C)
    (u : Chain V) {v : Chain V} (hv : TopCycle N v) (T : Finset V) :
    restrictChain (M.disjointSum N h) C a (signedJoin L u v) T =
      signedJoin L (restrictChain M C a u) v T := by
  have hLC : (M ／ (C : Set V)).E ⊆ (L : Set V) := by
    rw [Matroid.contract_ground, hL]
    exact Set.sdiff_subset
  have hRN : Disjoint (L : Set V) N.E := by simpa only [hL] using h
  have hb :
      (M.disjointSum N h ／ (C : Set V)).IsBase (T : Set V) ↔
        (M ／ (C : Set V)).IsBase (↑(T ∩ L) : Set V) ∧ N.IsBase (↑(T \ L) : Set V) := by
    rw [contract_disjointSum_left h (OrderedCycleFactorization.circuit_erase_basis hC ha),
      coe_inter, coe_sdiff]
    exact isBase_disjointSum_split _ hLC hRN
  unfold restrictChain
  rw [hb]
  by_cases hB : N.IsBase (↑(T \ L) : Set V)
  · have hBT : T \ L ⊆ R := fun x hx => by
      change x ∈ (R : Set V)
      rw [hR]
      exact hB.subset_ground hx
    have hA : C.erase a ⊆ L := fun x hx => by
      change x ∈ (L : Set V)
      rw [hL]
      exact hC.subset_ground (mem_of_mem_erase hx)
    have hTA : (T ∪ C.erase a) ∩ L = (T ∩ L) ∪ C.erase a := by
      rw [union_inter_distrib_right, inter_eq_left.2 hA]
    have hTB : (T ∪ C.erase a) \ L = T \ L := by
      rw [union_sdiff_distrib, sdiff_eq_empty_iff_subset.2 hA, union_empty]
    have hsign : restrictionSign C a T = restrictionSign C a (T ∩ L) := by
      have hshuffle := shuffleSign_union_right_of_left (T := T ∩ L) horder hA hBT
      rw [union_comm, sdiff_union_inter] at hshuffle
      simp only [restrictionSign, hshuffle]
    have hprod : (T ∩ L) ∪ C.erase a ⊆ L := union_subset inter_subset_right hA
    by_cases hbase : (M ／ (C : Set V)).IsBase (↑(T ∩ L) : Set V)
    · simp only [hbase, hB, and_self, ite_true, signedJoin, hTA, hTB, hsign,
        shuffleSign_separated horder hprod hBT,
        shuffleSign_separated horder inter_subset_right hBT, one_mul]
      ring
    · rw [ite_eq_right (fun hx => hbase hx.1), signedJoin, ite_eq_right hbase]
      simp
  · rw [ite_eq_right (fun hx => hB hx.2), signedJoin, hv.vanishes _ hB]
    simp

private lemma aggregateRestrict_disjointSum_left [Fintype V]
    (h : Disjoint M.E N.E) (hL : (L : Set V) = M.E) (hR : (R : Set V) = N.E)
    (horder : ∀ x ∈ L, ∀ y ∈ R, x < y) {C : Finset V}
    (hC : M.IsCircuit (C : Set V)) (u : Chain V) {v : Chain V} (hv : TopCycle N v) :
    aggregateRestrict (M.disjointSum N h) C (signedJoin L u v) =
      signedJoin L (aggregateRestrict M C u) v := by
  ext T
  simp only [aggregateRestrict, Finset.sum_apply, signedJoin]
  rw [sum_mul, mul_sum]
  exact sum_congr rfl fun a ha =>
    restrictChain_disjointSum_left h hL hR horder hC ha u hv T

private lemma restrictChain_disjointSum_right [Fintype V]
    (h : Disjoint M.E N.E) (hL : (L : Set V) = M.E) (hR : (R : Set V) = N.E)
    (horder : ∀ x ∈ L, ∀ y ∈ R, x < y) {C : Finset V}
    (hC : N.IsCircuit (C : Set V)) {a : V} (ha : a ∈ C)
    {u : Chain V} (hu : TopCycle M u) (v : Chain V) (T : Finset V) :
    restrictChain (M.disjointSum N h) C a (signedJoin L u v) T =
      (-1 : ℤ) ^ ((C.card - 1) * (T ∩ L).card) *
        signedJoin L u (restrictChain N C a v) T := by
  have hRC : (N ／ (C : Set V)).E ⊆ N.E := by
    rw [Matroid.contract_ground]
    exact Set.sdiff_subset
  have hLC : Disjoint (L : Set V) (N ／ (C : Set V)).E := by
    rw [hL]
    exact h.mono_right hRC
  have hb :
      (M.disjointSum N h ／ (C : Set V)).IsBase (T : Set V) ↔
        M.IsBase (↑(T ∩ L) : Set V) ∧ (N ／ (C : Set V)).IsBase (↑(T \ L) : Set V) := by
    rw [contract_disjointSum_right h (OrderedCycleFactorization.circuit_erase_basis hC ha),
      coe_inter, coe_sdiff]
    exact isBase_disjointSum_split _ hL.ge hLC
  unfold restrictChain
  rw [hb]
  by_cases hA : M.IsBase (↑(T ∩ L) : Set V)
  · by_cases hbase : (N ／ (C : Set V)).IsBase (↑(T \ L) : Set V)
    · have hBT : T \ L ⊆ R := fun x hx => by
        change x ∈ (R : Set V)
        rw [hR]
        exact hRC (hbase.subset_ground hx)
      have hB : C.erase a ⊆ R := fun x hx => by
        change x ∈ (R : Set V)
        rw [hR]
        exact hC.subset_ground (mem_of_mem_erase hx)
      have hd : Disjoint (C.erase a) L := by
        apply disjoint_left.2
        intro x hx hy
        apply Set.disjoint_left.mp h
        · rw [← hL]
          exact hy
        · rw [← hR]
          exact hB hx
      have hTA : (T ∪ C.erase a) ∩ L = T ∩ L := by
        rw [union_inter_distrib_right, disjoint_iff_inter_eq_empty.mp hd, union_empty]
      have hTB : (T ∪ C.erase a) \ L = (T \ L) ∪ C.erase a := by
        rw [union_sdiff_distrib, Finset.sdiff_eq_self_iff_disjoint.2 hd]
      have hsign : restrictionSign C a T =
          (-1 : ℤ) ^ ((C.card - 1) * (T ∩ L).card) * restrictionSign C a (T \ L) := by
        have hshuffle := shuffleSign_union_left_of_right (A := C.erase a) (B := T ∩ L)
          (T := T \ L) horder hB inter_subset_right (disjoint_sdiff_inter T L).symm
        rw [union_comm, sdiff_union_inter, card_erase_of_mem ha] at hshuffle
        simp only [restrictionSign, hshuffle]
        ring
      have hprod : (T \ L) ∪ C.erase a ⊆ R := union_subset hBT hB
      simp only [hbase, hA, and_self, ite_true, signedJoin, hTA, hTB, hsign,
        shuffleSign_separated horder inter_subset_right hprod,
        shuffleSign_separated horder inter_subset_right hBT, one_mul]
      ring
    · rw [ite_eq_right (fun hx => hbase hx.2), signedJoin, ite_eq_right hbase]
      simp
  · rw [ite_eq_right (fun hx => hA hx.1), signedJoin, hu.vanishes _ hA]
    simp

private lemma aggregateRestrict_disjointSum_right [Fintype V]
    (h : Disjoint M.E N.E) (hL : (L : Set V) = M.E) (hR : (R : Set V) = N.E)
    (horder : ∀ x ∈ L, ∀ y ∈ R, x < y) {C : Finset V}
    (hC : N.IsCircuit (C : Set V)) {u : Chain V} (hu : TopCycle M u) (v : Chain V)
    (T : Finset V) :
    aggregateRestrict (M.disjointSum N h) C (signedJoin L u v) T =
      (-1 : ℤ) ^ ((C.card - 1) * (T ∩ L).card) *
        signedJoin L u (aggregateRestrict N C v) T := by
  simp only [aggregateRestrict, Finset.sum_apply, signedJoin]
  rw [mul_sum, mul_sum, mul_sum]
  exact sum_congr rfl fun a ha =>
    restrictChain_disjointSum_right h hL hR horder hC ha hu v T

private lemma passiveBase_disjointSum_left
    (h : Disjoint M.E N.E) (hL : (L : Set V) = M.E)
    {F : Finset V} (hF : PassiveBase (M.disjointSum N h) F) :
    PassiveBase M (F ∩ L) := by
  have hsep : Disjoint (L : Set V) N.E := by simpa only [hL] using h
  have hsplit (G : Finset V) :
      (M.disjointSum N h).IsBase (G : Set V) ↔
        M.IsBase (↑(G ∩ L) : Set V) ∧ N.IsBase (↑(G \ L) : Set V) := by
    rw [coe_inter, coe_sdiff]
    exact isBase_disjointSum_split h hL.ge hsep
  have hbase := ((hsplit F).mp hF.1).1
  refine ⟨hbase, ?_⟩
  intro x hx
  obtain ⟨y, hy, hyx, hswap⟩ := hF.2 x (mem_inter.mp hx).1
  have hswap' := ((hsplit (insert y (F.erase x))).mp hswap).1
  by_cases hyL : y ∈ L
  · rw [insert_inter_of_mem hyL, erase_inter] at hswap'
    exact ⟨y, fun hy' => hy (mem_inter.mp hy').1, hyx, hswap'⟩
  · rw [insert_inter_of_notMem hyL, erase_inter] at hswap'
    have hEq := hswap'.eq_of_subset_isBase hbase (by
      exact_mod_cast erase_subset x (F ∩ L))
    exact False.elim (notMem_erase x (F ∩ L) (by
      change x ∈ (↑((F ∩ L).erase x) : Set V)
      rw [hEq]
      exact hx))

private lemma isBase_disjointSum_union (h : Disjoint M.E N.E)
    (hA : M.IsBase (A : Set V)) (hB : N.IsBase (B : Set V)) :
    (M.disjointSum N h).IsBase (↑(A ∪ B) : Set V) := by
  have hAN : Disjoint (A : Set V) N.E := h.mono_left hA.subset_ground
  have hBM : Disjoint (B : Set V) M.E := h.symm.mono_left hB.subset_ground
  rw [coe_union, Matroid.disjointSum_isBase_iff, Set.union_inter_distrib_right,
    Set.union_inter_distrib_right, Set.inter_eq_left.2 hA.subset_ground,
    Set.inter_eq_left.2 hB.subset_ground, Set.disjoint_iff_inter_eq_empty.mp hAN,
    Set.disjoint_iff_inter_eq_empty.mp hBM, Set.union_empty, Set.empty_union]
  exact ⟨hA, hB, Set.union_subset_union hA.subset_ground hB.subset_ground⟩

private lemma passiveBase_disjointSum_union (h : Disjoint M.E N.E)
    (hA : PassiveBase M A) (hB : PassiveBase N B) :
    PassiveBase (M.disjointSum N h) (A ∪ B) := by
  refine ⟨isBase_disjointSum_union h hA.1 hB.1, ?_⟩
  intro x hx
  have hAB : Disjoint A B := disjoint_left.2 fun _ hxA hxB =>
    Set.disjoint_left.mp h (hA.1.subset_ground hxA) (hB.1.subset_ground hxB)
  rcases mem_union.mp hx with hxA | hxB
  · obtain ⟨y, hyA, hyx, hyBase⟩ := hA.2 x hxA
    have hyM := hyBase.subset_ground (mem_insert_self y (A.erase x))
    have hyB : y ∉ B := fun hyB => Set.disjoint_left.mp h hyM (hB.1.subset_ground hyB)
    have hswap : insert y ((A ∪ B).erase x) = insert y (A.erase x) ∪ B := by
      rw [erase_union_distrib, erase_eq_of_notMem (disjoint_left.mp hAB hxA), insert_union]
    exact ⟨y, fun hy => (mem_union.mp hy).elim hyA hyB, hyx,
      hswap ▸ isBase_disjointSum_union h hyBase hB.1⟩
  · obtain ⟨y, hyB, hyx, hyBase⟩ := hB.2 x hxB
    have hyN := hyBase.subset_ground (mem_insert_self y (B.erase x))
    have hyA : y ∉ A := fun hyA => Set.disjoint_left.mp h (hA.1.subset_ground hyA) hyN
    have hswap : insert y ((A ∪ B).erase x) = A ∪ insert y (B.erase x) := by
      rw [erase_union_distrib, erase_eq_of_notMem (disjoint_right.mp hAB hxB),
        union_comm A, ← insert_union, union_comm A]
    exact ⟨y, fun hy => (mem_union.mp hy).elim hyA hyB, hyx,
      hswap ▸ isBase_disjointSum_union h hA.1 hyBase⟩

omit [LinearOrder V] in
private lemma disjoint_ground_finsets (h : Disjoint M.E N.E)
    (hL : (L : Set V) = M.E) (hR : (R : Set V) = N.E) : Disjoint L R := by
  have hsep : Disjoint (L : Set V) (R : Set V) := by simpa only [hL, hR] using h
  exact disjoint_left.2 (fun _ hx hy => Set.disjoint_left.mp hsep hx hy)

private def passiveSumEquiv (h : Disjoint M.E N.E)
    (hL : (L : Set V) = M.E) (hR : (R : Set V) = N.E) :
    Passive (M.disjointSum N h) ≃ Passive M × Passive N where
  toFun F :=
    ⟨⟨F.val ∩ L, passiveBase_disjointSum_left h hL F.prop⟩,
      ⟨F.val ∩ R, passiveBase_disjointSum_left h.symm hR
        (Matroid.disjointSum_comm (h := h) ▸ F.prop)⟩⟩
  invFun P := ⟨P.1.val ∪ P.2.val, passiveBase_disjointSum_union h P.1.prop P.2.prop⟩
  left_inv F := by
    apply Subtype.ext
    change F.val ∩ L ∪ F.val ∩ R = F.val
    have hsub : F.val ⊆ L ∪ R := by
      have hF := F.prop.1.subset_ground
      rwa [Matroid.disjointSum_ground_eq, ← hL, ← hR, ← coe_union, coe_subset] at hF
    rw [← inter_union_distrib_left, inter_eq_left.2 hsub]
  right_inv P := by
    have hA : P.1.val ⊆ L := by
      have h := P.1.prop.1.subset_ground
      rwa [← hL, coe_subset] at h
    have hB : P.2.val ⊆ R := by
      have h := P.2.prop.1.subset_ground
      rwa [← hR, coe_subset] at h
    have hd := disjoint_ground_finsets h hL hR
    apply Prod.ext <;> apply Subtype.ext
    · change (P.1.val ∪ P.2.val) ∩ L = P.1.val
      rw [union_inter_distrib_right, inter_eq_left.2 hA,
        disjoint_iff_inter_eq_empty.mp (hd.symm.mono_left hB), union_empty]
    · change (P.1.val ∪ P.2.val) ∩ R = P.2.val
      rw [union_inter_distrib_right, inter_eq_left.2 hB,
        disjoint_iff_inter_eq_empty.mp (hd.mono_left hA), empty_union]

open Module TensorProduct

variable [Fintype V]

private noncomputable def cycleCoordinates (P : Matroid V) :
    topCycles P ≃ₗ[ℤ] (Passive P → ℤ) where
  toFun z D := z.val D.val
  invFun := fromCoordinates P
  left_inv := fromCoordinates_cycle
  right_inv x := funext (fromCoordinates_coord x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def cycleBasis (P : Matroid V) : Basis (Passive P) ℤ (topCycles P) :=
  Basis.ofEquivFun (cycleCoordinates P)

private lemma cycleBasis_apply (P : Matroid V) (D : Passive P) :
    cycleBasis P D = normalizedCycle D := by
  classical
  rw [cycleBasis, Basis.coe_ofEquivFun]
  apply (cycleCoordinates P).injective
  rw [LinearEquiv.apply_symm_apply]
  funext E
  change Pi.single (M := fun _ => ℤ) D 1 E = (normalizedCycle D).val E.val
  rw [normalizedCycle_coord, Pi.single_apply]

private lemma signedJoin_normalized (h : Disjoint M.E N.E)
    (hL : (L : Set V) = M.E) (hR : (R : Set V) = N.E)
    (horder : ∀ x ∈ L, ∀ y ∈ R, x < y) (D : Passive M) (E : Passive N) :
    signedJoin L (normalizedCycle D).val (normalizedCycle E).val =
      (normalizedCycle ((passiveSumEquiv h hL hR).symm (D, E))).val := by
  classical
  apply topCycle_ext (signedJoin_topCycle h hL hR (normalizedCycle D).prop
    (normalizedCycle E).prop) (normalizedCycle _).prop
  intro F hF
  let P : Passive (M.disjointSum N h) := ⟨F, hF⟩
  let e := passiveSumEquiv h hL hR
  have hsub : F ⊆ L ∪ R := by
    have hg := hF.1.subset_ground
    rwa [Matroid.disjointSum_ground_eq, ← hL, ← hR, ← coe_union, coe_subset] at hg
  have hright := sdiff_eq_inter_right (disjoint_ground_finsets h hL hR) hsub
  change signedJoin L (normalizedCycle D).val (normalizedCycle E).val F =
    (normalizedCycle (e.symm (D, E))).val P.val
  rw [normalizedCycle_coord, signedJoin, hright,
    shuffleSign_separated horder inter_subset_right inter_subset_right, one_mul]
  change (normalizedCycle D).val (e P).1.val * (normalizedCycle E).val (e P).2.val =
    if P = e.symm (D, E) then 1 else 0
  rw [normalizedCycle_coord, normalizedCycle_coord]
  have heq : P = e.symm (D, E) ↔ (e P).1 = D ∧ (e P).2 = E := by
    rw [← e.apply_eq_iff_eq, e.apply_symm_apply]
    exact ⟨fun he => ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩,
      fun he => Prod.ext he.1 he.2⟩
  by_cases hD : (e P).1 = D <;> by_cases hE : (e P).2 = E <;> simp [heq, hD, hE]

private def cycleJoin (h : Disjoint M.E N.E)
    (hL : (L : Set V) = M.E) (hR : (R : Set V) = N.E) :
    topCycles M →ₗ[ℤ] topCycles N →ₗ[ℤ] topCycles (M.disjointSum N h) where
  toFun u :=
    { toFun := fun v => ⟨signedJoin L u.val v.val, signedJoin_topCycle h hL hR u.prop v.prop⟩
      map_add' := by
        intro v w
        apply Subtype.ext
        funext F
        change signedJoin L u.val (v.val + w.val) F =
          signedJoin L u.val v.val F + signedJoin L u.val w.val F
        simp only [signedJoin, Pi.add_apply]
        ring
      map_smul' := by
        intro c v
        apply Subtype.ext
        funext F
        change signedJoin L u.val (c • v.val) F = c * signedJoin L u.val v.val F
        simp only [signedJoin, Pi.smul_apply, zsmul_eq_mul, Int.cast_id]
        ring }
  map_add' := by
    intro u w
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext F
    change signedJoin L (u.val + w.val) v.val F =
      signedJoin L u.val v.val F + signedJoin L w.val v.val F
    simp only [signedJoin, Pi.add_apply]
    ring
  map_smul' := by
    intro c u
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext F
    change signedJoin L (c • u.val) v.val F = c * signedJoin L u.val v.val F
    simp only [signedJoin, Pi.smul_apply, zsmul_eq_mul, Int.cast_id]
    ring

private noncomputable def cycleJoinEquiv (h : Disjoint M.E N.E)
    (hL : (L : Set V) = M.E) (hR : (R : Set V) = N.E) :
    topCycles M ⊗[ℤ] topCycles N ≃ₗ[ℤ] topCycles (M.disjointSum N h) :=
  ((cycleBasis M).tensorProduct (cycleBasis N)).equiv (cycleBasis _)
    (passiveSumEquiv h hL hR).symm

private lemma cycleJoinEquiv_tmul (h : Disjoint M.E N.E)
    (hL : (L : Set V) = M.E) (hR : (R : Set V) = N.E)
    (horder : ∀ x ∈ L, ∀ y ∈ R, x < y) (u : topCycles M) (v : topCycles N) :
    (cycleJoinEquiv h hL hR (u ⊗ₜ[ℤ] v)).val = signedJoin L u.val v.val := by
  have heq : (cycleJoinEquiv h hL hR).toLinearMap = TensorProduct.lift (cycleJoin h hL hR) := by
    apply ((cycleBasis M).tensorProduct (cycleBasis N)).ext
    intro P
    change cycleJoinEquiv h hL hR _ = _
    refine (Basis.equiv_apply (b := (cycleBasis M).tensorProduct (cycleBasis N))
      (b' := cycleBasis (M.disjointSum N h))
      (e := (passiveSumEquiv h hL hR).symm) (i := P)).trans ?_
    simp only [Basis.tensorProduct_apply', TensorProduct.lift.tmul, cycleBasis_apply]
    exact Subtype.ext (signedJoin_normalized h hL hR horder P.1 P.2).symm
  have hf := LinearMap.congr_fun heq (u ⊗ₜ[ℤ] v)
  exact congrArg Subtype.val (hf.trans (TensorProduct.lift.tmul u v))

end D5.S3.Combinatorics.Matroids.DirectSumCircuitTorsion
