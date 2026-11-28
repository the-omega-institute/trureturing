/- GID: D5/S3/Combinatorics/Hamming/ConstantPowerCooling/Shadows
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hamming/ConstantPowerCooling/Shadows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pair shadows of cooling-code classes and their induced supports. -/

import D5.S3.Combinatorics.Graph.DeletionResilientCliques.EdgeBound

/-! # Pair shadows of cooling-code classes and their induced supports -/

open scoped BigOperators ENat
open SimpleGraph

namespace CPECCBridge

def Shadow {V : Type*} [DecidableEq V]
    (P : Finset (Finset V)) : SimpleGraph V :=
  SimpleGraph.mk
    (fun u v => u ≠ v ∧ ∃ A ∈ P, u ∈ A ∧ v ∈ A)
    (Std.Symm.mk (by
      exact fun u v h => ⟨h.1.symm, by
        obtain ⟨A, hA, hu, hv⟩ := h.2
        exact ⟨A, hA, hv, hu⟩⟩))
    (Std.Irrefl.mk (by
      exact fun u h => h.1 rfl))

private theorem shadow_adj_of_mem {V : Type*} [DecidableEq V]
    {P : Finset (Finset V)} {A : Finset V} (hA : A ∈ P)
    {u v : V} (hu : u ∈ A) (hv : v ∈ A) (hneq : u ≠ v) :
    (Shadow P).Adj u v := by
  exact ⟨hneq, ⟨A, hA, hu, hv⟩⟩

private theorem shadow_clique_of_mem {V : Type*} [DecidableEq V]
    {P : Finset (Finset V)} {A : Finset V} (hA : A ∈ P) :
    (Shadow P).IsClique (A : Set V) := by
  rw [isClique_iff]
  intro u hu v hv huv
  exact shadow_adj_of_mem hA hu hv (by exact huv)

private theorem shadow_min_degree_of_mem {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {P : Finset (Finset V)} {w : ℕ}
    [DecidableRel (Shadow P).Adj]
    (hsize : ∀ A ∈ P, A.card = w)
    (hcover : ∀ v, ∃ A ∈ P, v ∈ A) :
    w - 1 ≤ (Shadow P).minDegree := by
  classical
  refine (Shadow P).le_minDegree_of_forall_le_degree (w - 1) ?_
  intro v
  obtain ⟨A, hA, hvA⟩ := hcover v
  have hsub : (A.erase v : Set V) ⊆ (Shadow P).neighborSet v := by
    intro u hu
    have huA : u ∈ A := Finset.mem_of_mem_erase hu
    have hne : u ≠ v := by
      intro hEq
      subst u
      exact (Finset.mem_erase.mp hu).1 rfl
    exact shadow_adj_of_mem hA hvA huA hne.symm
  have hcard : (A.erase v).card = w - 1 := by
    rw [Finset.card_erase_of_mem hvA, hsize A hA]
  have hcard' : (A.erase v : Set V).ncard = w - 1 := by
    rw [Set.ncard_coe_finset, hcard]
  have hle := Set.ncard_le_ncard hsub
  exact hcard'.symm ▸ hle.trans_eq ((Shadow P).ncard_neighborSet v)

private theorem shadow_survives_deletion {V : Type*} [Fintype V] [DecidableEq V]
    {P : Finset (Finset V)} {w t : ℕ}
    (hsize : ∀ A ∈ P, A.card = w)
    (hdel : ∀ S : Finset V, S.card = t → ∃ A ∈ P, Disjoint S A) :
    AppendixA.SurvivesDeletion (Shadow P) w t := by
  intro S hS
  obtain ⟨A, hA, hdisj⟩ := hdel S hS
  refine ⟨A, ?_, hdisj⟩
  exact ⟨shadow_clique_of_mem hA, hsize A hA⟩

private theorem shadow_edge_mem_support {V : Type*} [DecidableEq V]
    {P : Finset (Finset V)} {e : Sym2 V}
    (he : e ∈ (Shadow P).edgeSet) :
    ∃ u v A, e = s(u, v) ∧ A ∈ P ∧ u ∈ A ∧ v ∈ A ∧ u ≠ v := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      rw [SimpleGraph.mem_edgeSet] at he
      obtain ⟨hne, A, hA, hu, hv⟩ := he
      exact ⟨u, v, A, rfl, hA, hu, hv, hne⟩

private theorem shadows_edge_disjoint
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (P : I → Finset (Finset V))
    (hcross : ∀ ⦃i j : I⦄, i ≠ j → ∀ A ∈ P i, ∀ B ∈ P j,
      (A ∩ B).card ≤ 1)
    [(i : I) → Fintype (Shadow (P i)).edgeSet] :
    (Set.univ : Set I).PairwiseDisjoint
    (fun i => (Shadow (P i)).edgeFinset) := by
  classical
  intro i hi j hj hij
  change Disjoint ((Shadow (P i)).edgeFinset) ((Shadow (P j)).edgeFinset)
  refine Finset.disjoint_left.mpr ?_
  intro e hei hej
  obtain ⟨u, v, A, he, hA, huA, hvA, huv⟩ :=
    shadow_edge_mem_support (P := P i) (by simpa [SimpleGraph.mem_edgeFinset] using hei)
  obtain ⟨u', v', B, he', hB, huB, hvB, huv'⟩ :=
    shadow_edge_mem_support (P := P j) (by simpa [SimpleGraph.mem_edgeFinset] using hej)
  rw [he] at he'
  rw [Sym2.eq_iff] at he'
  rcases he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hmemu : u ∈ A ∩ B := Finset.mem_inter.mpr ⟨huA, huB⟩
    have hmemv : v ∈ A ∩ B := Finset.mem_inter.mpr ⟨hvA, hvB⟩
    have huv' := Finset.card_le_one.mp (hcross hij A hA B hB) u hmemu v hmemv
    exact huv huv'
  · have hmemu : u ∈ A ∩ B := Finset.mem_inter.mpr ⟨huA, hvB⟩
    have hmemv : v ∈ A ∩ B := Finset.mem_inter.mpr ⟨hvA, huB⟩
    have huv' := Finset.card_le_one.mp (hcross hij A hA B hB) u hmemu v hmemv
    exact huv huv'

private theorem support_inter_le_one_of_distance
    {V : Type*} [DecidableEq V] {A B : Finset V} {w : ℕ}
    (hA : A.card = w) (hB : B.card = w)
    (hdist : 2 * w - 3 ≤ (A \ B).card + (B \ A).card) :
    (A ∩ B).card ≤ 1 := by
  by_contra h
  have hinter : 2 ≤ (A ∩ B).card := by omega
  have hinter_le : (A ∩ B).card ≤ w := by
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq hA
  have hAB : (A \ B).card = w - (A ∩ B).card := by
    rw [Finset.card_sdiff, hA]
    congr 1
    rw [Finset.inter_comm]
  have hBA : (B \ A).card = w - (A ∩ B).card := by
    rw [Finset.card_sdiff, hB]
  rw [hAB, hBA] at hdist
  omega

theorem shadows_edge_disjoint_of_distance
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (P : I → Finset (Finset V))
    [(i : I) → Fintype (Shadow (P i)).edgeSet]
    (hsize : ∀ i A, A ∈ P i → A.card =  w)
    (hdist : ∀ ⦃i j : I⦄, i ≠ j → ∀ A ∈ P i, ∀ B ∈ P j,
      2 * w - 3 ≤ (A \ B).card + (B \ A).card) :
    (Set.univ : Set I).PairwiseDisjoint
      (fun i => (Shadow (P i)).edgeFinset) := by
  apply shadows_edge_disjoint P
  intro i j hij A hA B hB
  exact support_inter_le_one_of_distance (hsize i A hA) (hsize j B hB)
    (hdist hij A hA B hB)

theorem support_distance_of_inter_le_one
    {V : Type*} [DecidableEq V] {A A' : Finset V} {w : ℕ}
    (hA : A.card = w) (hA' : A'.card = w)
    (hinter : (A ∩ A').card ≤ 1) :
    2 * w - 3 ≤ (A \ A').card + (A' \ A).card := by
  rw [Finset.card_sdiff, Finset.card_sdiff, hA, hA']
  have hcomm : (A' ∩ A).card = (A ∩ A').card := by rw [Finset.inter_comm]
  rw [hcomm]
  have hle : (A ∩ A').card ≤ w := by
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq hA
  omega

/-- The union of all word supports in one information class. -/
def ClassSupport {V : Type*} [DecidableEq V] (P : Finset (Finset V)) : Finset V :=
  P.biUnion id

/-- The shadow induced on the union of the class's word supports. -/
abbrev SupportShadow {V : Type*} [DecidableEq V] (P : Finset (Finset V)) :
    SimpleGraph (ClassSupport P : Set V) :=
  (Shadow P).induce (ClassSupport P : Set V)

private theorem word_subset_classSupport {V : Type*} [DecidableEq V]
    {P : Finset (Finset V)} {A : Finset V} (hA : A ∈ P) : A ⊆ ClassSupport P :=
  fun _ hv => Finset.mem_biUnion.mpr ⟨A, hA, hv⟩

private theorem shadow_support_subset_classSupport {V : Type*} [DecidableEq V]
    (P : Finset (Finset V)) : (Shadow P).support ⊆ (ClassSupport P : Set V) := by
  rintro v ⟨u, _, A, hA, hv, _⟩
  exact word_subset_classSupport hA hv

private theorem supportShadow_spanningCoe {V : Type*} [DecidableEq V]
    (P : Finset (Finset V)) : (SupportShadow P).spanningCoe = Shadow P :=
  ((Shadow P).spanningCoe_induce_eq_self _).mpr (shadow_support_subset_classSupport P)

private theorem supportShadow_edgeSet_image {V : Type*} [DecidableEq V]
    (P : Finset (Finset V)) :
    (Function.Embedding.subtype (· ∈ (ClassSupport P : Set V))).sym2Map ''
      (SupportShadow P).edgeSet = (Shadow P).edgeSet :=
  (SimpleGraph.edgeSet_map _ _).symm.trans
    (congrArg SimpleGraph.edgeSet (supportShadow_spanningCoe P))

/-- Map each edge to the unordered pair of its ambient endpoints. -/

private theorem supportShadow_map_edgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finset (Finset V)) [DecidableRel (Shadow P).Adj] :
    (SupportShadow P).edgeFinset.map
      (Function.Embedding.subtype (· ∈ (ClassSupport P : Set V))).sym2Map =
    (Shadow P).edgeFinset := by
  apply Finset.coe_injective
  rw [Finset.coe_map, SimpleGraph.coe_edgeFinset, SimpleGraph.coe_edgeFinset]
  exact supportShadow_edgeSet_image P

private theorem supportShadow_card_edgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finset (Finset V)) [DecidableRel (Shadow P).Adj] :
    (SupportShadow P).edgeFinset.card = (Shadow P).edgeFinset.card := by
  rw [← supportShadow_map_edgeFinset P, Finset.card_map]

private theorem classSupport_card_ge_of_deletion {V : Type*} [Fintype V] [DecidableEq V]
    {P : Finset (Finset V)} {w t : ℕ} (hw : 0 < w) (htV : t ≤ Fintype.card V)
    (hsize : ∀ A ∈ P, A.card = w)
    (hdel : ∀ D : Finset V, D.card = t → ∃ A ∈ P, Disjoint D A) :
    w + t ≤ (ClassSupport P).card := by
  let U := ClassSupport P
  obtain ⟨R, hRU, hR⟩ :=
    Finset.exists_subset_card_eq (s := U) (min_le_right t U.card)
  -- First take as many support vertices as possible, then fill out the ambient deletion.
  obtain ⟨D, hRD, _, hD⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ R) (hR.trans_le (min_le_left _ _)) (by simpa using htV)
  obtain ⟨A, hA, hDA⟩ := hdel D hD
  have hRA : Disjoint R A := hDA.mono_left hRD
  have hUnion := Finset.card_le_card (Finset.union_subset hRU (word_subset_classSupport hA))
  rw [Finset.card_union_of_disjoint hRA, hR, hsize A hA] at hUnion
  change w + t ≤ U.card
  omega

private theorem supportShadow_survives_deletion {V : Type*} [Fintype V] [DecidableEq V]
    {P : Finset (Finset V)} {w t : ℕ} (hw : 1 < w)
    (hdelete : AppendixA.SurvivesDeletion (Shadow P) w t) :
    AppendixA.SurvivesDeletion (SupportShadow P) w t := by
  intro D hD
  let incl := Function.Embedding.subtype (· ∈ (ClassSupport P : Set V))
  obtain ⟨A, hA, hDA⟩ := hdelete (D.map incl) (by simpa using hD)
  rw [← supportShadow_spanningCoe P] at hA
  obtain ⟨Q, hQ, hQA⟩ := (SimpleGraph.isNClique_map_iff hw).mp hA
  exact ⟨Q, hQ, (Finset.disjoint_map incl).mp (hQA ▸ hDA)⟩

private theorem supportShadow_cliqueFree_iff {V : Type*} [DecidableEq V]
    (P : Finset (Finset V)) {k : ℕ} (hk : 1 < k) :
    (SupportShadow P).CliqueFree k ↔ (Shadow P).CliqueFree k := by
  rw [← supportShadow_spanningCoe P]
  simp only [CliqueFree, isNClique_map_iff hk, not_exists, not_and]
  constructor
  · intro h A Q hQ _
    exact h Q hQ
  · intro h Q hQ
    exact h _ Q hQ rfl

private theorem supportShadow_minDegree {V : Type*} [Fintype V] [DecidableEq V]
    {P : Finset (Finset V)} [Nonempty (ClassSupport P : Set V)]
    [DecidableRel (Shadow P).Adj] {w : ℕ}
    (hsize : ∀ A ∈ P, A.card = w) :
    w - 1 ≤ (SupportShadow P).minDegree := by
  let restrict (A : Finset V) := A.subtype (· ∈ ClassSupport P)
  let Q := P.image restrict
  have hgraph : SupportShadow P = Shadow Q := by
    ext u v
    change (u.val ≠ v.val ∧ ∃ A ∈ P, u.val ∈ A ∧ v.val ∈ A) ↔
      (u ≠ v ∧ ∃ B ∈ Q, u ∈ B ∧ v ∈ B)
    constructor
    · rintro ⟨hne, A, hA, hu, hv⟩
      exact ⟨fun he => hne (congrArg Subtype.val he), restrict A,
        Finset.mem_image_of_mem restrict hA, Finset.mem_subtype.mpr hu, Finset.mem_subtype.mpr hv⟩
    · rintro ⟨hne, B, hB, hu, hv⟩
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
      exact ⟨fun he => hne (Subtype.ext he), A, hA,
        Finset.mem_subtype.mp hu, Finset.mem_subtype.mp hv⟩
  have hQsize : ∀ B ∈ Q, B.card = w := by
    intro B hB
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
    change (A.subtype (· ∈ ClassSupport P)).card = w
    rw [Finset.card_subtype, Finset.filter_eq_self.mpr (word_subset_classSupport hA), hsize A hA]
  have hQcover (v : (ClassSupport P : Set V)) : ∃ B ∈ Q, v ∈ B := by
    obtain ⟨A, hA, hv⟩ := Finset.mem_biUnion.mp v.property
    exact ⟨restrict A, Finset.mem_image_of_mem restrict hA, Finset.mem_subtype.mpr hv⟩
  let : DecidableRel (Shadow Q).Adj := Classical.decRel _
  have hiso : SupportShadow P ≃g Shadow Q := hgraph ▸ SimpleGraph.Iso.refl
  exact (shadow_min_degree_of_mem hQsize hQcover).trans_eq hiso.minDegree_eq.symm

theorem nonclique_shadow_edge_lower_of_ambient_deletion
    {V : Type*} [Fintype V] [DecidableEq V]
    {P : Finset (Finset V)} [DecidableRel (Shadow P).Adj] {w t : ℕ}
    (ht : 1 ≤ t) (hw : t + 3 < w) (htV : t ≤ Fintype.card V)
    (hsize : ∀ A ∈ P, A.card = w)
    (hdel : ∀ D : Finset V, D.card = t → ∃ A ∈ P, Disjoint D A)
    (hfree : (Shadow P).CliqueFree (w + t)) :
    AppendixA.B w t ≤ (Shadow P).edgeFinset.card := by
  have hcard : Fintype.card (ClassSupport P : Set V) = (ClassSupport P).card :=
    @Fintype.card_coe V (ClassSupport P) (inferInstance : Fintype (ClassSupport P : Set V))
  have hsizeU : w + t ≤ Fintype.card (ClassSupport P : Set V) :=
    (classSupport_card_ge_of_deletion (by omega) htV hsize hdel).trans_eq hcard.symm
  let : Nonempty (ClassSupport P : Set V) := Fintype.card_pos_iff.mp (by omega)
  have hlower := AppendixA.nonclique_edge_bound (SupportShadow P) ht hw hsizeU
    ((supportShadow_cliqueFree_iff P (by omega)).mpr hfree)
    (supportShadow_minDegree hsize)
    (supportShadow_survives_deletion (by omega) (shadow_survives_deletion hsize hdel))
  rwa [supportShadow_card_edgeFinset P] at hlower

theorem shadow_degree_lower_of_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {P : Finset (Finset V)} {w : ℕ}
    [DecidableRel (Shadow P).Adj]
    (hsize : ∀ A ∈ P, A.card = w) {v : V}
    (hv : v ∈ (Shadow P).support) :
    w - 1 ≤ (Shadow P).degree v := by
  obtain ⟨u, huv⟩ := (SimpleGraph.mem_support (Shadow P)).mp hv
  obtain ⟨hne, A, hA, hvA, huA⟩ := huv
  have hsub : (A.erase v : Set V) ⊆ (Shadow P).neighborSet v := by
    intro z hz
    have hzA : z ∈ A := Finset.mem_of_mem_erase hz
    have hzneq : z ≠ v := by
      intro heq
      subst z
      exact (Finset.mem_erase.mp hz).1 rfl
    exact shadow_adj_of_mem hA hvA hzA hzneq.symm
  have hcard : (A.erase v).card = w - 1 := by
    rw [Finset.card_erase_of_mem hvA, hsize A hA]
  have hcard' : (A.erase v : Set V).ncard = w - 1 := by
    rw [Set.ncard_coe_finset, hcard]
  have hle := Set.ncard_le_ncard hsub
  exact hcard'.symm ▸ hle.trans_eq ((Shadow P).ncard_neighborSet v)

end CPECCBridge
