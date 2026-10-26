/- GID: D5/S3/Combinatorics/Graph/MutualVisibility/RootComparability
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MutualVisibility/RootComparability
   mirror-E: none(waiver:no-computational-evidence)
   anchors: []
   utility: none
   digest: A small actual cut forces every stranded pair to be comparable towards a clean root. -/

import D5.S3.Combinatorics.Graph.MutualVisibility.CyclicIntervals
import D5.S3.Combinatorics.Graph.MutualVisibility.SingletonCore
import D5.S3.Combinatorics.Graph.MutualVisibility.CleanRoots

/-! A maximal pair-complete configuration supplies a sparse witness for one actual cut. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.MutualVisibility

open SimpleGraph
open scoped symmDiff

variable {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}

omit [Fintype V] in
/-- Deleting labels between two nested feasible configurations meets the same actual cut. -/
private theorem subset_cut_payment [Finite V]
    (C : Finset (Configuration H)) (s T U : Configuration H)
    (hUT : U.val ⊆ T.val)
    (hT : CutReach (reconfiguration H) C s T ∨ T ∈ C)
    (hU : ¬ CutReach (reconfiguration H) C s U) :
    ∃ Q ∈ C, U.val ⊆ Q.val ∧ Q.val ⊆ T.val := by
  classical
  let : Fintype V := Fintype.ofFinite V
  rcases hT with hT | hTC
  · let E : Set (Configuration H) := {Q | U.val ⊆ Q.val ∧ Q.val ⊆ T.val ∧
        ¬ CutReach (reconfiguration H) C s Q}
    have hE : E.Nonempty := ⟨U, Finset.Subset.refl _, hUT, hU⟩
    obtain ⟨Q, hQ, hmax⟩ := Set.exists_max_image E (fun Q => Q.val.card) (Set.toFinite E) hE
    have hne : Q.val ≠ T.val := by
      intro he
      exact hQ.2.2 (Subtype.ext he ▸ hT)
    obtain ⟨x, hxT, hxQ⟩ := Finset.exists_of_ssubset
      (Finset.ssubset_iff_subset_ne.mpr ⟨hQ.2.1, hne⟩)
    have hPvis : Visible H (insert x Q.val) :=
      visible_mono (Finset.insert_subset_iff.mpr ⟨hxT, hQ.2.1⟩) T.property
    let P : Configuration H := ⟨insert x Q.val, hPvis⟩
    have hP : CutReach (reconfiguration H) C s P := by
      by_contra hn
      have hb := hmax P ⟨hQ.1.trans (Finset.subset_insert _ _),
        Finset.insert_subset_iff.mpr ⟨hxT, hQ.2.1⟩, hn⟩
      have hc : P.val.card = Q.val.card + 1 := Finset.card_insert_of_notMem hxQ
      omega
    have hQC : Q ∈ C := by
      by_contra hn
      have hQP : (reconfiguration H).Adj Q P := mixedMove_insert H Q.val hxQ
      exact hQ.2.2 (cutReach_step hP hQP.symm hn)
    exact ⟨Q, hQC, hQ.1, hQ.2.1⟩
  · exact ⟨T, hTC, hUT, Finset.Subset.refl _⟩

theorem stranded_singletons (hH : H.Connected) (C : Finset (Configuration H))
    (s : Configuration H) {w : V} (hc : C.card < Fintype.card V)
    (hw : CleanRoot C w)
    (hwout : ¬ CutReach (reconfiguration H) C s ⟨{w}, visible_singleton H w⟩) :
    ∀ x, ¬ CutReach (reconfiguration H) C s ⟨{x}, visible_singleton H x⟩ := by
  intro x hr
  have hwC : (⟨{w}, visible_singleton H w⟩ : Configuration H) ∉ C := by
    simpa [deletedLabels] using hw.1
  exact hwout (cutReach_trans hr (singleton_core hH C hc hr.choose_spec.choose hwC))

theorem stranded_pair_labels (hH : H.Connected) (C : Finset (Configuration H))
    (s : Configuration H)
    (hsingle : ∀ x, ¬ CutReach (reconfiguration H) C s ⟨{x}, visible_singleton H x⟩)
    {u v : V} (huv : u ≠ v)
    (hr : CutReach (reconfiguration H) C s ⟨{u, v}, visible_pair hH u v⟩) :
    u ∈ deletedLabels C ∧ v ∈ deletedLabels C := by
  have hlabel (a b : V) (hab : a ≠ b)
      (hpair : CutReach (reconfiguration H) C s ⟨{a, b}, visible_pair hH a b⟩) :
      a ∈ deletedLabels C := by
    have hAdj : (reconfiguration H).Adj ⟨{a, b}, visible_pair hH a b⟩
        ⟨{a}, visible_singleton H a⟩ := by
      have hm := mixedMove_erase H ({a, b} : Finset V) (x := b) (by simp)
      have he : ({a, b} : Finset V).erase b = {a} := by
        ext z
        simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        aesop
      rw [he] at hm
      exact hm
    have hC : (⟨{a}, visible_singleton H a⟩ : Configuration H) ∈ C := by
      by_contra hn
      exact hsingle a (cutReach_step hpair hAdj hn)
    simpa [deletedLabels] using hC
  exact ⟨hlabel u v huv hr, hlabel v u huv.symm (by simpa [Finset.pair_comm] using hr)⟩

omit [Fintype V] in
theorem outside_move_shape {S T : Finset V} {y : V}
    (hy : y ∉ S) (hyT : y ∈ T) (hsub : T ⊆ insert y S)
    (h : MixedMove H S T) :
    T = insert y S ∨ ∃ x ∈ S, H.Adj x y ∧ T = insert y (S.erase x) := by
  classical
  rcases h.2 with htar | ⟨x, z, hx, hz, hxy⟩
  · left
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp htar
    have hya : y = a := by
      have hymem : y ∈ S ∆ T := Finset.mem_symmDiff.mpr (Or.inr ⟨hyT, hy⟩)
      simpa [ha] using hymem
    apply Finset.Subset.antisymm hsub
    apply Finset.insert_subset_iff.mpr ⟨hyT, ?_⟩
    intro q hqS
    by_contra hqT
    have hqsy : q ∈ S ∆ T := Finset.mem_symmDiff.mpr (Or.inl ⟨hqS, hqT⟩)
    have hqy : q = y := by simpa only [ha, Finset.mem_singleton, ← hya] using hqsy
    exact hy (hqy ▸ hqS)
  · right
    have hyz : y = z := by
      have hymem : y ∈ T \ S := Finset.mem_sdiff.mpr ⟨hyT, hy⟩
      simpa [hz] using hymem
    subst z
    have hxmem : x ∈ S := (Finset.mem_sdiff.mp (by rw [hx]; simp)).1
    have hxnotT : x ∉ T :=
      (Finset.mem_sdiff.mp (show x ∈ S \ T by rw [hx]; simp)).2
    refine ⟨x, hxmem, hxy, ?_⟩
    ext q
    constructor
    · intro hqT
      rcases Finset.mem_insert.mp (hsub hqT) with hqy | hqS
      · exact Finset.mem_insert.mpr (Or.inl hqy)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr
          ⟨fun hqx => hxnotT (hqx ▸ hqT), hqS⟩))
    · intro hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hyT
      · obtain ⟨hqx, hqS⟩ := Finset.mem_erase.mp hq
        by_contra hqT
        have hqdiff : q ∈ S \ T := Finset.mem_sdiff.mpr ⟨hqS, hqT⟩
        exact hqx (by simpa only [hx, Finset.mem_singleton] using hqdiff)

private theorem sparse_local_neighbor_bound (S : Configuration H) {y : V}
    (hy : y ∉ S.val)
    (hsparse : ∀ x ∈ S.val, ∀ z ∈ S.val, H.Adj x y → H.Adj z y → x = z) :
    let L := localCutClass ((reconfiguration H).neighborFinset S) S.val y
    L.card ≤ 2 ∧ (¬ Visible H (insert y S.val) → L.card ≤ 1) := by
  classical
  dsimp only
  let L := localCutClass ((reconfiguration H).neighborFinset S) S.val y
  let A := L.filter fun T => T.val = insert y S.val
  let P := L.filter fun T => T.val ≠ insert y S.val
  change L.card ≤ 2 ∧ (¬ Visible H (insert y S.val) → L.card ≤ 1)
  have hA : A.card ≤ 1 := Finset.card_le_one.mpr (by
    intro T hT U hU
    exact Subtype.ext ((Finset.mem_filter.mp hT).2.trans (Finset.mem_filter.mp hU).2.symm))
  have hP : P.card ≤ 1 := Finset.card_le_one.mpr (by
    intro T hT U hU
    obtain ⟨hTL, hTne⟩ := Finset.mem_filter.mp hT
    obtain ⟨hUL, hUne⟩ := Finset.mem_filter.mp hU
    obtain ⟨hTN, hyT, hsubT⟩ := Finset.mem_filter.mp hTL
    obtain ⟨hUN, hyU, hsubU⟩ := Finset.mem_filter.mp hUL
    have ht := outside_move_shape hy hyT hsubT ((SimpleGraph.mem_neighborFinset _ _ _).mp hTN)
    have hu := outside_move_shape hy hyU hsubU ((SimpleGraph.mem_neighborFinset _ _ _).mp hUN)
    obtain ⟨x, hxS, hxy, hxT⟩ := ht.resolve_left hTne
    obtain ⟨z, hzS, hzy, hzU⟩ := hu.resolve_left hUne
    have he := hsparse x hxS z hzS hxy hzy
    exact Subtype.ext (hxT.trans (he ▸ hzU.symm)))
  have hpart : A.card + P.card = L.card :=
    Finset.card_filter_add_card_filter_not (s := L) (fun T => T.val = insert y S.val)
  refine ⟨by omega, ?_⟩
  intro hn
  have he : A = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro T hT
    have hv := (Finset.mem_filter.mp hT).2
    exact hn (hv ▸ T.property)
  have ha0 : A.card = 0 := by rw [he]; simp
  omega

omit [Fintype V] [DecidableEq V] in
private theorem configuration_enumeration (S : Configuration H) :
    ∃ e : Fin S.val.card ↪ V, Finset.univ.map e = S.val := by
  classical
  let e : Fin S.val.card ↪ V :=
    ⟨fun i => (S.val.equivFin.symm i).val,
      fun i j h => S.val.equivFin.symm.injective (Subtype.ext h)⟩
  refine ⟨e, ?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hz
    exact (S.val.equivFin.symm i).property
  · intro hz
    refine Finset.mem_map.mpr ⟨S.val.equivFin ⟨z, hz⟩, Finset.mem_univ _, ?_⟩
    change ((S.val.equivFin.symm (S.val.equivFin ⟨z, hz⟩)).val) = z
    rw [Equiv.symm_apply_apply]

omit [Fintype V] in
private theorem extension_two_cuts [Finite V] (C : Finset (Configuration H)) (s S : Configuration H)
    (hm : 2 ≤ S.val.card) {y : V} (hy : y ∉ S.val)
    (hvis : Visible H (insert y S.val))
    (hr : CutReach (reconfiguration H) C s ⟨insert y S.val, hvis⟩)
    (hend : ∀ T : Configuration H, T.val.card = 2 → y ∈ T.val →
      ¬ CutReach (reconfiguration H) C s T) :
    2 ≤ (localCutClass C S.val y).card := by
  classical
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨e, he⟩ := configuration_enumeration S
  have hy' : y ∉ Finset.univ.map e := by rwa [he]
  have hsub (i : Fin S.val.card) (k : ℕ) : mappedArc e i k ⊆ S.val := by
    have hh : mappedArc e i k ⊆ Finset.univ.map e :=
      Finset.map_subset_map.mpr (Finset.subset_univ _)
    exact hh.trans (Finset.subset_of_eq he)
  have hv (i : Fin S.val.card) (_hi : i ∈ (Finset.univ : Finset (Fin S.val.card))) :
      Visible H (insert y (mappedArc e i (S.val.card - 1))) :=
    visible_mono (Finset.insert_subset_insert y (hsub i _)) hvis
  have hstart : ∀ i (hi : i ∈ (Finset.univ : Finset (Fin S.val.card))),
      CutReach (reconfiguration H) C s
        ⟨insert y (mappedArc e i (S.val.card - 1)), hv i hi⟩ ∨
      (⟨insert y (mappedArc e i (S.val.card - 1)), hv i hi⟩ : Configuration H) ∈ C := by
    intro i hi
    by_cases hC : (⟨insert y (mappedArc e i (S.val.card - 1)), hv i hi⟩ : Configuration H) ∈ C
    · exact Or.inr hC
    · left
      have hstep := mappedArc_insert_step H e i (by omega : S.val.card - 1 < S.val.card) hy'
      have hfull : mappedArc e i (S.val.card - 1 + 1) = S.val := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ S.val.card)]
        apply Finset.eq_of_subset_of_card_le (hsub i _)
        rw [mappedArc_card e i le_rfl]
      rw [hfull] at hstep
      have hAdj : (reconfiguration H).Adj
          ⟨insert y (mappedArc e i (S.val.card - 1)), hv i hi⟩ ⟨insert y S.val, hvis⟩ := hstep
      exact cutReach_step hr hAdj.symm hC
  have hb := cyclic_outside_cut_bound H e hm hy' C s Finset.univ hv hstart hend
  simp only [Finset.card_univ, Fintype.card_fin, he] at hb
  have hsubC : (C.filter fun T => y ∈ T.val ∧ T.val ⊆ insert y S.val ∧
      T.val ≠ insert y S.val) ⊆ localCutClass C S.val y := by
    intro T hT
    obtain ⟨hTC, hyT, hTS, _⟩ := Finset.mem_filter.mp hT
    exact Finset.mem_filter.mpr ⟨hTC, hyT, hTS⟩
  exact hm.trans (hb.trans (Finset.card_le_card hsubC))

omit [Fintype V] in
private theorem pair_to_singleton (T : Configuration H) {y : V}
    (hcard : T.val.card = 2) (hy : y ∈ T.val) :
    (reconfiguration H).Adj T ⟨{y}, visible_singleton H y⟩ := by
  classical
  change MixedMove H T.val {y}
  refine ⟨?_, Or.inl ?_⟩
  · intro he
    have := congrArg Finset.card he
    simp only [Finset.card_singleton] at this
    omega
  · have he : T.val ∆ {y} = T.val.erase y := by
      ext z
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
      aesop
    rw [he, Finset.card_erase_of_mem hy, hcard]

private theorem sparse_local_cut_bound (hH : H.Connected)
    (C : Finset (Configuration H)) (s S : Configuration H)
    (hm : 2 ≤ S.val.card) (hs : CutReach (reconfiguration H) C s S)
    (hsingle : ∀ x, ¬ CutReach (reconfiguration H) C s ⟨{x}, visible_singleton H x⟩)
    (hmax : ∀ y, y ∉ S.val → ∀ hv : Visible H (insert y S.val),
      CutReach (reconfiguration H) C s ⟨insert y S.val, hv⟩ →
      ∃ x ∈ S.val, ¬ CutReach (reconfiguration H) C s ⟨{y, x}, visible_pair hH y x⟩)
    {y : V} (hy : y ∉ S.val)
    (hsparse : ∀ x ∈ S.val, ∀ z ∈ S.val, H.Adj x y → H.Adj z y → x = z) :
    (localCutClass ((reconfiguration H).neighborFinset S) S.val y).card ≤
      (localCutClass C S.val y).card := by
  classical
  let L := localCutClass ((reconfiguration H).neighborFinset S) S.val y
  let CY := localCutClass C S.val y
  have hL := sparse_local_neighbor_bound S hy hsparse
  change L.card ≤ CY.card
  have hQmem (Q : Configuration H) (hQC : Q ∈ C) (hyQ : y ∈ Q.val)
      (hQS : Q.val ⊆ insert y S.val) : Q ∈ CY :=
    Finset.mem_filter.mpr ⟨hQC, hyQ, hQS⟩
  by_cases hyD : y ∈ deletedLabels C
  · let Y : Configuration H := ⟨{y}, visible_singleton H y⟩
    have hYC : Y ∈ C := by simpa [Y, deletedLabels] using hyD
    have hY : Y ∈ CY := hQmem Y hYC (by simp [Y]) (by simp [Y])
    have hCY : 1 ≤ CY.card := Finset.card_pos.mpr ⟨Y, hY⟩
    by_cases hv : Visible H (insert y S.val)
    · have hex : ∃ Q ∈ CY, Q ≠ Y := by
        let T : Configuration H := ⟨insert y S.val, hv⟩
        by_cases hTC : T ∈ C
        · refine ⟨T, hQmem T hTC (by simp [T]) (by simp [T]), ?_⟩
          intro he
          have hc := congrArg (fun Q : Configuration H => Q.val.card) he
          have htcard : T.val.card = S.val.card + 1 := Finset.card_insert_of_notMem hy
          have hycard : Y.val.card = 1 := Finset.card_singleton y
          omega
        · have hAdj : (reconfiguration H).Adj S T := mixedMove_insert H S.val hy
          have hr := cutReach_step hs hAdj hTC
          obtain ⟨x, hxS, hxout⟩ := hmax y hy hv hr
          let U : Configuration H := ⟨{y, x}, visible_pair hH y x⟩
          have hUT : U.val ⊆ T.val := by simp [U, T, Finset.insert_subset_iff, hxS]
          obtain ⟨Q, hQC, hUQ, hQT⟩ := subset_cut_payment C s T U hUT (Or.inl hr) hxout
          refine ⟨Q, hQmem Q hQC (hUQ (by simp [U])) hQT, ?_⟩
          intro he
          have hxQ : x ∈ Q.val := hUQ (by simp [U])
          rw [he] at hxQ
          have hxy : x = y := by simpa [Y] using hxQ
          exact hy (hxy ▸ hxS)
      obtain ⟨Q, hQ, hQY⟩ := hex
      have htwo : 2 ≤ CY.card := by
        have hsub : ({Q, Y} : Finset (Configuration H)) ⊆ CY := by
          simp [Finset.insert_subset_iff, hQ, hY]
        have hc := Finset.card_le_card hsub
        simpa [hQY] using hc
      exact hL.1.trans htwo
    · exact (hL.2 hv).trans hCY
  · have hyC : (⟨{y}, visible_singleton H y⟩ : Configuration H) ∉ C := by
      simpa [deletedLabels] using hyD
    have hend : ∀ T : Configuration H, T.val.card = 2 → y ∈ T.val →
        ¬ CutReach (reconfiguration H) C s T := by
      intro T hT hyT hr
      exact hsingle y (cutReach_step hr (pair_to_singleton T hT hyT) hyC)
    by_cases hv : Visible H (insert y S.val)
    · let T : Configuration H := ⟨insert y S.val, hv⟩
      by_cases hTC : T ∈ C
      · have hT : T ∈ CY := hQmem T hTC (by simp [T]) (by simp [T])
        by_cases hex : ∃ U ∈ L, U.val ≠ insert y S.val
        · obtain ⟨U, hUL, hUne⟩ := hex
          obtain ⟨hUN, hyU, hUS⟩ := Finset.mem_filter.mp hUL
          have hstart : CutReach (reconfiguration H) C s U ∨ U ∈ C := by
            by_cases hUC : U ∈ C
            · exact Or.inr hUC
            · exact Or.inl (cutReach_step hs ((SimpleGraph.mem_neighborFinset _ _ _).mp hUN) hUC)
          let Y : Configuration H := ⟨{y}, visible_singleton H y⟩
          obtain ⟨Q, hQC, hYQ, hQU⟩ := subset_cut_payment C s U Y
            (by simpa [Y] using hyU) hstart (hsingle y)
          have hQ : Q ∈ CY := hQmem Q hQC (hYQ (by simp [Y])) (hQU.trans hUS)
          have hQT : Q ≠ T := by
            intro he
            have hTU : T.val ⊆ U.val := he ▸ hQU
            exact hUne (Finset.Subset.antisymm hUS hTU)
          have htwo : 2 ≤ CY.card := by
            have hsub : ({Q, T} : Finset (Configuration H)) ⊆ CY := by
              simp [Finset.insert_subset_iff, hQ, hT]
            have hc := Finset.card_le_card hsub
            simpa [hQT] using hc
          exact hL.1.trans htwo
        · have hLone : L.card ≤ 1 := Finset.card_le_one.mpr (by
            intro U hU Q hQ
            have hUeq : U.val = insert y S.val := by
              by_contra hn
              exact hex ⟨U, hU, hn⟩
            have hQeq : Q.val = insert y S.val := by
              by_contra hn
              exact hex ⟨Q, hQ, hn⟩
            exact Subtype.ext (hUeq.trans hQeq.symm))
          exact hLone.trans (Finset.card_pos.mpr ⟨T, hT⟩)
      · have hAdj : (reconfiguration H).Adj S T := mixedMove_insert H S.val hy
        exact hL.1.trans (extension_two_cuts C s S hm hy hv (cutReach_step hs hAdj hTC) hend)
    · have hLone := hL.2 hv
      by_cases hzero : L = ∅
      · simp only [hzero, Finset.card_empty, Nat.zero_le]
      · obtain ⟨U, hU⟩ := Finset.nonempty_iff_ne_empty.mpr hzero
        obtain ⟨hUN, hyU, hUS⟩ := Finset.mem_filter.mp hU
        have hstart : CutReach (reconfiguration H) C s U ∨ U ∈ C := by
          by_cases hUC : U ∈ C
          · exact Or.inr hUC
          · exact Or.inl (cutReach_step hs ((SimpleGraph.mem_neighborFinset _ _ _).mp hUN) hUC)
        let Y : Configuration H := ⟨{y}, visible_singleton H y⟩
        obtain ⟨Q, hQC, hYQ, hQU⟩ := subset_cut_payment C s U Y
          (by simpa [Y] using hyU) hstart (hsingle y)
        exact hLone.trans (Finset.card_pos.mpr ⟨Q,
          hQmem Q hQC (hYQ (by simp [Y])) (hQU.trans hUS)⟩)

private theorem sparse_witness_degree (hH : H.Connected)
    (C : Finset (Configuration H)) (s S : Configuration H)
    (hm : 2 ≤ S.val.card) (hs : CutReach (reconfiguration H) C s S)
    (hsingle : ∀ x, ¬ CutReach (reconfiguration H) C s ⟨{x}, visible_singleton H x⟩)
    (hpair : ∀ u ∈ S.val, ∀ v ∈ S.val, u ≠ v →
      CutReach (reconfiguration H) C s ⟨{u, v}, visible_pair hH u v⟩)
    (hmax : ∀ y, y ∉ S.val → ∀ hv : Visible H (insert y S.val),
      CutReach (reconfiguration H) C s ⟨insert y S.val, hv⟩ →
      ∃ x ∈ S.val, ¬ CutReach (reconfiguration H) C s ⟨{y, x}, visible_pair hH y x⟩)
    (hsparse : ∀ y, y ∉ S.val → ∀ x ∈ S.val, ∀ z ∈ S.val,
      H.Adj x y → H.Adj z y → x = z) :
    (reconfiguration H).degree S ≤ C.card := by
  classical
  have hSD : S.val ⊆ deletedLabels C := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := Finset.exists_mem_ne (by omega : 1 < S.val.card) x
    exact (stranded_pair_labels hH C s hsingle hzx.symm (hpair x hx z hz hzx.symm)).1
  let f (x : V) : Configuration H := ⟨{x}, visible_singleton H x⟩
  have hinj : Function.Injective f := by
    intro x y he
    exact Finset.singleton_injective (congrArg Subtype.val he)
  have hsub : S.val.image f ⊆ C.filter fun T => T.val ⊆ S.val := by
    intro T hT
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hT
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simpa [f, deletedLabels] using hSD hx
    · simpa [f] using hx
  have hinner : S.val.card ≤ (C.filter fun T => T.val ⊆ S.val).card := by
    have := Finset.card_le_card hsub
    simpa [Finset.card_image_of_injective _ hinj] using this
  have hlocal : (∑ y ∈ Finset.univ \ S.val,
      (localCutClass ((reconfiguration H).neighborFinset S) S.val y).card) ≤
      ∑ y ∈ Finset.univ \ S.val, (localCutClass C S.val y).card := by
    apply Finset.sum_le_sum
    intro y hy
    have hyS := (Finset.mem_sdiff.mp hy).2
    exact sparse_local_cut_bound hH C s S hm hs hsingle hmax hyS (hsparse y hyS)
  have hbudget := joint_cut_budget C S.val (Finset.univ \ S.val) Finset.sdiff_disjoint
    ∅ (by simp) (by simp) (by simp)
  have hdeg := degree_by_label_classes H S
  simp only [Finset.card_empty, Nat.add_zero] at hbudget
  omega

/-- A pair stranded from a clean root by an actual cut below minimum degree is comparable. -/
theorem stranded_pair_comparable (hH : H.Connected)
    (C : Finset (Configuration H)) (s : Configuration H) {w u v : V}
    (hc : C.card < (reconfiguration H).minDegree) (hw : CleanRoot C w)
    (huv : u ≠ v)
    (hB : CutReach (reconfiguration H) C s ⟨{u, v}, visible_pair hH u v⟩)
    (hwout : ¬ CutReach (reconfiguration H) C s ⟨{w}, visible_singleton H w⟩) :
    Dominates H w u v ∨ Dominates H w v u := by
  classical
  have hcn : C.card < Fintype.card V := hc.trans_le minDegree_le_host_order
  have hsingle := stranded_singletons hH C s hcn hw hwout
  have hlabels := stranded_pair_labels hH C s hsingle huv hB
  have huw : u ≠ w := fun he => hw.1 (he ▸ hlabels.1)
  have hvw : v ≠ w := fun he => hw.1 (he ▸ hlabels.2)
  have hnv := clean_root_pair_nonvisible hH C s huv hw hlabels.1 hlabels.2 hB hwout
  rcases nonvisible_triple_choice huw hvw huv hnv with hsep | hdom | hdom
  · exfalso
    let E : Set (Configuration H) := {T | CutReach (reconfiguration H) C s T ∧
      ({u, v} : Finset V) ⊆ T.val ∧
      ∀ a ∈ T.val, ∀ b ∈ T.val, a ≠ b →
        CutReach (reconfiguration H) C s ⟨{a, b}, visible_pair hH a b⟩}
    have hE : E.Nonempty := by
      refine ⟨⟨{u, v}, visible_pair hH u v⟩, hB, Finset.Subset.refl _, ?_⟩
      intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (hab rfl).elim
      · exact hB
      · simpa [Finset.pair_comm] using hB
      · exact (hab rfl).elim
    obtain ⟨S, hS, hmaxcard⟩ := Set.exists_max_image E (fun T => T.val.card) (Set.toFinite E) hE
    have hm : 2 ≤ S.val.card := by
      have hle := Finset.card_le_card hS.2.1
      simpa [huv] using hle
    have hpair := hS.2.2
    have hmax : ∀ y, y ∉ S.val → ∀ hv : Visible H (insert y S.val),
        CutReach (reconfiguration H) C s ⟨insert y S.val, hv⟩ →
        ∃ x ∈ S.val, ¬ CutReach (reconfiguration H) C s ⟨{y, x}, visible_pair hH y x⟩ := by
      intro y hy hv hr
      by_contra hn
      push Not at hn
      have hnew : (⟨insert y S.val, hv⟩ : Configuration H) ∈ E := by
        refine ⟨hr, hS.2.1.trans (Finset.subset_insert _ _), ?_⟩
        intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with hay | haS
        · rcases Finset.mem_insert.mp hb with hby | hbS
          · exact (hab (hay.trans hby.symm)).elim
          · simpa only [hay] using hn b hbS
        · rcases Finset.mem_insert.mp hb with hby | hbS
          · simpa only [hby, Finset.pair_comm] using hn a haS
          · exact hpair a haS b hbS hab
      have hb := hmaxcard _ hnew
      have hcard : (insert y S.val).card = S.val.card + 1 := Finset.card_insert_of_notMem hy
      change (insert y S.val).card ≤ S.val.card at hb
      omega
    have hSD : S.val ⊆ deletedLabels C := by
      intro a ha
      obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne (by omega : 1 < S.val.card) a
      exact (stranded_pair_labels hH C s hsingle hba.symm (hpair a ha b hb hba.symm)).1
    have hwS : w ∉ S.val := fun h => hw.1 (hSD h)
    have hnonvis : ∀ a ∈ S.val, ∀ b ∈ S.val, a ≠ b → ¬ Visible H {a, b, w} := by
      intro a ha b hb hab
      exact clean_root_pair_nonvisible hH C s hab hw (hSD ha) (hSD hb)
        (hpair a ha b hb hab) hwout
    have hmandatory : ∀ a ∈ S.val, ∀ b ∈ S.val, a ≠ b → Mandatory H w a b := by
      by_cases hthree : 3 ≤ S.val.card
      · exact root_hub hH S.property hthree hwS hnonvis
      · have he : S.val = {u, v} := by
          apply Eq.symm
          apply Finset.eq_of_subset_of_card_le hS.2.1
          simpa [huv] using (show S.val.card ≤ 2 by omega)
        intro a ha b hb hab
        rw [he] at ha hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact (hab rfl).elim
        · exact hsep
        · exact mandatory_symm hsep
        · exact (hab rfl).elim
    have hfar : ∀ a ∈ S.val, ∀ b ∈ S.val, a ≠ b → 4 ≤ H.dist a b := by
      intro a ha b hb hab
      have haw : a ≠ w := fun he => hwS (he ▸ ha)
      have hbw : b ≠ w := fun he => hwS (he ▸ hb)
      have han := clean_root_pair_nonadjacent hH C s hab hw (hSD ha) (hSD hb)
        (hpair a ha b hb hab) hwout
      have hbn := clean_root_pair_nonadjacent hH C s hab.symm hw (hSD hb) (hSD ha)
        (hpair b hb a ha hab.symm) hwout
      have hap := (hH a w).pos_dist_of_ne haw
      have hbp := (hH b w).pos_dist_of_ne hbw
      have haone : H.dist a w ≠ 1 := fun he => han (dist_eq_one_iff_adj.mp he)
      have hbone : H.dist b w ≠ 1 := fun he => hbn (dist_eq_one_iff_adj.mp he)
      have hd := mandatory_dist hH (hmandatory a ha b hb hab)
      rw [H.dist_comm (u := w) (v := b)] at hd
      omega
    have hsparse : ∀ y, y ∉ S.val → ∀ x ∈ S.val, ∀ z ∈ S.val,
        H.Adj x y → H.Adj z y → x = z := by
      intro y _hy x hx z hz hxy hzy
      by_contra hne
      have hdist := hfar x hx z hz hne
      have hle := H.dist_le (Walk.cons hxy (Walk.cons hzy.symm .nil))
      simp only [Walk.length_cons, Walk.length_nil] at hle
      omega
    have hdegree := sparse_witness_degree hH C s S hm hS.1 hsingle hpair hmax hsparse
    have hmin := (reconfiguration H).minDegree_le_degree S
    omega
  · exact Or.inl hdom
  · exact Or.inr hdom

end D5.S3.Combinatorics.Graph.MutualVisibility
