/- GID: D5/S3/ObserverMemory/Trajectories/GraphScheduledSelectionCapacity
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Trajectories/GraphScheduledSelectionCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Canonical register outputs for graph scheduled selection. -/

import D5.S3.ObserverMemory.Trajectories.GraphScheduledSelection

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.Trajectories.GraphScheduledSelectionCapacity

open Finset GraphScheduledSelection
open scoped BigOperators Classical

private theorem initial_zero_support {r c : ℕ} (G : SimpleGraph (Fin r))
    (hr : 3 ≤ r) (hc : 1 ≤ c) (hcB : c ≤ initialLength r)
    (w : Finset ℕ) (hw : IsPrefix c w) :
    FirstSelected r G c w ↔ w = Icc 1 (c - 1) := by
  constructor
  · rintro ⟨ht, hp⟩
    have hz : c ∉ w := by
      rcases ht with ht | ht | ht | ht
      · exact ht.2.2
      · dsimp [identityEnd] at ht; omega
      · obtain ⟨t, u, v, _, _, _, _, he⟩ := ht
        dsimp [identityEnd] at he; omega
      · obtain ⟨i, hi, _, _, ht | ht⟩ := ht
        · obtain ⟨j, hj, _, he, _⟩ := ht
          have := hj.1
          dsimp [identityEnd] at he; omega
        · have := ht.1
          dsimp [identityEnd] at this; omega
    ext k
    simp only [mem_Icc]
    constructor
    · intro hk
      have hb := mem_Icc.mp (hw hk)
      have hne : k ≠ c := by rintro rfl; exact hz hk
      omega
    · rintro ⟨hk, hkc⟩
      by_contra hn
      exact hp k (by omega) (Or.inl ⟨hk, by omega, hn⟩)
  · rintro rfl
    refine ⟨Or.inl ⟨hc, hcB, by simp; omega⟩, ?_⟩
    intro d hd ht
    rcases ht with ht | ht | ht | ht
    · exact ht.2.2 (mem_Icc.mpr ⟨ht.1, by omega⟩)
    · dsimp [identityEnd] at ht; omega
    · obtain ⟨t, u, v, _, _, _, _, he⟩ := ht
      dsimp [identityEnd] at he; omega
    · obtain ⟨i, hi, _, _, ht | ht⟩ := ht
      · obtain ⟨j, hj, _, he, _⟩ := ht
        have := hj.1
        dsimp [identityEnd] at he; omega
      · have := ht.1
        dsimp [identityEnd] at this; omega

private theorem singleton_fiber_of_support {r c : ℕ} (G : SimpleGraph (Fin r))
    (rho : Bool) (w : Finset ℕ) (hw : IsPrefix c w)
    (hs : FirstSelected r G c w)
    (hu : ∀ v, IsPrefix c v → FirstSelected r G c v → v.card = w.card → v = w) :
    selectedFiber r G rho (bareAddress r rho c w) = {w} := by
  ext v
  change (v ∈ ((Icc 1 c).powerset).filter (fun v =>
    FirstSelected r G c v ∧ v.card = w.card ∧ syndrome r rho v = syndrome r rho w)) ↔ v ∈ {w}
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
  constructor
  · rintro ⟨hv, hs, hc, _⟩
    exact hu v hv hs hc
  · rintro rfl
    exact ⟨hw, hs, rfl, rfl⟩

theorem run_at_first_selection {Z : Type} {r c : ℕ}
    (G : SimpleGraph (Fin r)) (P : BlindProgram Z) (rho : Bool) (w : Finset ℕ)
    (hs : FirstSelected r G (c + 1) w) :
    runBlind r G P rho w (c + 1) =
      ⟨P.update (markerInput r rho w c) true (runBlind r G P rho w c).value,
        some (bareAddress r rho (c + 1) (atCut w (c + 1)))⟩ := by
  have hn := run_snapshot_none G P rho w c (fun d hd => hs.2 d (by omega))
  have hf := (first_selected_at_cut G w).mpr hs
  simp [runBlind, writeThenLatch, hn, hf, markerInput]

/-- A first zero in the initial block has a singleton unpruned dictionary and
is latched as canonical zero by the same pre-decision color program. -/
theorem c7_initial_zero_latch {r c D : ℕ} (G : SimpleGraph (Fin r))
    (hr : 3 ≤ r) (hc : 1 ≤ c) (hcB : c ≤ initialLength r)
    (rho : Bool) (color : G.Coloring (Fin D)) (hD : 2 ≤ D) :
    let w := Icc 1 (c - 1)
    let b := bareAddress r rho c w
    let s := runBlind r G (asBlind (coloringPreProgram G color hD)) rho w c
    selectedFiber r G rho b = {w} ∧ s.snapshot = some b ∧
      (s.value : ℕ) = colexRank (selectedFiber r G rho b) w := by
  dsimp only
  let w := Icc 1 (c - 1)
  have hw : IsPrefix c w := Icc_subset_Icc_right (by omega)
  have hs := (initial_zero_support G hr hc hcB w hw).mpr rfl
  have hf := singleton_fiber_of_support G rho w hw hs (fun v hv hs _ =>
    (initial_zero_support G hr hc hcB v hv).mp hs)
  have hcut : atCut w c = w := filter_eq_self.mpr (fun a ha => (mem_Icc.mp (hw ha)).2)
  obtain ⟨k, hk⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
  have hrun := run_at_first_selection G (asBlind (coloringPreProgram G color hD))
    rho w (hk ▸ (show FirstSelected r G c w from hs))
  have hz : ∀ z : Fin D,
      ((coloringPreProgram G color hD).update (markerInput r rho w k) z : ℕ) = 0 := by
    intro z
    simp [coloringPreProgram, markerInput, bareAddress, show k + 1 ≤ initialLength r by omega]
  refine ⟨hf, ?_, ?_⟩
  · change (runBlind r G (asBlind (coloringPreProgram G color hD)) rho w c).snapshot = _
    rw [hk, hrun]
    simp only [← hk, hcut]
    rfl
  · change ((runBlind r G (asBlind (coloringPreProgram G color hD)) rho w c).value : ℕ) = _
    change ((runBlind r G (asBlind (coloringPreProgram G color hD)) rho w c).value : ℕ) =
      colexRank (selectedFiber r G rho (bareAddress r rho c w)) w
    rw [hf]
    simp only [colexRank, filter_singleton, lt_self_iff_false, ↓reduceIte, card_empty]
    rw [hk, hrun]
    exact hz
      (runBlind r G (asBlind (coloringPreProgram G color hD)) rho w k).value

private theorem onehot_identities {r i : ℕ} (hi : 1 ≤ i) (hir : i ≤ r) :
    identities r (insert (initialLength r + i) (Icc 1 (initialLength r))) = {i} := by
  ext k
  simp only [identities, mem_filter, mem_Icc, mem_insert, mem_singleton]
  omega

private theorem zero_deadline_support {r i : ℕ} (G : SimpleGraph (Fin r))
    (hr : 3 ≤ r) (hi : 1 ≤ i) (hir : i ≤ r) (w : Finset ℕ)
    (hw : IsPrefix (identityEnd r + pairCount r + i) w) :
    FirstSelected r G (identityEnd r + pairCount r + i) w ↔
      w = insert (initialLength r + i) (Icc 1 (initialLength r)) := by
  constructor
  · rintro ⟨ht, hp⟩
    have hb := initial_support (by dsimp [identityEnd]; omega) hp
    have hid : identities r w = {i} ∧
        ∀ k, 1 ≤ k → k ≤ pairCount r + i → identityEnd r + k ∉ w := by
      rcases ht with ht | ht | ht | ht
      · dsimp [identityEnd] at ht; omega
      · omega
      · obtain ⟨t, u, v, ht, _, _, _, he⟩ := ht; omega
      · obtain ⟨a, ha, har, hid, ht | ht⟩ := ht
        · obtain ⟨j, hf, hj, _, ht | ht⟩ := ht
          · have hjQ := ht.1.2.1; omega
          · have hd := delayed_target_bounds hr ha har hf.1 (by omega)
            omega
        · have hai : a = i := by omega
          simpa [hai] using And.intro hid ht.2
    ext k
    simp only [mem_insert]
    constructor
    · intro hk
      have hkb := mem_Icc.mp (hw hk)
      by_cases hB : k ≤ initialLength r
      · exact Or.inr (mem_Icc.mpr ⟨hkb.1, hB⟩)
      · by_cases hE : k ≤ identityEnd r
        · have hki : k - initialLength r ∈ identities r w := by
            simp only [identities, mem_filter, mem_Icc]
            refine ⟨?_, ?_⟩
            · dsimp [identityEnd] at hE; omega
            · convert hk using 1; omega
          rw [hid.1, mem_singleton] at hki
          exact Or.inl (by omega)
        · exfalso
          apply hid.2 (k - identityEnd r) (by omega) (by omega)
          convert hk using 1; omega
    · rintro (rfl | hk)
      · have hm : i ∈ identities r w := by simp [hid.1]
        exact (mem_filter.mp hm).2
      · exact hb hk
  · rintro rfl
    have hid := onehot_identities hi hir
    have hz : ∀ k, 1 ≤ k → identityEnd r + k ∉
        insert (initialLength r + i) (Icc 1 (initialLength r)) := by
      intro k hk
      simp only [mem_insert, mem_Icc]
      dsimp [identityEnd]; omega
    refine ⟨Or.inr (Or.inr (Or.inr ⟨i, hi, hir, hid,
      Or.inr ⟨rfl, fun k hk _ => hz k hk⟩⟩)), ?_⟩
    intro d hd ht
    rcases ht with ht | ht | ht | ht
    · exact ht.2.2 (mem_insert_of_mem (mem_Icc.mpr ⟨ht.1, ht.2.1⟩))
    · exact singleton_ne_empty i (hid.symm.trans ht.2)
    · obtain ⟨t, u, v, _, _, _, hs, _⟩ := ht
      have := congrArg List.length hs
      simp [hid] at this
    · obtain ⟨a, _, _, ha, ht | ht⟩ := ht
      · obtain ⟨j, hj, _⟩ := ht
        exact hz j hj.1 hj.2.1
      · have hai : a = i := by simpa [hid] using ha.symm
        omega

/-- A one-hot identity with no tail one before its deadline has a singleton
unpruned dictionary and the canonical zero output for both seeds. -/
theorem c7_zero_deadline_latch {r i D : ℕ} (G : SimpleGraph (Fin r))
    (hr : 3 ≤ r) (hi : 1 ≤ i) (hir : i ≤ r) (rho : Bool)
    (color : G.Coloring (Fin D)) (hD : 2 ≤ D) :
    let w := insert (initialLength r + i) (Icc 1 (initialLength r))
    let c := identityEnd r + pairCount r + i
    let b := bareAddress r rho c w
    let s := runBlind r G (asBlind (coloringPreProgram G color hD)) rho w c
    selectedFiber r G rho b = {w} ∧ s.snapshot = some b ∧
      (s.value : ℕ) = colexRank (selectedFiber r G rho b) w := by
  dsimp only
  let w := insert (initialLength r + i) (Icc 1 (initialLength r))
  let c := identityEnd r + pairCount r + i
  have hw : IsPrefix c w := by
    intro a ha
    simp only [w, mem_insert, mem_Icc] at ha ⊢
    dsimp [c, identityEnd]; omega
  have hs := (zero_deadline_support G hr hi hir w hw).mpr rfl
  have hf := singleton_fiber_of_support G rho w hw hs (fun v hv hs _ =>
    (zero_deadline_support G hr hi hir v hv).mp hs)
  have hcut : atCut w c = w := filter_eq_self.mpr (fun a ha => (mem_Icc.mp (hw ha)).2)
  obtain ⟨k, hk⟩ : ∃ k, c = k + 1 := ⟨c - 1, by dsimp [c]; omega⟩
  have hrun := run_at_first_selection G (asBlind (coloringPreProgram G color hD))
    rho w (hk ▸ (show FirstSelected r G c w from hs))
  have hz : ∀ z : Fin D,
      ((coloringPreProgram G color hD).update (markerInput r rho w k) z : ℕ) = 0 := by
    intro z
    have hB : ¬ k + 1 ≤ initialLength r := by dsimp [c, identityEnd] at hk; omega
    have hE : ¬ k + 1 ≤ identityEnd r := by dsimp [c] at hk; omega
    have hQ : pairCount r < k + 1 - identityEnd r := by dsimp [c] at hk; omega
    have hbit : k + 1 ∉ w := by
      simp only [w, mem_insert, mem_Icc]
      dsimp [c, identityEnd] at hk; omega
    simp [coloringPreProgram, markerInput, bareAddress, hB, hE, hQ, hbit]
  refine ⟨hf, ?_, ?_⟩
  · change (runBlind r G (asBlind (coloringPreProgram G color hD)) rho w c).snapshot = some _
    rw [hk, hrun]
    simp only [← hk, hcut]
    rfl
  · change ((runBlind r G (asBlind (coloringPreProgram G color hD)) rho w c).value : ℕ) =
      colexRank (selectedFiber r G rho (bareAddress r rho c w)) w
    rw [hf]
    simp only [colexRank, filter_singleton, lt_self_iff_false, ↓reduceIte, card_empty]
    rw [hk, hrun]
    exact hz (runBlind r G (asBlind (coloringPreProgram G color hD)) rho w k).value

private theorem empty_identity_support {r : ℕ} (G : SimpleGraph (Fin r))
    (hr : 3 ≤ r) (w : Finset ℕ) (hw : IsPrefix (identityEnd r) w) :
    FirstSelected r G (identityEnd r) w ↔ w = Icc 1 (initialLength r) := by
  constructor
  · rintro ⟨ht, hp⟩
    have hb := initial_support (by dsimp [identityEnd]; omega) hp
    have hid : identities r w = ∅ := by
      rcases ht with ht | ht | ht | ht
      · dsimp [identityEnd] at ht; omega
      · exact ht.2
      · obtain ⟨t, u, v, ht, _, _, _, he⟩ := ht; omega
      · obtain ⟨i, hi, _, _, ht | ht⟩ := ht
        · obtain ⟨j, hj, _, he, _⟩ := ht
          have := hj.1; omega
        · omega
    apply Subset.antisymm ?_ hb
    intro k hk
    have hkb := mem_Icc.mp (hw hk)
    by_contra hn
    have hki : k - initialLength r ∈ identities r w := by
      simp only [identities, mem_filter, mem_Icc]
      refine ⟨?_, ?_⟩
      · simp only [mem_Icc, not_and_or, not_le] at hn
        dsimp [identityEnd] at hkb; omega
      · simp only [mem_Icc, not_and_or, not_le] at hn
        convert hk using 1; omega
    simp [hid] at hki
  · rintro rfl
    have hid : identities r (Icc 1 (initialLength r)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro k hk hm
      have hb := mem_Icc.mp hk
      have hc := mem_Icc.mp hm
      omega
    refine ⟨Or.inr (Or.inl ⟨rfl, hid⟩), ?_⟩
    intro d hd ht
    rcases ht with ht | ht | ht | ht
    · exact ht.2.2 (mem_Icc.mpr ⟨ht.1, ht.2.1⟩)
    · omega
    · obtain ⟨t, u, v, ht, _, _, _, he⟩ := ht; omega
    · obtain ⟨i, _, _, hi, _⟩ := ht
      exact empty_ne_singleton i (hid.symm.trans hi)

/-- An empty identity block keeps zero throughout its acquisition and latches
that zero as the rank in the entire selected dictionary. -/
theorem c7_empty_identity_latch {r D : ℕ} (G : SimpleGraph (Fin r))
    (hr : 3 ≤ r) (rho : Bool) (color : G.Coloring (Fin D)) (hD : 2 ≤ D) :
    let w := Icc 1 (initialLength r)
    let c := identityEnd r
    let b := bareAddress r rho c w
    let s := runBlind r G (asBlind (coloringPreProgram G color hD)) rho w c
    selectedFiber r G rho b = {w} ∧ s.snapshot = some b ∧
      (s.value : ℕ) = colexRank (selectedFiber r G rho b) w := by
  dsimp only
  let w := Icc 1 (initialLength r)
  let c := identityEnd r
  have hw : IsPrefix c w := Icc_subset_Icc_right (by dsimp [c, identityEnd]; omega)
  have hs := (empty_identity_support G hr w hw).mpr rfl
  have hf := singleton_fiber_of_support G rho w hw hs (fun v hv hs _ =>
    (empty_identity_support G hr v hv).mp hs)
  have hcut : atCut w c = w := filter_eq_self.mpr (fun a ha => (mem_Icc.mp (hw ha)).2)
  obtain ⟨k, hk⟩ : ∃ k, c = k + 1 := ⟨c - 1, by dsimp [c, identityEnd]; omega⟩
  have hrun := run_at_first_selection G (asBlind (coloringPreProgram G color hD))
    rho w (hk ▸ (show FirstSelected r G c w from hs))
  have hz : ∀ d, d ≤ c →
      ((runBlind r G (asBlind (coloringPreProgram G color hD)) rho w d).value : ℕ) = 0 := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      have hz := ih (by omega)
      have hn := run_snapshot_none G (asBlind (coloringPreProgram G color hD)) rho w d
        (fun a ha => hs.2 a (by omega))
      have hup : ∀ z : Fin D, (z : ℕ) = 0 →
          ((coloringPreProgram G color hD).update (markerInput r rho w d) z : ℕ) = 0 := by
        intro z hz
        by_cases hB : d + 1 ≤ initialLength r
        · simp [coloringPreProgram, markerInput, bareAddress, hB]
        · have hbit : d + 1 ∉ w := by simp [w, hB]
          have hE : d + 1 ≤ identityEnd r := hd
          simp only [coloringPreProgram, markerInput, bareAddress, hB, hE, hbit,
            decide_false, Bool.false_eq_true, ↓reduceIte]
          split <;> simp_all
      rw [runBlind]
      simp only [writeThenLatch, hn, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      exact hup _ hz
  refine ⟨hf, ?_, ?_⟩
  · change (runBlind r G (asBlind (coloringPreProgram G color hD)) rho w c).snapshot = some _
    rw [hk, hrun]
    simp only [← hk, hcut]
    rfl
  · change ((runBlind r G (asBlind (coloringPreProgram G color hD)) rho w c).value : ℕ) =
      colexRank (selectedFiber r G rho (bareAddress r rho c w)) w
    rw [hf]
    simp only [colexRank, filter_singleton, lt_self_iff_false, ↓reduceIte, card_empty]
    exact hz c le_rfl

private theorem edge_at_injective {r j t : ℕ} (hj : 1 ≤ j) (ht : 1 ≤ t)
    (u v : Fin r) (he : edgeAt r j = some (u, v))
    (he' : edgeAt r t = some (u, v)) : j = t := by
  have hn : (pairList r).Nodup := by
    apply List.Nodup.map ofLex.injective
    exact Finset.sort_nodup _ _
  have hb := (List.getElem?_eq_some_iff.mp he).1
  have hh : j - 1 = t - 1 := (List.getElem?_inj hb hn).mp (he.trans he'.symm)
  omega

private theorem two_identity_card {r : ℕ} (u v : Fin r) (huv : u < v) :
    (insert (initialLength r + u.val + 1)
      (insert (initialLength r + v.val + 1) (Icc 1 (initialLength r)))).card =
      halfLength r := by
  have hu : initialLength r + u.val + 1 ∉
      insert (initialLength r + v.val + 1) (Icc 1 (initialLength r)) := by
    simp only [mem_insert, mem_Icc]
    have : u.val < v.val := huv
    omega
  have hv : initialLength r + v.val + 1 ∉ Icc 1 (initialLength r) := by simp
  simp [card_insert_of_notMem hu, card_insert_of_notMem hv, Nat.card_Icc, halfLength]

private theorem two_identity_support {r j : ℕ} (G : SimpleGraph (Fin r))
    (hr : 3 ≤ r) (hj : 1 ≤ j) (hjQ : j ≤ pairCount r)
    (u v : Fin r) (he : edgeAt r j = some (u, v))
    (w : Finset ℕ) (hw : w.card ≤ halfLength r) :
    FirstSelected r G (identityEnd r + pairCount r + r + j) w ↔
      w = insert (initialLength r + u.val + 1)
        (insert (initialLength r + v.val + 1) (Icc 1 (initialLength r))) := by
  have huv : u < v := (mem_pair_list u v).mp (List.mem_of_getElem? he)
  constructor
  · rintro ⟨ht, hp⟩
    have hb := initial_support (by dsimp [identityEnd]; omega) hp
    have hid : ((identities r w).sort (· ≤ ·)).take 2 = [u.val + 1, v.val + 1] := by
      rcases ht with ht | ht | ht | ht
      · dsimp [identityEnd] at ht; omega
      · omega
      · obtain ⟨t, a, b, _, _, hab, hs, hc⟩ := ht
        have htj : t = j := by omega
        subst t
        have hab' : (a, b) = (u, v) := Option.some.inj (hab.symm.trans he)
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab'
        exact hs
      · obtain ⟨a, ha, har, _, ht | ht⟩ := ht
        · obtain ⟨b, hf, hbQ, _, ht | ht⟩ := ht
          · have hb := ht.1.2.1; omega
          · have hd := delayed_target_bounds hr ha har hf.1 (by omega)
            omega
        · omega
    have hm (a : ℕ) (ha : a ∈ [u.val + 1, v.val + 1]) : initialLength r + a ∈ w := by
      have hh : a ∈ identities r w := by
        rw [← mem_sort (r := (· ≤ ·))]
        exact List.mem_of_mem_take (hid.symm ▸ ha)
      exact (mem_filter.mp hh).2
    apply (eq_of_subset_of_card_le (s := insert (initialLength r + u.val + 1)
      (insert (initialLength r + v.val + 1) (Icc 1 (initialLength r)))) ?_ ?_).symm
    · intro a ha
      simp only [mem_insert] at ha
      rcases ha with rfl | rfl | ha
      · simpa [Nat.add_assoc] using hm (u.val + 1) (by simp)
      · simpa [Nat.add_assoc] using hm (v.val + 1) (by simp)
      · exact hb ha
    · simpa [two_identity_card u v huv] using hw
  · rintro rfl
    have hid : identities r (insert (initialLength r + u.val + 1)
        (insert (initialLength r + v.val + 1) (Icc 1 (initialLength r)))) =
        {u.val + 1, v.val + 1} := by
      ext k
      simp only [identities, mem_filter, mem_Icc, mem_insert, mem_singleton]
      have := u.isLt
      have := v.isLt
      omega
    have hsort : ({u.val + 1, v.val + 1} : Finset ℕ).sort (· ≤ ·) =
        [u.val + 1, v.val + 1] := by
      have hn : [u.val + 1, v.val + 1].Nodup := by simp; exact ne_of_lt huv
      have hp : [u.val + 1, v.val + 1].Pairwise (· ≤ ·) := by simp; exact le_of_lt huv
      simpa using (List.toFinset_sort (r := (· ≤ ·)) hn).mpr hp
    have ht : ((identities r (insert (initialLength r + u.val + 1)
        (insert (initialLength r + v.val + 1) (Icc 1 (initialLength r))))).sort (· ≤ ·)).take 2 =
        [u.val + 1, v.val + 1] := by simp [hid, hsort]
    refine ⟨Or.inr (Or.inr (Or.inl ⟨j, u, v, hj, hjQ, he, ht, rfl⟩)), ?_⟩
    intro d hd htr
    rcases htr with htr | htr | htr | htr
    · exact htr.2.2 (mem_insert_of_mem (mem_insert_of_mem (mem_Icc.mpr ⟨htr.1, htr.2.1⟩)))
    · have hm : u.val + 1 ∈ identities r (insert (initialLength r + u.val + 1)
          (insert (initialLength r + v.val + 1) (Icc 1 (initialLength r)))) := by simp [hid]
      simp [htr.2] at hm
    · obtain ⟨t, a, b, ht1, _, hab, hs, hdc⟩ := htr
      rw [ht] at hs
      have hab' : u = a ∧ v = b := by
        simp only [List.cons.injEq] at hs
        exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
      obtain ⟨rfl, rfl⟩ := hab'
      have := edge_at_injective hj ht1 u v he hab
      omega
    · obtain ⟨a, _, _, ha, _⟩ := htr
      have hcard := congrArg Finset.card ha
      have hne : u.val + 1 ≠ v.val + 1 := by have : u.val < v.val := huv; omega
      rw [hid, Finset.card_pair hne, card_singleton] at hcard
      omega

/-- The two-identity schedule identifies both positions without a suffix or
acceptance filter, and its late latch clears the register to the unique rank. -/
theorem c7_two_identity_latch {r j D : ℕ} (G : SimpleGraph (Fin r))
    (hr : 3 ≤ r) (hj : 1 ≤ j) (hjQ : j ≤ pairCount r)
    (u v : Fin r) (he : edgeAt r j = some (u, v)) (rho : Bool)
    (color : G.Coloring (Fin D)) (hD : 2 ≤ D) :
    let w := insert (initialLength r + u.val + 1)
      (insert (initialLength r + v.val + 1) (Icc 1 (initialLength r)))
    let c := identityEnd r + pairCount r + r + j
    let b := bareAddress r rho c w
    let s := runBlind r G (asBlind (coloringPreProgram G color hD)) rho w c
    selectedFiber r G rho b = {w} ∧ s.snapshot = some b ∧
      (s.value : ℕ) = colexRank (selectedFiber r G rho b) w := by
  dsimp only
  let w := insert (initialLength r + u.val + 1)
    (insert (initialLength r + v.val + 1) (Icc 1 (initialLength r)))
  let c := identityEnd r + pairCount r + r + j
  have huv : u < v := (mem_pair_list u v).mp (List.mem_of_getElem? he)
  have hcard : w.card = halfLength r := two_identity_card u v huv
  have hw : IsPrefix c w := by
    intro a ha
    simp only [w, mem_insert, mem_Icc] at ha ⊢
    have := u.isLt
    have := v.isLt
    dsimp [c, identityEnd]; omega
  have hs := (two_identity_support G hr hj hjQ u v he w hcard.le).mpr rfl
  have hf := singleton_fiber_of_support G rho w hw hs (fun a _ hs ha =>
    (two_identity_support G hr hj hjQ u v he a (by omega)).mp hs)
  have hcut : ∀ d, identityEnd r ≤ d → atCut w d = w := by
    intro d hd
    apply filter_eq_self.mpr
    intro a ha
    simp only [w, mem_insert, mem_Icc] at ha
    have := u.isLt
    have := v.isLt
    dsimp [identityEnd] at hd; omega
  obtain ⟨k, hk⟩ : ∃ k, c = k + 1 := ⟨c - 1, by dsimp [c]; omega⟩
  have hrun := run_at_first_selection G (asBlind (coloringPreProgram G color hD))
    rho w (hk ▸ (show FirstSelected r G c w from hs))
  have hz : ∀ z : Fin D,
      ((coloringPreProgram G color hD).update (markerInput r rho w k) z : ℕ) = 0 := by
    intro z
    apply GraphScheduledSelection.coloring_update_full
    · change identityEnd r < k + 1
      dsimp [c] at hk; omega
    · change (atCut w k).card = halfLength r
      rw [hcut k (by dsimp [c] at hk; omega), hcard]
  refine ⟨hf, ?_, ?_⟩
  · change (runBlind r G (asBlind (coloringPreProgram G color hD)) rho w c).snapshot = some _
    rw [hk, hrun]
    simp only [← hk, hcut c (by dsimp [c]; omega)]
    rfl
  · change ((runBlind r G (asBlind (coloringPreProgram G color hD)) rho w c).value : ℕ) =
      colexRank (selectedFiber r G rho (bareAddress r rho c w)) w
    rw [hf]
    simp only [colexRank, filter_singleton, lt_self_iff_false, ↓reduceIte, card_empty]
    rw [hk, hrun]
    exact hz (runBlind r G (asBlind (coloringPreProgram G color hD)) rho w k).value

/-- Every non-early first selection of a prefix of completable weight has a
singleton dictionary, and the pre-decision program writes its canonical rank. -/
theorem c7_non_early_latch {r c D : ℕ} (G : SimpleGraph (Fin r))
    (hr : 3 ≤ r) (rho : Bool) (w : Finset ℕ) (hw : IsPrefix c w)
    (hcard : w.card ≤ halfLength r) (hs : FirstSelected r G c w)
    (hne : ¬ (identityEnd r < c ∧ c ≤ identityEnd r + pairCount r))
    (color : G.Coloring (Fin D)) (hD : 2 ≤ D) :
    let b := bareAddress r rho c w
    let s := runBlind r G (asBlind (coloringPreProgram G color hD)) rho w c
    selectedFiber r G rho b = {w} ∧ s.snapshot = some b ∧
      (s.value : ℕ) = colexRank (selectedFiber r G rho b) w := by
  dsimp only
  rcases hs.1 with ht | ht | ht | ht
  · have he := (initial_zero_support G hr ht.1 ht.2.1 w hw).mp hs
    subst w
    exact c7_initial_zero_latch G hr ht.1 ht.2.1 rho color hD
  · obtain ⟨rfl, _⟩ := ht
    have he := (empty_identity_support G hr w hw).mp hs
    subst w
    exact c7_empty_identity_latch G hr rho color hD
  · obtain ⟨j, u, v, hj, hjQ, he, _, rfl⟩ := ht
    have heq := (two_identity_support G hr hj hjQ u v he w hcard).mp hs
    subst w
    exact c7_two_identity_latch G hr hj hjQ u v he rho color hD
  · obtain ⟨i, hi, hir, hid, ht | ht⟩ := ht
    · obtain ⟨j, hf, hjQ, _, ht | ht⟩ := ht
      · exact False.elim (hne ⟨by have := hf.1; omega, by have := ht.1.2.1; omega⟩)
      · have hb := initial_support (by have := hf.1; dsimp [identityEnd] at *; omega) hs.2
        have him : i ∈ identities r w := by simp [hid]
        have heq := edge_prefix_eq_of_support hi hir hf.1 hb (mem_filter.mp him).2 hf.2.1 hcard
        subst w
        obtain ⟨hret, rfl⟩ := ht
        have hl := c7_delayed_latch G hr hi hir hf.1 hjQ hret rho color hD
        exact ⟨(delayed_selected_fiber_and_rank G hr hi hir hf.1 hjQ hret rho).1,
          hl.2.1, hl.2.2.1⟩
    · obtain ⟨rfl, _⟩ := ht
      have he := (zero_deadline_support G hr hi hir w hw).mp hs
      subst w
      exact c7_zero_deadline_latch G hr hi hir rho color hD

/-- Synchronous execution through a cut depends only on the occupied positions
at or before that cut, including the independently computed latch event. -/
theorem run_prefix_congr {Z : Type} {r c : ℕ} (G : SimpleGraph (Fin r))
    (P : BlindProgram Z) (rho : Bool) (w v : Finset ℕ)
    (h : ∀ k, k ≤ c → (k ∈ w ↔ k ∈ v)) :
    runBlind r G P rho w c = runBlind r G P rho v c := by
  induction c with
  | zero => rfl
  | succ c ih =>
    have he := ih (fun k hk => h k (by omega))
    have hc (d : ℕ) (hd : d ≤ c + 1) : atCut w d = atCut v d := by
      ext k
      simp only [atCut, mem_filter]
      by_cases hkd : k ≤ d
      · simp only [hkd, and_true, h k (by omega)]
      · simp only [hkd, and_false]
    have hi : markerInput r rho w c = markerInput r rho v c := by
      simp only [markerInput, hc c (by omega), hc (c + 1) le_rfl, h (c + 1) le_rfl]
    simp only [runBlind, he, hi, hc (c + 1) le_rfl]

end D5.S3.ObserverMemory.Trajectories.GraphScheduledSelectionCapacity
