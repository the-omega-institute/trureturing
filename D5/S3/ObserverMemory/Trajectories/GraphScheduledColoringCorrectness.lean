/- GID: D5/S3/ObserverMemory/Trajectories/GraphScheduledColoringCorrectness
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Trajectories/GraphScheduledColoringCorrectness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Acquiring graph colors and converting them to canonical selected ranks. -/

import D5.S3.ObserverMemory.Trajectories.GraphScheduledSelectionCapacity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.Trajectories.GraphScheduledColoringCorrectness

open Finset GraphScheduledSelection GraphScheduledSelectionCapacity
open scoped BigOperators Classical

private theorem at_cut_succ (w : Finset ℕ) (c : ℕ) :
    atCut w (c + 1) = if c + 1 ∈ w then insert (c + 1) (atCut w c) else atCut w c := by
  ext a
  by_cases hc : c + 1 ∈ w
  · simp only [atCut, mem_filter, hc, ↓reduceIte, mem_insert]
    constructor
    · rintro ⟨ha, hac⟩
      by_cases he : a = c + 1
      · exact Or.inl he
      · exact Or.inr ⟨ha, by omega⟩
    · rintro (rfl | ⟨ha, hac⟩)
      · exact ⟨hc, le_rfl⟩
      · exact ⟨ha, by omega⟩
  · simp only [atCut, mem_filter, hc, ↓reduceIte]
    constructor
    · rintro ⟨ha, hac⟩
      refine ⟨ha, ?_⟩
      by_contra hn
      have he : a = c + 1 := by omega
      exact hc (he ▸ ha)
    · rintro ⟨ha, hac⟩
      exact ⟨ha, by omega⟩

private theorem marker_input_consistent (r : ℕ) (rho : Bool) (w : Finset ℕ) (c : ℕ) :
    (atCut w (c + 1)).card = (atCut w c).card + (if c + 1 ∈ w then 1 else 0) ∧
    syndrome r rho (atCut w (c + 1)) = syndrome r rho (atCut w c) +
      (if c + 1 ∈ w then coefficient r rho (c + 1) else 0) := by
  have hn : c + 1 ∉ atCut w c := by simp [atCut]
  rw [at_cut_succ]
  by_cases hc : c + 1 ∈ w
  · simp [hc, hn, syndrome, add_comm, add_left_comm, add_assoc]
  · simp [hc]

private theorem edge_cut_wait {r j d : ℕ} (i : Fin r) (hj : 1 ≤ j)
    (hd : initialLength r + i.val + 1 ≤ d) (hdj : d < identityEnd r + j) :
    atCut (edgePrefix r (i.val + 1) j) d =
      insert (initialLength r + i.val + 1) (Icc 1 (initialLength r)) := by
  ext a
  simp only [atCut, edgePrefix, mem_filter, mem_insert, mem_Icc]
  have := i.isLt
  dsimp [identityEnd] at hdj ⊢
  omega

private theorem early_color_wait {r j D : ℕ} (G : SimpleGraph (Fin r))
    (hr : 3 ≤ r) (hj : 1 ≤ j) (hjQ : j ≤ pairCount r) (i : Fin r)
    (hret : Retained r G j (i.val + 1)) (rho : Bool)
    (color : G.Coloring (Fin D)) (hD : 2 ≤ D) :
    ∀ d, initialLength r + i.val + 1 ≤ d → d < identityEnd r + j →
      (runBlind r G (asBlind (coloringPreProgram G color hD)) rho
        (edgePrefix r (i.val + 1) j) d).value = color i := by
  let w := edgePrefix r (i.val + 1) j
  have hi : i.val + 1 ≤ r := by have := i.isLt; omega
  have hw := edge_prefix_subset (r := r) (by omega : 1 ≤ i.val + 1) hi hj
  have hs := (early_first_selection_support G hr hj hjQ w hw).mpr ⟨i.val + 1, hret, rfl⟩
  have step (d : ℕ) (hd : d < identityEnd r + j) :
      (runBlind r G (asBlind (coloringPreProgram G color hD)) rho w (d + 1)).value =
        (coloringPreProgram G color hD).update (markerInput r rho w d)
          (runBlind r G (asBlind (coloringPreProgram G color hD)) rho w d).value := by
    have hn := run_snapshot_none G (asBlind (coloringPreProgram G color hD)) rho w d
      (fun a ha => hs.2 a (by omega))
    simp only [runBlind, writeThenLatch, hn, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hstart : (runBlind r G (asBlind (coloringPreProgram G color hD)) rho w
      (initialLength r + i.val + 1)).value = color i := by
    rw [step (initialLength r + i.val) (by dsimp [identityEnd]; omega)]
    have hc : atCut w (initialLength r + i.val) = Icc 1 (initialLength r) := by
      ext a
      simp only [w, atCut, edgePrefix, mem_filter, mem_insert, mem_Icc]
      dsimp [identityEnd]; omega
    have hb : initialLength r + i.val + 1 ∈ w := by simp [w, edgePrefix, Nat.add_assoc]
    have hv := marker_input_consistent r rho w (initialLength r + i.val)
    have hn : initialLength r + i.val + 1 - initialLength r - 1 = i.val := by omega
    simp [coloringPreProgram, markerInput, bareAddress, hv.1, hv.2, hb, hc,
      show ¬ initialLength r + i.val + 1 ≤ initialLength r by omega,
      show initialLength r + i.val + 1 ≤ identityEnd r by dsimp [identityEnd]; omega,
      hn, i.isLt]
  intro d hd
  induction d, hd using Nat.le_induction with
  | base => intro _; exact hstart
  | succ d hdi ih =>
    intro hdj
    rw [step d (by omega), ih (by omega)]
    have hb : d + 1 ∉ w := by
      simp only [w, edgePrefix, mem_insert, mem_Icc]
      omega
    have hv := marker_input_consistent r rho w d
    have hc := edge_cut_wait i hj hdi (by omega : d < identityEnd r + j)
    have hcard : (atCut w d).card = halfLength r - 1 := by
      rw [hc, card_insert_of_notMem (by simp : initialLength r + i.val + 1 ∉ Icc 1 (initialLength r))]
      simp [Nat.card_Icc, halfLength]
    have hB : ¬ d + 1 ≤ initialLength r := by omega
    have hQ : ¬ pairCount r < d + 1 - identityEnd r := by omega
    simp [coloringPreProgram, markerInput, bareAddress, hv.1, hv.2, hb, hB, hcard, hQ]

private theorem early_rank_at_endpoint {r j : ℕ} (G : SimpleGraph (Fin r))
    (hr : 3 ≤ r) (hj : 1 ≤ j) (hjQ : j ≤ pairCount r)
    (u v : Fin r) (he : edgeAt r j = some (u, v)) (hG : G.Adj u v)
    (rho : Bool) (i : Fin r) (hi : i = u ∨ i = v) (ha : rho = true ∨ i.val + 1 ≠ 3) :
    colexRank (selectedFiber r G rho (earlyAddress r j)) (edgePrefix r (i.val + 1) j) =
      if (rho = true ∨ (u.val + 1 ≠ 3 ∧ v.val + 1 ≠ 3)) ∧ i = v then 1 else 0 := by
  have huv : u < v := (mem_pair_list u v).mp (List.mem_of_getElem? he)
  have hids : i.val + 1 ∈ ({u.val + 1, v.val + 1} : Finset ℕ).filter
      (fun a => rho = true ∨ a ≠ 3) := by
    simp only [mem_filter, mem_insert, mem_singleton]
    exact ⟨hi.elim (fun h => Or.inl (congrArg (fun x : Fin r => x.val + 1) h))
      (fun h => Or.inr (congrArg (fun x : Fin r => x.val + 1) h)), ha⟩
  rw [(c4_edge_fiber_and_ranks G hr hj hjQ rho u v he hG).2 _ hids]
  have hlt : u.val + 1 < v.val + 1 := by exact Nat.add_lt_add_right huv 1
  rcases hi with hi | hi
  · subst i
    have hf : ((({u.val + 1, v.val + 1} : Finset ℕ).filter
        (fun a => rho = true ∨ a ≠ 3)).filter (· < u.val + 1)) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro a ha hlt'
      have hm := (mem_filter.mp ha).1
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with rfl | rfl <;> omega
    rw [hf]
    simp [ne_of_lt huv]
  · subst i
    by_cases hboth : rho = true ∨ (u.val + 1 ≠ 3 ∧ v.val + 1 ≠ 3)
    · have hu : rho = true ∨ u.val + 1 ≠ 3 := by tauto
      have hf : ((({u.val + 1, v.val + 1} : Finset ℕ).filter
          (fun a => rho = true ∨ a ≠ 3)).filter (· < v.val + 1)) = {u.val + 1} := by
        ext a
        simp only [mem_filter, mem_insert, mem_singleton]
        constructor
        · rintro ⟨⟨hm | hm, _⟩, hlt'⟩
          · exact hm
          · omega
        · rintro rfl
          exact ⟨⟨Or.inl rfl, hu⟩, hlt⟩
      rw [hf]
      simp only [hboth, and_self, and_true, true_and, false_and, ↓reduceIte,
        card_singleton, card_empty]
    · have hu : ¬ (rho = true ∨ u.val + 1 ≠ 3) := by tauto
      have hf : ((({u.val + 1, v.val + 1} : Finset ℕ).filter
          (fun a => rho = true ∨ a ≠ 3)).filter (· < v.val + 1)) = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro a ha hlt'
        obtain ⟨hm, ha⟩ := mem_filter.mp ha
        simp only [mem_insert, mem_singleton] at hm
        rcases hm with rfl | rfl
        · exact hu ha
        · omega
      rw [hf]
      simp only [hboth, and_self, and_true, true_and, false_and, ↓reduceIte,
        card_singleton, card_empty]

/-- A retained endpoint acquires its graph color before the tail and converts
it at the actual first latch to the colex rank after the seed-zero deletion. -/
theorem c7_early_latch {r j D : ℕ} (G : SimpleGraph (Fin r))
    (hr : 3 ≤ r) (hj : 1 ≤ j) (hjQ : j ≤ pairCount r)
    (u v : Fin r) (he : edgeAt r j = some (u, v)) (hG : G.Adj u v)
    (rho : Bool) (i : Fin r) (hi : i = u ∨ i = v) (ha : rho = true ∨ i.val + 1 ≠ 3)
    (color : G.Coloring (Fin D)) (hD : 2 ≤ D) :
    let w := edgePrefix r (i.val + 1) j
    let c := identityEnd r + j
    let s := runBlind r G (asBlind (coloringPreProgram G color hD)) rho w c
    s.snapshot = some (earlyAddress r j) ∧
      (s.value : ℕ) = colexRank (selectedFiber r G rho (earlyAddress r j)) w := by
  dsimp only
  let w := edgePrefix r (i.val + 1) j
  let c := identityEnd r + j
  have hir : i.val + 1 ≤ r := by have := i.isLt; omega
  have hret : Retained r G j (i.val + 1) :=
    ⟨hj, hjQ, u, v, he, hG, hi.elim (fun h => Or.inl (by rw [h]))
      (fun h => Or.inr (by rw [h]))⟩
  have hw := edge_prefix_subset (by omega : 1 ≤ i.val + 1) hir hj
  have hs := (early_first_selection_support G hr hj hjQ w hw).mpr ⟨i.val + 1, hret, rfl⟩
  have hcut : atCut w c = w := filter_eq_self.mpr (fun a ha => (mem_Icc.mp (hw ha)).2)
  have hb : bareAddress r rho c w = earlyAddress r j := by
    have hsy := edge_prefix_syndrome hr (by omega : 1 ≤ i.val + 1) hir hj hjQ rho
    have hbad : ¬ (rho = false ∧ i.val + 1 = 3) := by
      rcases ha with ha | ha <;> simp_all
    dsimp only [bareAddress, earlyAddress, w, c]
    rw [edge_prefix_card (by omega : 1 ≤ i.val + 1) hir hj, hsy, if_neg hbad]
  obtain ⟨k, hk⟩ : ∃ k, c = k + 1 := ⟨c - 1, by dsimp [c]; omega⟩
  have hrun := run_at_first_selection G (asBlind (coloringPreProgram G color hD))
    rho w (hk ▸ (show FirstSelected r G c w from hs))
  have hwait := early_color_wait G hr hj hjQ i hret rho color hD k
    (by dsimp [c, identityEnd] at hk; omega) (by dsimp [c] at hk; omega)
  have hv := marker_input_consistent r rho w k
  have hbit : k + 1 ∈ w := by rw [← hk]; simp [c, w, edgePrefix]
  have hB : ¬ k + 1 ≤ initialLength r := by dsimp [c, identityEnd] at hk; omega
  have hE : ¬ k + 1 ≤ identityEnd r := by dsimp [c] at hk; omega
  have hidx : k + 1 - identityEnd r = j := by dsimp [c] at hk; omega
  have hc := edge_cut_wait i hj
    (by dsimp [c, identityEnd] at hk; omega : initialLength r + i.val + 1 ≤ k)
    (by dsimp [c] at hk; omega : k < identityEnd r + j)
  have hcard : (atCut w k).card = halfLength r - 1 := by
    rw [hc, card_insert_of_notMem (by simp : initialLength r + i.val + 1 ∉ Icc 1 (initialLength r))]
    simp [Nat.card_Icc, halfLength]
  have hcolor : color i = color v ↔ i = v := by
    rcases hi with hi | hi
    · subst i
      simp [color.valid hG, ne_of_lt ((mem_pair_list u v).mp (List.mem_of_getElem? he))]
    · subst i
      simp
  refine ⟨?_, ?_⟩
  · change (runBlind r G (asBlind (coloringPreProgram G color hD)) rho w c).snapshot = _
    rw [hk, hrun]
    simp only [← hk, hcut, hb]
  · change ((runBlind r G (asBlind (coloringPreProgram G color hD)) rho w c).value : ℕ) = _
    rw [hk, hrun]
    change ((coloringPreProgram G color hD).update (markerInput r rho w k)
      (runBlind r G (asBlind (coloringPreProgram G color hD)) rho w k).value : ℕ) = _
    rw [hwait, early_rank_at_endpoint G hr hj hjQ u v he hG rho i hi ha]
    simp [coloringPreProgram, markerInput, bareAddress, hv.1, hv.2, hbit,
      hB, hE, hidx, he, hG, hcard, hcolor]
    split <;> rfl

private theorem selection_before_end {r c : ℕ} (G : SimpleGraph (Fin r))
    (hr : 3 ≤ r) (w : Finset ℕ) (hs : FirstSelected r G c w) : c < wordLength r := by
  obtain ⟨d, hd, _⟩ := schedule_first_freeze G hr w
  by_contra hn
  exact hs.2 d (by omega) ((first_selected_at_cut G w).mp hd.2).1

/-- The same pre-decision program is correct for both seeds and every accepted
word, with its integer output measured in the full unpruned selected dictionary. -/
theorem coloring_pre_program_correct {r D : ℕ} (G : SimpleGraph (Fin r))
    (hr : 3 ≤ r) (color : G.Coloring (Fin D)) (hD : 2 ≤ D) :
    CorrectBlind r G D (asBlind (coloringPreProgram G color hD)) := by
  intro rho w hw c _ hs
  have hsf := (first_selected_at_cut G w).mp hs
  have hcn := selection_before_end G hr w hsf
  let p := atCut w c
  have hp : IsPrefix c p := by
    intro a ha
    obtain ⟨haw, hac⟩ := mem_filter.mp ha
    exact mem_Icc.mpr ⟨(mem_Icc.mp (hw.1 haw)).1, hac⟩
  have hpc : p.card ≤ halfLength r := by
    exact (card_filter_le _ _).trans hw.2.1.le
  have hrun : runBlind r G (asBlind (coloringPreProgram G color hD)) rho w c =
      runBlind r G (asBlind (coloringPreProgram G color hD)) rho p c :=
    run_prefix_congr G _ rho w p (fun k hk => by simp [p, atCut, hk])
  dsimp only
  rw [if_pos hcn, hrun]
  change (runBlind r G (asBlind (coloringPreProgram G color hD)) rho p c).snapshot =
      some (bareAddress r rho c p) ∧
    ((runBlind r G (asBlind (coloringPreProgram G color hD)) rho p c).value : ℕ) =
      colexRank (selectedFiber r G rho (bareAddress r rho c p)) p
  by_cases hearly : identityEnd r < c ∧ c ≤ identityEnd r + pairCount r
  · let j := c - identityEnd r
    have hj : 1 ≤ j := by dsimp [j]; omega
    have hjQ : j ≤ pairCount r := by dsimp [j]; omega
    have hc : c = identityEnd r + j := by dsimp [j]; omega
    have hsp : FirstSelected r G (identityEnd r + j) p := hc ▸ hs
    have hpp : IsPrefix (identityEnd r + j) p := hc ▸ hp
    obtain ⟨i, hret, hpi⟩ := (early_first_selection_support G hr hj hjQ p hpp).mp hsp
    obtain ⟨_, _, u, v, he, hG, hei⟩ := hret
    have hir : 1 ≤ i ∧ i ≤ r := by
      have := u.isLt
      have := v.isLt
      omega
    have hew : w = p := by
      apply (eq_of_subset_of_card_le (filter_subset _ _) ?_).symm
      change w.card ≤ p.card
      rw [hw.2.1, hpi, edge_prefix_card hir.1 hir.2 hj]
    have hzero : syndrome r rho p = 0 := by rw [← hew]; exact hw.2.2
    have ha : rho = true ∨ i ≠ 3 := by
      have hsy := edge_prefix_syndrome hr hir.1 hir.2 hj hjQ rho
      rw [← hpi, hzero] at hsy
      cases rho
      · right
        intro hi3
        have hbad : (0 : ZMod 2) = 1 := by simpa [hi3] using hsy
        exact zero_ne_one hbad
      · exact Or.inl rfl
    have hb : bareAddress r rho c p = earlyAddress r j := by
      dsimp only [bareAddress, earlyAddress]
      rw [hc, hzero, hpi, edge_prefix_card hir.1 hir.2 hj]
    rw [hb, hc, hpi]
    rcases hei with hei | hei
    · rw [hei] at ha ⊢
      exact c7_early_latch G hr hj hjQ u v he hG rho u (Or.inl rfl) ha color hD
    · rw [hei] at ha ⊢
      exact c7_early_latch G hr hj hjQ u v he hG rho v (Or.inr rfl) ha color hD
  · exact (c7_non_early_latch G hr rho p hp hpc hs hearly color hD).2

/-- Every finite graph with an edge admits a correct pre-decision register
whose alphabet is no larger than its chromatic number. -/
theorem pre_capacity_le_chromatic {r : ℕ} (G : SimpleGraph (Fin r))
    (hr : 3 ≤ r) (hedge : ∃ u v, G.Adj u v) : preCapacity r G ≤ G.chromaticNumber := by
  obtain ⟨color⟩ := G.colorable_chromaticNumber_of_fintype
  have hD : 2 ≤ G.chromaticNumber.toNat := by
    obtain ⟨u, v, hadj⟩ := hedge
    by_contra hn
    apply color.valid hadj
    apply Fin.ext
    have := (color u).isLt
    have := (color v).isLt
    omega
  calc
    preCapacity r G ≤ (G.chromaticNumber.toNat : ℕ∞) :=
      iInf_le (fun D : {D : ℕ // ∃ P : PreProgram (Fin D), CorrectBlind r G D (asBlind P)} =>
        (D.val : ℕ∞)) ⟨G.chromaticNumber.toNat, coloringPreProgram G color hD,
          coloring_pre_program_correct G hr color hD⟩
    _ ≤ G.chromaticNumber := ENat.natCast_toNat_le_self _

private theorem edge_inputs_eq {r j d : ℕ} (i a : Fin r) (hj : 1 ≤ j)
    (hd : identityEnd r ≤ d) (hdj : d < identityEnd r + j) :
    markerInput r true (edgePrefix r (i.val + 1) j) d =
      markerInput r true (edgePrefix r (a.val + 1) j) d := by
  have hc (t : ℕ) (ht : identityEnd r ≤ t) (htj : t ≤ identityEnd r + j) :
      (atCut (edgePrefix r (i.val + 1) j) t).card =
        (atCut (edgePrefix r (a.val + 1) j) t).card := by
    by_cases hlt : t < identityEnd r + j
    · have hi := edge_cut_wait i hj (by have := i.isLt; dsimp [identityEnd] at ht; omega) hlt
      have ha := edge_cut_wait a hj (by have := a.isLt; dsimp [identityEnd] at ht; omega) hlt
      rw [hi, ha]
      simp [card_insert_of_notMem, Nat.card_Icc]
    · have he : t = identityEnd r + j := by omega
      subst t
      have cut (b : Fin r) : atCut (edgePrefix r (b.val + 1) j) (identityEnd r + j) =
          edgePrefix r (b.val + 1) j := by
        apply filter_eq_self.mpr
        intro k hk
        exact (mem_Icc.mp (edge_prefix_subset (by omega : 1 ≤ b.val + 1)
          (by have := b.isLt; omega) hj hk)).2
      rw [cut i, cut a, edge_prefix_card (by omega : 1 ≤ i.val + 1)
        (by have := i.isLt; omega) hj, edge_prefix_card (by omega : 1 ≤ a.val + 1)
        (by have := a.isLt; omega) hj]
  have haddr (t : ℕ) (ht : identityEnd r ≤ t) (htj : t ≤ identityEnd r + j) :
      bareAddress r true t (atCut (edgePrefix r (i.val + 1) j) t) =
        bareAddress r true t (atCut (edgePrefix r (a.val + 1) j) t) := by
    simp [bareAddress, syndrome, coefficient, hc t ht htj]
  have hbit : decide (d + 1 ∈ edgePrefix r (i.val + 1) j) =
      decide (d + 1 ∈ edgePrefix r (a.val + 1) j) := by
    congr 1
    apply propext
    simp only [edgePrefix, mem_insert, mem_Icc]
    have := i.isLt
    have := a.isLt
    dsimp [identityEnd] at hd
    omega
  simp only [markerInput, haddr d hd (by omega), haddr (d + 1) (by omega) (by omega), hbit]

private theorem selected_event_at {r c d : ℕ} (G : SimpleGraph (Fin r))
    (w : Finset ℕ) (hs : FirstSelected r G c w) (hd : d ≤ c) :
    decide (FirstSelected r G d (atCut w d)) = decide (d = c) := by
  by_cases he : d = c
  · subst d
    simp [(first_selected_at_cut G w).mpr hs]
  · have hn : ¬ FirstSelected r G d (atCut w d) := by
      intro ht
      exact hs.2 d (by omega) ((first_selected_at_cut G w).mp ht).1
    simp [hn, he]

private theorem blind_endpoint_separation {r j D : ℕ} (G : SimpleGraph (Fin r))
    (hr : 3 ≤ r) (hj : 1 ≤ j) (hjQ : j ≤ pairCount r)
    (u v : Fin r) (he : edgeAt r j = some (u, v)) (hG : G.Adj u v)
    (P : BlindProgram (Fin D)) (hP : CorrectBlind r G D P) :
    (runBlind r G P true (insert (initialLength r + (u.val + 1))
      (Icc 1 (initialLength r))) (identityEnd r)).value ≠
    (runBlind r G P true (insert (initialLength r + (v.val + 1))
      (Icc 1 (initialLength r))) (identityEnd r)).value := by
  let c := identityEnd r + j
  let w (i : Fin r) := edgePrefix r (i.val + 1) j
  have hs (i : Fin r) (hi : i = u ∨ i = v) : FirstSelected r G c (w i) := by
    have hir : i.val + 1 ≤ r := by have := i.isLt; omega
    apply (early_first_selection_support G hr hj hjQ (w i)
      (edge_prefix_subset (by omega : 1 ≤ i.val + 1) hir hj)).mpr
    refine ⟨i.val + 1, ⟨hj, hjQ, u, v, he, hG, ?_⟩, rfl⟩
    rcases hi with hi | hi
    · exact Or.inl (by rw [hi])
    · exact Or.inr (by rw [hi])
  have hsu := hs u (Or.inl rfl)
  have hsv := hs v (Or.inr rfl)
  have hcn := selection_before_end G hr (w u) hsu
  have hcut (i : Fin r) : atCut (w i) c = w i := by
    apply filter_eq_self.mpr
    intro k hk
    exact (mem_Icc.mp (edge_prefix_subset (by omega : 1 ≤ i.val + 1)
      (by have := i.isLt; omega) hj hk)).2
  have haccept (i : Fin r) : Accepted r true (w i) := by
    have hir : i.val + 1 ≤ r := by have := i.isLt; omega
    refine ⟨(edge_prefix_subset (by omega : 1 ≤ i.val + 1) hir hj).trans
      (Icc_subset_Icc_right hcn.le), edge_prefix_card (by omega : 1 ≤ i.val + 1) hir hj, ?_⟩
    simpa using edge_prefix_syndrome hr (by omega : 1 ≤ i.val + 1) hir hj hjQ true
  have haddr (i : Fin r) : bareAddress r true c (w i) = earlyAddress r j := by
    dsimp only [bareAddress, earlyAddress]
    rw [(haccept i).2.1, (haccept i).2.2]
  have houtput (i : Fin r) (hi : i = u ∨ i = v) :
      ((runBlind r G P true (w i) c).value : ℕ) = if i = v then 1 else 0 := by
    have hout := (hP true (w i) (haccept i) c hcn.le ((first_selected_at_cut G (w i)).mpr (hs i hi))).2
    rw [if_pos hcn, hcut, haddr] at hout
    rw [early_rank_at_endpoint G hr hj hjQ u v he hG true i hi (Or.inl rfl)] at hout
    simpa using hout
  have hprefix (i : Fin r) : runBlind r G P true (w i) (identityEnd r) =
      runBlind r G P true (insert (initialLength r + (i.val + 1))
        (Icc 1 (initialLength r))) (identityEnd r) := by
    apply run_prefix_congr
    intro k hk
    have hn : k ≠ identityEnd r + j := by omega
    simp [w, edgePrefix, hn]
  intro heq
  have hstart : runBlind r G P true (w u) (identityEnd r) =
      runBlind r G P true (w v) (identityEnd r) := by
    have hval : (runBlind r G P true (w u) (identityEnd r)).value =
        (runBlind r G P true (w v) (identityEnd r)).value := by
      rw [hprefix u, hprefix v]
      exact heq
    have hnu := run_snapshot_none G P true (w u) (identityEnd r)
      (fun d hd => hsu.2 d (by dsimp [c]; omega))
    have hnv := run_snapshot_none G P true (w v) (identityEnd r)
      (fun d hd => hsv.2 d (by dsimp [c]; omega))
    cases hu : runBlind r G P true (w u) (identityEnd r)
    cases hv : runBlind r G P true (w v) (identityEnd r)
    simp_all
  have hequal : ∀ d, identityEnd r ≤ d → d ≤ c →
      runBlind r G P true (w u) d = runBlind r G P true (w v) d := by
    intro d hd
    induction d, hd using Nat.le_induction with
    | base => intro _; exact hstart
    | succ d hEd ih =>
      intro hdc
      have hinput := edge_inputs_eq u v hj hEd (by dsimp [c] at hdc; omega)
      change markerInput r true (w u) d = markerInput r true (w v) d at hinput
      have hevent := (selected_event_at G (w u) hsu hdc).trans
        (selected_event_at G (w v) hsv hdc).symm
      simp only [runBlind, ih (by omega), hinput, hevent]
  have hv := congrArg (fun s : LatchedRegister (Fin D) => (s.value : ℕ))
    (hequal c (by dsimp [c]; omega) le_rfl)
  rw [houtput u (Or.inl rfl), houtput v (Or.inr rfl)] at hv
  have huv : u ≠ v := ne_of_lt ((mem_pair_list u v).mp (List.mem_of_getElem? he))
  simp [huv] at hv

/-- The states actually acquired before the common tail form a proper coloring
for every correct blind program; hence its alphabet has at least χ(G) symbols. -/
theorem chromatic_le_blind_capacity {r : ℕ} (G : SimpleGraph (Fin r))
    (hr : 3 ≤ r) : G.chromaticNumber ≤ blindCapacity r G := by
  apply le_iInf
  intro D
  obtain ⟨P, hP⟩ := D.property
  apply SimpleGraph.Colorable.chromaticNumber_le
  refine ⟨SimpleGraph.Coloring.mk
    (fun i => (runBlind r G P true (insert (initialLength r + (i.val + 1))
      (Icc 1 (initialLength r))) (identityEnd r)).value) ?_⟩
  intro u v hG
  by_cases huv : u < v
  · obtain ⟨j, hj, hjQ, he⟩ := edge_at_complete u v huv
    exact blind_endpoint_separation G hr hj hjQ u v he hG P hP
  · have hvu : v < u := lt_of_le_of_ne (le_of_not_gt huv) (Ne.symm (G.ne_of_adj hG))
    obtain ⟨j, hj, hjQ, he⟩ := edge_at_complete v u hvu
    exact Ne.symm (blind_endpoint_separation G hr hj hjQ v u he (G.adj_symm hG) P hP)

/-- Blind and pre-decision alphabets both attain the graph chromatic number. -/
theorem blind_pre_capacity_eq_chromatic {r : ℕ} (G : SimpleGraph (Fin r))
    (hr : 3 ≤ r) (hedge : ∃ u v, G.Adj u v) :
    blindCapacity r G = G.chromaticNumber ∧ preCapacity r G = G.chromaticNumber := by
  have hclass : blindCapacity r G ≤ preCapacity r G := by
    apply le_iInf
    intro D
    obtain ⟨P, hP⟩ := D.property
    exact iInf_le (fun E : {E : ℕ // ∃ P : BlindProgram (Fin E), CorrectBlind r G E P} =>
      (E.val : ℕ∞)) ⟨D.val, asBlind P, hP⟩
  have hlo := chromatic_le_blind_capacity G hr
  have hhi := pre_capacity_le_chromatic G hr hedge
  exact ⟨le_antisymm (hclass.trans hhi) hlo, le_antisymm hhi (hlo.trans hclass)⟩

end D5.S3.ObserverMemory.Trajectories.GraphScheduledColoringCorrectness
