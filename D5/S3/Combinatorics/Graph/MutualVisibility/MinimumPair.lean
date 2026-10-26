/- GID: D5/S3/Combinatorics/Graph/MutualVisibility/MinimumPair
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MutualVisibility/MinimumPair
   mirror-E: none(waiver:no-computational-evidence)
   anchors: []
   utility: none
   digest: A minimum rooted pair pays every actual mixed neighbor from one configuration cut. -/

import D5.S3.Combinatorics.Graph.MutualVisibility.RootComparability

/-! One common cut pays local neighbors and simultaneous inward replacements. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.MutualVisibility

open SimpleGraph
open scoped symmDiff

variable {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}

omit [Fintype V] in
private theorem pair_erase_right {u v : V} (huv : u ≠ v) :
    ({u, v} : Finset V).erase v = {u} := by
  ext z
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  aesop

omit [Fintype V] in
private theorem pair_singleton_adj (hH : H.Connected) {u v : V} (huv : u ≠ v) :
    (reconfiguration H).Adj ⟨{u, v}, visible_pair hH u v⟩
      ⟨{u}, visible_singleton H u⟩ := by
  have h := mixedMove_erase H ({u, v} : Finset V) (x := v) (by simp)
  rw [pair_erase_right huv] at h
  exact h

omit [Fintype V] in
private theorem pair_slide (hH : H.Connected) {u v y : V}
    (huv : u ≠ v) (hyu : y ≠ u) (hyv : y ≠ v) (hvy : H.Adj v y) :
    (reconfiguration H).Adj ⟨{u, v}, visible_pair hH u v⟩
      ⟨{u, y}, visible_pair hH u y⟩ := by
  refine ⟨?_, Or.inr ⟨v, y, ?_, ?_, hvy⟩⟩
  · intro he
    change ({u, v} : Finset V) = {u, y} at he
    have hm : v ∈ ({u, y} : Finset V) := by rw [← he]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    exact hm.elim huv.symm hyv.symm
  · ext z
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    aesop
  · ext z
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    aesop

omit [Fintype V] in
private theorem triple_pair_adj (hH : H.Connected) {u v y : V}
    (hyu : y ≠ u) (hyv : y ≠ v) (ht : Visible H {u, v, y}) :
    (reconfiguration H).Adj ⟨{u, v, y}, ht⟩ ⟨{u, v}, visible_pair hH u v⟩ := by
  have he : ({u, v, y} : Finset V).erase y = {u, v} := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have h := mixedMove_erase H ({u, v, y} : Finset V) (x := y) (by simp)
  rw [he] at h
  exact h

omit [Fintype V] in
private theorem triple_cross_adj (hH : H.Connected) {u v y : V}
    (huv : u ≠ v) (hyu : y ≠ u) (hyv : y ≠ v) (ht : Visible H {u, v, y}) :
    (reconfiguration H).Adj ⟨{u, v, y}, ht⟩ ⟨{u, y}, visible_pair hH u y⟩ ∧
    (reconfiguration H).Adj ⟨{u, v, y}, ht⟩ ⟨{v, y}, visible_pair hH v y⟩ := by
  have heP : ({u, v, y} : Finset V).erase v = {u, y} := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have heQ : ({u, v, y} : Finset V).erase u = {v, y} := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  constructor
  · have h := mixedMove_erase H ({u, v, y} : Finset V) (x := v) (by simp)
    rw [heP] at h
    exact h
  · have h := mixedMove_erase H ({u, v, y} : Finset V) (x := u) (by simp)
    rw [heQ] at h
    exact h

omit [Fintype V] in
private theorem triangle_visible {u v y : V}
    (huv : H.Adj u v) (huy : H.Adj u y) (hvy : H.Adj v y) :
    Visible H {u, v, y} := by
  intro a ha b hb hab
  have hadj : H.Adj a b := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact (hab rfl).elim
    · exact huv
    · exact huy
    · exact huv.symm
    · exact (hab rfl).elim
    · exact hvy
    · exact huy.symm
    · exact hvy.symm
    · exact (hab rfl).elim
  exact ⟨hadj.toWalk, by simpa using (dist_eq_one_iff_adj.mpr hadj).symm,
    fun z hz _ => by simpa using hz⟩

open Classical in
private theorem pair_neighbor_bound (hH : H.Connected) {u v y : V}
    (huv : u ≠ v) (hyu : y ≠ u) (hyv : y ≠ v) :
    (localCutClass ((reconfiguration H).neighborFinset
      ⟨{u, v}, visible_pair hH u v⟩) {u, v} y).card ≤
      (if H.Adj u y then 1 else 0) + (if H.Adj v y then 1 else 0) +
      (if Visible H {u, v, y} then 1 else 0) := by
  classical
  let L := localCutClass ((reconfiguration H).neighborFinset
    ⟨{u, v}, visible_pair hH u v⟩) {u, v} y
  let A : Finset (Finset V) := if H.Adj u y then {{v, y}} else ∅
  let B : Finset (Finset V) := if H.Adj v y then {{u, y}} else ∅
  let T : Finset (Finset V) := if Visible H {u, v, y} then {{u, v, y}} else ∅
  have hsub : L.image Subtype.val ⊆ A ∪ B ∪ T := by
    intro Q hQ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨hN, hyP, hPS⟩ := Finset.mem_filter.mp hP
    have hm := (SimpleGraph.mem_neighborFinset _ _ _).mp hN
    rcases outside_move_shape (by simp [hyu, hyv]) hyP hPS hm with he | ⟨x, hx, hxy, he⟩
    · have he' : P.val = {u, v, y} := he.trans (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; aesop)
      have ht : Visible H {u, v, y} := he' ▸ P.property
      simp [A, B, T, ht, he']
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx
      · subst x
        have he' : P.val = {v, y} := he.trans (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]; aesop)
        simp [A, B, T, hxy, he']
      · subst x
        have he' : P.val = {u, y} := he.trans (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]; aesop)
        simp [A, B, T, hxy, he']
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hc
  have h1 := Finset.card_union_le (A ∪ B) T
  have h2 := Finset.card_union_le A B
  have hA : A.card = if H.Adj u y then 1 else 0 := by by_cases h : H.Adj u y <;> simp [A, h]
  have hB : B.card = if H.Adj v y then 1 else 0 := by by_cases h : H.Adj v y <;> simp [B, h]
  have hT : T.card = if Visible H {u, v, y} then 1 else 0 := by
    by_cases h : Visible H {u, v, y} <;> simp [T, h]
  change L.card ≤ _
  omega

private theorem visible_pairs_impossible (hH : H.Connected)
    (C : Finset (Configuration H)) (s : Configuration H) {w u v y : V}
    (hc : C.card < (reconfiguration H).minDegree) (hw : CleanRoot C w)
    (huv : u ≠ v) (hyu : y ≠ u) (hyv : y ≠ v)
    (ht : Visible H {u, v, y})
    (hB : CutReach (reconfiguration H) C s ⟨{u, v}, visible_pair hH u v⟩)
    (hU : CutReach (reconfiguration H) C s ⟨{u, y}, visible_pair hH u y⟩)
    (hQ : CutReach (reconfiguration H) C s ⟨{v, y}, visible_pair hH v y⟩)
    (hwout : ¬ CutReach (reconfiguration H) C s ⟨{w}, visible_singleton H w⟩) : False := by
  exact visible_comparability_triangle hH ht (by simp) (by simp) (by simp)
    (stranded_pair_comparable hH C s hc hw huv hB hwout)
    (stranded_pair_comparable hH C s hc hw hyu.symm hU hwout)
    (stranded_pair_comparable hH C s hc hw hyv.symm hQ hwout)

omit [Fintype V] in
private theorem nonvisible_common_pair_cut (hH : H.Connected)
    (C : Finset (Configuration H)) (s : Configuration H) {w u v y : V}
    (hdom : Dominates H w u v) (hyu : y ≠ u) (hyv : y ≠ v)
    (huy : H.Adj u y) (hvy : H.Adj v y) (hn : ¬ Visible H {u, v, y})
    (hB : CutReach (reconfiguration H) C s ⟨{u, v}, visible_pair hH u v⟩)
    (hmin : ∀ a b, a ≠ b →
      CutReach (reconfiguration H) C s ⟨{a, b}, visible_pair hH a b⟩ →
      H.dist u w + H.dist v w ≤ H.dist a w + H.dist b w) :
    (⟨{u, y}, visible_pair hH u y⟩ : Configuration H) ∈ C := by
  have hnadj : ¬ H.Adj u v := fun h => hn (triangle_visible h huy hvy)
  have hdist := hH.one_lt_dist_of_ne_of_not_adj hdom.2.1 hnadj
  have hy := common_neighbor_height hH hdom huy hvy
  have hd := mandatory_dist hH hdom.2.2
  rw [H.dist_comm (u := v) (v := u)] at hd
  by_contra hnC
  have hr := cutReach_step hB (pair_slide hH hdom.2.1 hyu hyv hvy) hnC
  have hm := hmin u y hyu.symm hr
  omega

omit [Fintype V] [DecidableEq V] in
private theorem two_cuts {L : Finset (Configuration H)} {A B : Configuration H}
    (hA : A ∈ L) (hB : B ∈ L) (hne : A ≠ B) : 2 ≤ L.card := by
  have h := Finset.card_le_card (show ({A, B} : Finset (Configuration H)) ⊆ L by
    simp [Finset.insert_subset_iff, hA, hB])
  simpa [hne] using h

omit [Fintype V] [DecidableEq V] in
private theorem three_cuts {L : Finset (Configuration H)} {A B T : Configuration H}
    (hA : A ∈ L) (hB : B ∈ L) (hT : T ∈ L)
    (hAB : A ≠ B) (hAT : A ≠ T) (hBT : B ≠ T) : 3 ≤ L.card := by
  have h := Finset.card_le_card (show ({A, B, T} : Finset (Configuration H)) ⊆ L by
    simp [Finset.insert_subset_iff, hA, hB, hT])
  simpa [hAB, hAT, hBT] using h

private def Exceptional (C : Finset (Configuration H))
    (s : Configuration H) (u v y : V) : Prop :=
  H.Adj u y ∧ H.Adj v y ∧ ∃ ht : Visible H {u, v, y},
    CutReach (reconfiguration H) C s ⟨{u, v, y}, ht⟩

open Classical in
private theorem minimum_pair_local_bound (hH : H.Connected)
    (C : Finset (Configuration H)) (s : Configuration H) {w u v y : V}
    (hc : C.card < (reconfiguration H).minDegree) (hw : CleanRoot C w)
    (huv : u ≠ v) (hyu : y ≠ u) (hyv : y ≠ v)
    (hB : CutReach (reconfiguration H) C s ⟨{u, v}, visible_pair hH u v⟩)
    (hwout : ¬ CutReach (reconfiguration H) C s ⟨{w}, visible_singleton H w⟩)
    (hdom : Dominates H w u v)
    (hmin : ∀ a b, a ≠ b →
      CutReach (reconfiguration H) C s ⟨{a, b}, visible_pair hH a b⟩ →
      H.dist u w + H.dist v w ≤ H.dist a w + H.dist b w) :
    (localCutClass ((reconfiguration H).neighborFinset
      ⟨{u, v}, visible_pair hH u v⟩) {u, v} y).card ≤
      (localCutClass C {u, v} y).card +
      if Exceptional C s u v y then 1 else 0 := by
  classical
  let L := localCutClass C {u, v} y
  let P : Configuration H := ⟨{u, y}, visible_pair hH u y⟩
  let Q : Configuration H := ⟨{v, y}, visible_pair hH v y⟩
  let A : Configuration H := ⟨{y}, visible_singleton H y⟩
  have hPQ : P ≠ Q := by
    intro he
    have hu : u ∈ Q.val := by rw [← he]; simp [P]
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hu
    exact hu.elim huv hyu.symm
  have hAP : A ≠ P := by
    intro he
    have hu : u ∈ A.val := by rw [he]; simp [P]
    exact hyu ((by simpa [A] using hu : u = y).symm)
  have hAQ : A ≠ Q := by
    intro he
    have hv : v ∈ A.val := by rw [he]; simp [Q]
    exact hyv ((by simpa [A] using hv : v = y).symm)
  have hLP (h : P ∈ C) : P ∈ L := by
    exact Finset.mem_filter.mpr ⟨h, by simp [P], by simp [P, Finset.insert_subset_iff]⟩
  have hLQ (h : Q ∈ C) : Q ∈ L := by
    exact Finset.mem_filter.mpr ⟨h, by simp [Q], by simp [Q, Finset.insert_subset_iff]⟩
  have hsingle := stranded_singletons hH C s (hc.trans_le minDegree_le_host_order) hw hwout
  have hbound := pair_neighbor_bound hH huv hyu hyv
  by_cases hyD : y ∈ deletedLabels C
  · have hAC : A ∈ C := by simpa [A, deletedLabels] using hyD
    have hAL : A ∈ L := Finset.mem_filter.mpr
      ⟨hAC, by simp [A], by simp [A, Finset.insert_subset_iff]⟩
    have hL1 : 1 ≤ L.card := Finset.card_pos.mpr ⟨A, hAL⟩
    by_cases ht : Visible H {u, v, y}
    · let T : Configuration H := ⟨{u, v, y}, ht⟩
      have hAT : A ≠ T := by
        intro he
        have hu : u ∈ A.val := by rw [he]; simp [T]
        exact hyu ((by simpa [A] using hu : u = y).symm)
      have hPT : P ≠ T := by
        intro he
        have hv : v ∈ P.val := by rw [he]; simp [T]
        simp only [P, Finset.mem_insert, Finset.mem_singleton] at hv
        exact hv.elim huv.symm hyv.symm
      have hQT : Q ≠ T := by
        intro he
        have hu : u ∈ Q.val := by rw [he]; simp [T]
        simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hu
        exact hu.elim huv hyu.symm
      have hfaces (hr : CutReach (reconfiguration H) C s T) : P ∈ C ∨ Q ∈ C := by
        by_contra hn
        have hnP : P ∉ C := fun h => hn (Or.inl h)
        have hnQ : Q ∉ C := fun h => hn (Or.inr h)
        have hUP : CutReach (reconfiguration H) C s P := cutReach_step hr
          (triple_cross_adj hH huv hyu hyv ht).1 hnP
        have hVQ : CutReach (reconfiguration H) C s Q := cutReach_step hr
          (triple_cross_adj hH huv hyu hyv ht).2 hnQ
        exact visible_pairs_impossible hH C s hc hw huv hyu hyv ht hB hUP hVQ hwout
      by_cases hTC : T ∈ C
      · have hTL : T ∈ L := Finset.mem_filter.mpr
          ⟨hTC, by simp [T], by simp [T, Finset.insert_subset_iff]⟩
        have hL2 := two_cuts hAL hTL hAT
        by_cases huy : H.Adj u y <;> by_cases hvy : H.Adj v y
        · have hcut : P ∈ C ∨ Q ∈ C := by
            by_contra hn
            have hUP := cutReach_step hB (pair_slide hH huv hyu hyv hvy)
              (fun h => hn (Or.inl h))
            have hVQ := cutReach_step hB
              (by simpa only [Finset.pair_comm, Q] using (pair_slide hH huv.symm hyv hyu huy))
              (fun h => hn (Or.inr h))
            exact visible_pairs_impossible hH C s hc hw huv hyu hyv ht hB hUP hVQ hwout
          have hL3 : 3 ≤ L.card := hcut.elim
            (fun h => three_cuts hAL (hLP h) hTL hAP hAT hPT)
            (fun h => three_cuts hAL (hLQ h) hTL hAQ hAT hQT)
          simp only [huy, hvy, ht, ite_true, ite_false, Nat.zero_add, Nat.add_zero] at hbound
          change _ ≤ L.card + _
          omega
        all_goals
          simp only [huy, hvy, ht, ite_true, ite_false, Nat.zero_add, Nat.add_zero] at hbound
          change _ ≤ L.card + _
          omega
      · have hr : CutReach (reconfiguration H) C s T := cutReach_step hB
          (triple_pair_adj hH hyu hyv ht).symm hTC
        have hL2 : 2 ≤ L.card := (hfaces hr).elim
          (fun h => two_cuts hAL (hLP h) hAP)
          (fun h => two_cuts hAL (hLQ h) hAQ)
        by_cases huy : H.Adj u y <;> by_cases hvy : H.Adj v y
        · have he : Exceptional C s u v y := ⟨huy, hvy, ht, hr⟩
          simp only [huy, hvy, ht, ite_true, ite_false, Nat.zero_add, Nat.add_zero] at hbound
          change _ ≤ L.card + _
          rw [ite_eq_left he]
          omega
        all_goals
          simp only [huy, hvy, ht, ite_true, ite_false, Nat.zero_add, Nat.add_zero] at hbound
          change _ ≤ L.card + _
          omega
    · by_cases huy : H.Adj u y <;> by_cases hvy : H.Adj v y
      · have hPC : P ∈ C := nonvisible_common_pair_cut hH C s hdom hyu hyv huy hvy ht hB hmin
        have hL2 := two_cuts hAL (hLP hPC) hAP
        simp only [huy, hvy, ht, ite_true, ite_false, Nat.zero_add, Nat.add_zero] at hbound
        change _ ≤ L.card + _
        omega
      all_goals
        simp only [huy, hvy, ht, ite_true, ite_false, Nat.zero_add, Nat.add_zero] at hbound
        change _ ≤ L.card + _
        omega
  · have hAC : A ∉ C := by simpa [A, deletedLabels] using hyD
    have hPoutside : ¬ CutReach (reconfiguration H) C s P := by
      intro hr
      exact hsingle y (cutReach_step hr (by simpa [P, A, Finset.pair_comm] using
        (pair_singleton_adj hH hyu)) hAC)
    have hQoutside : ¬ CutReach (reconfiguration H) C s Q := by
      intro hr
      exact hsingle y (cutReach_step hr (by simpa [Q, A, Finset.pair_comm] using
        (pair_singleton_adj hH hyv)) hAC)
    have hPC (hvy : H.Adj v y) : P ∈ C := by
      by_contra hn
      exact hPoutside (cutReach_step hB (pair_slide hH huv hyu hyv hvy) hn)
    have hQC (huy : H.Adj u y) : Q ∈ C := by
      by_contra hn
      exact hQoutside (cutReach_step hB
        (by simpa only [Finset.pair_comm, Q] using (pair_slide hH huv.symm hyv hyu huy)) hn)
    by_cases ht : Visible H {u, v, y}
    · let T : Configuration H := ⟨{u, v, y}, ht⟩
      have hPT : P ≠ T := by
        intro he
        have hv : v ∈ P.val := by rw [he]; simp [T]
        simp only [P, Finset.mem_insert, Finset.mem_singleton] at hv
        exact hv.elim huv.symm hyv.symm
      have hQT : Q ≠ T := by
        intro he
        have hu : u ∈ Q.val := by rw [he]; simp [T]
        simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hu
        exact hu.elim huv hyu.symm
      by_cases hTC : T ∈ C
      · have hTL : T ∈ L := Finset.mem_filter.mpr
          ⟨hTC, by simp [T], by simp [T, Finset.insert_subset_iff]⟩
        have hL1 : 1 ≤ L.card := Finset.card_pos.mpr ⟨T, hTL⟩
        by_cases huy : H.Adj u y <;> by_cases hvy : H.Adj v y
        · have hL3 := three_cuts (hLP (hPC hvy)) (hLQ (hQC huy)) hTL hPQ hPT hQT
          simp only [huy, hvy, ht, ite_true, ite_false, Nat.zero_add, Nat.add_zero] at hbound
          change _ ≤ L.card + _
          omega
        · have hL2 := two_cuts (hLQ (hQC huy)) hTL hQT
          simp only [huy, hvy, ht, ite_true, ite_false, Nat.zero_add, Nat.add_zero] at hbound
          change _ ≤ L.card + _
          omega
        · have hL2 := two_cuts (hLP (hPC hvy)) hTL hPT
          simp only [huy, hvy, ht, ite_true, ite_false, Nat.zero_add, Nat.add_zero] at hbound
          change _ ≤ L.card + _
          omega
        · simp only [huy, hvy, ht, ite_true, ite_false, Nat.zero_add, Nat.add_zero] at hbound
          change _ ≤ L.card + _
          omega
      · have hr : CutReach (reconfiguration H) C s T := cutReach_step hB
          (triple_pair_adj hH hyu hyv ht).symm hTC
        have hPC' : P ∈ C := by
          by_contra hn
          exact hPoutside (cutReach_step hr
            (triple_cross_adj hH huv hyu hyv ht).1 hn)
        have hQC' : Q ∈ C := by
          by_contra hn
          exact hQoutside (cutReach_step hr
            (triple_cross_adj hH huv hyu hyv ht).2 hn)
        have hL2 := two_cuts (hLP hPC') (hLQ hQC') hPQ
        by_cases huy : H.Adj u y <;> by_cases hvy : H.Adj v y
        · have he : Exceptional C s u v y := ⟨huy, hvy, ht, hr⟩
          simp only [huy, hvy, ht, ite_true, ite_false, Nat.zero_add, Nat.add_zero] at hbound
          change _ ≤ L.card + _
          rw [ite_eq_left he]
          omega
        all_goals
          simp only [huy, hvy, ht, ite_true, ite_false, Nat.zero_add, Nat.add_zero] at hbound
          change _ ≤ L.card + _
          omega
    · by_cases huy : H.Adj u y <;> by_cases hvy : H.Adj v y
      · have hL2 := two_cuts (hLP (hPC hvy)) (hLQ (hQC huy)) hPQ
        simp only [huy, hvy, ht, ite_true, ite_false, Nat.zero_add, Nat.add_zero] at hbound
        change _ ≤ L.card + _
        omega
      · have hL1 : 1 ≤ L.card := Finset.card_pos.mpr ⟨Q, hLQ (hQC huy)⟩
        simp only [huy, hvy, ht, ite_true, ite_false, Nat.zero_add, Nat.add_zero] at hbound
        change _ ≤ L.card + _
        omega
      · have hL1 : 1 ≤ L.card := Finset.card_pos.mpr ⟨P, hLP (hPC hvy)⟩
        simp only [huy, hvy, ht, ite_true, ite_false, Nat.zero_add, Nat.add_zero] at hbound
        change _ ≤ L.card + _
        omega
      · simp only [huy, hvy, ht, ite_true, ite_false, Nat.zero_add, Nat.add_zero] at hbound
        change _ ≤ L.card + _
        omega

omit [Fintype V] [DecidableEq V] in
private theorem inward_predecessor (hH : H.Connected) {u w : V} (huw : u ≠ w) :
    ∃ p, H.Adj p u ∧ H.dist p w + 1 = H.dist u w := by
  obtain ⟨q, hq⟩ := hH.exists_walk_length_eq_dist u w
  cases q with
  | nil => exact (huw rfl).elim
  | @cons a b c hab q =>
    refine ⟨b, hab.symm, ?_⟩
    have hl := H.dist_le q
    have ht := hH.dist_triangle (u := u) (v := b) (w := w)
    rw [dist_eq_one_iff_adj.mpr hab] at ht
    simp only [Walk.length_cons] at hq
    omega

private theorem minimum_pair_degree (hH : H.Connected)
    (C : Finset (Configuration H)) (s : Configuration H) {w u v : V}
    (hc : C.card < (reconfiguration H).minDegree) (hw : CleanRoot C w)
    (huv : u ≠ v)
    (hB : CutReach (reconfiguration H) C s ⟨{u, v}, visible_pair hH u v⟩)
    (hwout : ¬ CutReach (reconfiguration H) C s ⟨{w}, visible_singleton H w⟩)
    (hdom : Dominates H w u v)
    (hmin : ∀ a b, a ≠ b →
      CutReach (reconfiguration H) C s ⟨{a, b}, visible_pair hH a b⟩ →
      H.dist u w + H.dist v w ≤ H.dist a w + H.dist b w) :
    (reconfiguration H).degree ⟨{u, v}, visible_pair hH u v⟩ ≤ C.card := by
  classical
  let B : Configuration H := ⟨{u, v}, visible_pair hH u v⟩
  let Y : Finset V := Finset.univ \ {u, v}
  let E : Finset V := Y.filter (Exceptional C s u v)
  obtain ⟨p, hpu, hp⟩ := inward_predecessor hH hdom.1
  obtain ⟨F, hFC, hFcard, hFI, hFL⟩ := simultaneous_inward_payments hH C s
    hdom hpu hp hmin E (fun y hy => (Finset.mem_filter.mp hy).2)
  have hsingle := stranded_singletons hH C s (hc.trans_le minDegree_le_host_order) hw hwout
  have hlabels := stranded_pair_labels hH C s hsingle huv hB
  have hI : 2 ≤ (C.filter fun T => T.val ⊆ {u, v}).card := by
    let U : Configuration H := ⟨{u}, visible_singleton H u⟩
    let Q : Configuration H := ⟨{v}, visible_singleton H v⟩
    have hUC : U ∈ C := by simpa [U, deletedLabels] using hlabels.1
    have hQC : Q ∈ C := by simpa [Q, deletedLabels] using hlabels.2
    apply two_cuts (Finset.mem_filter.mpr ⟨hUC, by simp [U]⟩)
      (Finset.mem_filter.mpr ⟨hQC, by simp [Q]⟩)
    intro he
    have hv := congrArg Subtype.val he
    exact huv (Finset.singleton_injective hv)
  have hsum := Finset.sum_le_sum (s := Y) (fun y hy =>
    minimum_pair_local_bound (y := y) hH C s hc hw huv
      (by have hn := (Finset.mem_sdiff.mp hy).2; exact fun he => hn (by simp [he]))
      (by have hn := (Finset.mem_sdiff.mp hy).2; exact fun he => hn (by simp [he]))
      hB hwout hdom hmin)
  have hEcard : (∑ y ∈ Y, if Exceptional C s u v y then 1 else 0) = E.card := by
    simp [E, Finset.sum_boole]
  rw [Finset.sum_add_distrib, hEcard, ← hFcard] at hsum
  have hY : Disjoint Y ({u, v} : Finset V) := Finset.sdiff_disjoint
  have hbudget := joint_cut_budget C {u, v} Y hY F hFC hFI (fun y _ => hFL y)
  have hd := degree_by_label_classes H B
  have hcard : B.val.card = 2 := by simp [B, huv]
  rw [hcard] at hd
  change (reconfiguration H).degree B ≤ C.card
  change (reconfiguration H).degree B ≤ 2 + ∑ y ∈ Y,
    (localCutClass ((reconfiguration H).neighborFinset
      ⟨{u, v}, visible_pair hH u v⟩) {u, v} y).card at hd
  change (∑ y ∈ Y, _) ≤ _ at hsum
  omega

private theorem stranded_pair_exists (hH : H.Connected)
    (C : Finset (Configuration H)) (s : Configuration H) {w : V}
    (hs : s ∉ C) (hc : C.card < (reconfiguration H).minDegree) (hw : CleanRoot C w)
    (hwout : ¬ CutReach (reconfiguration H) C s ⟨{w}, visible_singleton H w⟩) :
    ∃ u v, u ≠ v ∧ CutReach (reconfiguration H) C s ⟨{u, v}, visible_pair hH u v⟩ := by
  classical
  have hsingle := stranded_singletons hH C s (hc.trans_le minDegree_le_host_order) hw hwout
  have hwC : (⟨{w}, visible_singleton H w⟩ : Configuration H) ∉ C := by
    simpa [deletedLabels] using hw.1
  have hempty : ¬ CutReach (reconfiguration H) C s ⟨∅, visible_empty H⟩ := by
    intro hr
    have hm : (reconfiguration H).Adj ⟨∅, visible_empty H⟩
        ⟨{w}, visible_singleton H w⟩ := by
      change MixedMove H ∅ {w}
      simpa using (mixedMove_insert H ∅ (x := w) (by simp))
    exact hwout (cutReach_step hr hm hwC)
  by_contra hnpair
  have hlow (T : Configuration H) (hr : CutReach (reconfiguration H) C s T) :
      3 ≤ T.val.card := by
    by_contra hn
    have hcases : T.val.card = 0 ∨ T.val.card = 1 ∨ T.val.card = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · have he : T = ⟨∅, visible_empty H⟩ := Subtype.ext (Finset.card_eq_zero.mp h0)
      exact hempty (he ▸ hr)
    · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
      have he : T = ⟨{x}, visible_singleton H x⟩ := Subtype.ext hx
      exact hsingle x (he ▸ hr)
    · obtain ⟨u, v, huv, he⟩ := Finset.card_eq_two.mp h2
      exact hnpair ⟨u, v, huv, (Subtype.ext he : T = ⟨{u, v}, visible_pair hH u v⟩) ▸ hr⟩
  obtain ⟨T, _, hT⟩ := high_rank_component H C s hs hlow
  have hm := (reconfiguration H).minDegree_le_degree T
  omega

private theorem stranded_component_impossible (hH : H.Connected)
    (C : Finset (Configuration H)) (s : Configuration H) {w : V}
    (hs : s ∉ C) (hc : C.card < (reconfiguration H).minDegree) (hw : CleanRoot C w)
    (hwout : ¬ CutReach (reconfiguration H) C s ⟨{w}, visible_singleton H w⟩) : False := by
  obtain ⟨u, v, huv, hB, hmin⟩ := minimal_pair_exists hH C s w
    (stranded_pair_exists hH C s hs hc hw hwout)
  rcases stranded_pair_comparable hH C s hc hw huv hB hwout with hdom | hdom
  · have hd := minimum_pair_degree hH C s hc hw huv hB hwout hdom hmin
    have hm := (reconfiguration H).minDegree_le_degree ⟨{u, v}, visible_pair hH u v⟩
    omega
  · have hB' : CutReach (reconfiguration H) C s ⟨{v, u}, visible_pair hH v u⟩ := by
      simpa only [Finset.pair_comm] using hB
    have hmin' : ∀ a b, a ≠ b →
        CutReach (reconfiguration H) C s ⟨{a, b}, visible_pair hH a b⟩ →
        H.dist v w + H.dist u w ≤ H.dist a w + H.dist b w := by
      intro a b hab hr
      simpa only [Nat.add_comm] using hmin a b hab hr
    have hd := minimum_pair_degree hH C s hc hw huv.symm hB' hwout hdom hmin'
    have hm := (reconfiguration H).minDegree_le_degree ⟨{v, u}, visible_pair hH v u⟩
    omega

/-- Every original mutual-visibility configuration and every legal mixed move is retained. -/
theorem result : FullMaximalConnectivityClaim := by
  intro V _ _ _ H hH
  classical
  let : Nonempty (Configuration H) := ⟨⟨∅, visible_empty H⟩⟩
  apply le_antisymm (connectivity_le_minDegree (reconfiguration H))
  apply minDegree_le_connectivity
  intro C hc
  obtain ⟨w, hw⟩ := exists_cleanRoot C (hc.trans_le minDegree_le_host_order)
  have hreach (s : Configuration H) (hs : s ∉ C) :
      CutReach (reconfiguration H) C s ⟨{w}, visible_singleton H w⟩ := by
    by_contra hn
    exact stranded_component_impossible hH C s hs hc hw hn
  intro s t
  obtain ⟨_, _, hsr⟩ := hreach s.val s.property
  obtain ⟨_, _, htr⟩ := hreach t.val t.property
  exact hsr.trans htr.symm

end D5.S3.Combinatorics.Graph.MutualVisibility
