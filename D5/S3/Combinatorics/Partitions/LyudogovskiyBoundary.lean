/- GID: D5/S3/Combinatorics/Partitions/LyudogovskiyBoundary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/LyudogovskiyBoundary
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram]
   utility: none
   digest: First positive size with a transfer edge between consecutive exact local clique layers. -/

import D5.S3.Combinatorics.Partitions.LyudogovskiySimplex

/-! Lyudogovskiy, Problem 6.3 (arXiv:2603.23228v1, p. 12), issue #34731.

For positive lower dimension, the boundary first occurs at the first
appearance of the higher exact layer. At lower dimension zero the defining
set is empty: the endpoints of any edge form a two-element clique, so the
supremum defining each endpoint's local dimension is at least one.
-/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Partitions.LyudogovskiySimplex

set_option maxHeartbeats 800000 in
/-- The least positive size admitting a literal transfer between the exact
local dimensions r and r+1, for every positive lower dimension r. -/
theorem boundary_result (r : ℕ) (hr : 1 ≤ r) :
    IsLeast {n : ℕ | 0 < n ∧ ∃ p q : Nat.Partition n,
      (graph n).Adj p q ∧ localDimension p = r ∧ localDimension q = r + 1}
      (triangular (r + 1) + 1) := by
  classical
  let n := triangular (r + 1) + 1
  have hn : 0 < n := by dsimp [n]; omega
  constructor
  · change 0 < n ∧ ∃ p q : Nat.Partition n,
      (graph n).Adj p q ∧ localDimension p = r ∧ localDimension q = r + 1
    refine ⟨hn, ?_⟩
    -- The upper endpoint U = (r+2,r,...,1).
    let U := expandedStaircase (r + 1) 1
    have hUcard : U.card = n := expanded_card (r + 1) 1
    have hUm (i j : ℕ) : (i,j) ∈ U ↔ i + j < r + 1 ∨ i = 0 ∧ j < r + 2 := by
      change (i,j) ∈ (staircase (r + 1)).cells ∪ ({0} ×ˢ Finset.range (r+2)) ↔ _
      rw [Finset.mem_union]
      change ((i,j) ∈ staircase (r+1) ∨ (i,j) ∈ ({0} ×ˢ Finset.range (r+2))) ↔ _
      rw [mem_staircase]
      simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range]
    have hbU : (r,0) ∈ U := (hUm r 0).mpr (Or.inl (by omega))
    -- Delete the last singleton. D = (r+2,r,...,2) is the common diagram.
    let D : YoungDiagram :=
      { cells := U.cells.erase (r,0)
        isLowerSet := by
          rintro ⟨a,b⟩ ⟨i,j⟩ hxy hy
          obtain ⟨hne, hU⟩ := Finset.mem_erase.mp hy
          refine Finset.mem_erase.mpr ⟨?_, U.isLowerSet hxy hU⟩
          intro he
          have ha := congrArg Prod.fst he
          have hb := congrArg Prod.snd he
          have hi := hxy.1
          have hj := hxy.2
          have hm := (hUm a b).mp hU
          have hae : a = r := by dsimp at *; omega
          have hbe : b = 0 := by dsimp at *; omega
          exact hne (Prod.ext hae hbe) }
    have hDm (i j : ℕ) : (i,j) ∈ D ↔ i < r ∧ (i + j < r + 1 ∨ i = 0 ∧ j < r + 2) := by
      change (i,j) ∈ U.cells.erase (r,0) ↔ _
      rw [Finset.mem_erase]
      change ((i,j) ≠ (r,0) ∧ (i,j) ∈ U) ↔ _
      rw [hUm]
      simp only [ne_eq, Prod.mk.injEq]
      omega
    have hDcard : D.card = n - 1 := by
      change (U.cells.erase (r,0)).card = _
      rw [Finset.card_erase_of_mem hbU]
      exact congrArg (· - 1) hUcard
    -- One addable corner for every existing row and the next empty row.
    let c (i : Fin (r + 1)) : ℕ × ℕ :=
      (i.val, if i.val = 0 then r + 2 else if i.val = r then 0 else r + 1 - i.val)
    have hc_not (i : Fin (r + 1)) : c i ∉ D := by
      have hi := i.isLt
      dsimp [c]
      rw [hDm]
      split_ifs <;> omega
    have hc_below (i : Fin (r + 1)) (x : ℕ × ℕ)
        (h : x ≤ c i) (hne : x ≠ c i) : x ∈ D := by
      rcases x with ⟨a,b⟩
      have hi := i.isLt
      have ha : a ≤ i.val := h.1
      have hb : b ≤ (c i).2 := h.2
      dsimp [c] at hb hne
      rw [hDm]
      simp only [Prod.mk.injEq] at hne
      split_ifs at hb hne <;> omega
    let E (i : Fin (r + 1)) : YoungDiagram :=
      { cells := insert (c i) D.cells
        isLowerSet := by
          intro y x hxy hy
          rcases Finset.mem_insert.mp hy with he | hy
          · subst y
            by_cases he : x = c i
            · exact Finset.mem_insert.mpr (Or.inl he)
            · exact Finset.mem_insert.mpr (Or.inr (hc_below i x hxy he))
          · exact Finset.mem_insert.mpr (Or.inr (D.isLowerSet hxy hy)) }
    have hEcard (i : Fin (r + 1)) : (E i).card = n := by
      change (insert (c i) D.cells).card = n
      rw [Finset.card_insert_of_notMem (hc_not i)]
      change D.card + 1 = n
      omega
    let P (i : Fin (r + 1)) : Nat.Partition n := (E i).toPartition (hEcard i)
    have hP (i : Fin (r + 1)) : YoungDiagram.ofPartition (P i) = E i :=
      YoungDiagram.ofPartition_toPartition (hEcard i)
    have hPinj : Function.Injective P := by
      intro i j hij
      have he := congrArg YoungDiagram.ofPartition hij
      rw [hP i, hP j] at he
      have hm : c i ∈ E j := by
        rw [← he]
        exact Finset.mem_insert_self _ _
      rcases Finset.mem_insert.mp hm with hc | hc
      · exact Fin.ext (congrArg Prod.fst hc)
      · exact (hc_not i hc).elim
    let C : Finset (Nat.Partition n) := Finset.univ.image P
    have hCcard : C.card = r + 1 := by
      dsimp [C]
      rw [Finset.card_image_of_injective _ hPinj]
      simp
    have hC : (graph n).IsClique (C : Set (Nat.Partition n)) := by
      intro p hp q hq hpq
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
      apply (transfer_iff_intersection hn _ _).mpr
      rw [hP i, hP j]
      have hne : c i ≠ c j := by
        intro he
        exact hpq (congrArg P (Fin.ext (congrArg Prod.fst he)))
      have he : (E i ⊓ E j).cells = D.cells := by
        ext x
        simp only [YoungDiagram.cells_inf, E, Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨hi,hj⟩
          rcases hi with rfl | hi
          · rcases hj with hj | hj
            · exact (hne hj).elim
            · exact hj
          · exact hi
        · intro hx
          exact ⟨Or.inr hx, Or.inr hx⟩
      change (E i ⊓ E j).cells.card = n - 1
      rw [he]
      exact hDcard
    let top : Fin (r+1) := ⟨r, by omega⟩
    let first : Fin (r+1) := ⟨0, by omega⟩
    have hctop : c top = (r,0) := by
      simp [c, top, Nat.ne_of_gt hr]
    have hcfirst : c first = (0,r+2) := by simp [c, first]
    let p := P first
    let q := P top
    have hpC : p ∈ C := Finset.mem_image.mpr ⟨first, Finset.mem_univ _, rfl⟩
    have hqC : q ∈ C := Finset.mem_image.mpr ⟨top, Finset.mem_univ _, rfl⟩
    have hpq : p ≠ q := by
      intro he
      have hi := congrArg Fin.val (hPinj he)
      change 0 = r at hi
      omega
    have hqU : YoungDiagram.ofPartition q = U := by
      change YoungDiagram.ofPartition (P top) = U
      rw [hP]
      apply YoungDiagram.ext
      change insert (c top) (U.cells.erase (r,0)) = U.cells
      rw [hctop, Finset.insert_erase hbU]
    have hfamily : q ∈ firstFamily (r+1) n := by
      apply Finset.mem_filter.mpr
      rw [hqU]
      refine ⟨Finset.mem_univ _, Finset.subset_union_left, Finset.card_eq_one.mpr ?_⟩
      refine ⟨(0,r+1), ?_⟩
      ext ⟨i,j⟩
      rw [Finset.mem_sdiff, Finset.mem_singleton]
      change ((i,j) ∈ U ∧ (i,j) ∉ staircase (r+1)) ↔ (i,j) = (0,r+1)
      rw [hUm, mem_staircase, Prod.mk.injEq]
      dsimp
      omega
    have hlayer : layer (r+1) n = firstFamily (r+1) n :=
      (first_occurrence_result (r+1) (by omega)).2.1
    have hqLayer : q ∈ layer (r+1) n := by rwa [hlayer]
    have hqDim : localDimension q = r + 1 := (Finset.mem_filter.mp hqLayer).2
    have hlo : r ≤ localDimension p := by
      have h := clique_le_local C hC p hpC
      rw [hCcard] at h
      omega
    have hhi : localDimension p ≤ r + 1 := by
      simpa only [n, maximum_at_threshold] using local_le_maximum p
    have hp_not : (r,0) ∉ YoungDiagram.ofPartition p := by
      change (r,0) ∉ YoungDiagram.ofPartition (P first)
      rw [hP]
      change (r,0) ∉ insert (c first) D.cells
      rw [hcfirst, Finset.mem_insert]
      change ¬ ((r,0) = (0,r+2) ∨ (r,0) ∈ D)
      rw [hDm]
      simp
    have hp_not_upper : localDimension p ≠ r+1 := by
      intro he
      have hmem : p ∈ layer (r+1) n := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
      rw [hlayer] at hmem
      have hsub := (Finset.mem_filter.mp hmem).2.1
      apply hp_not
      apply hsub
      exact (mem_staircase (r+1) (r,0)).mpr (by omega)
    exact ⟨p, q, hC hpC hqC hpq, by omega, hqDim⟩
  · intro m hm
    obtain ⟨hmpos, p, q, _, _, hq⟩ := hm
    exact ((threshold_result.1 (r+1)).2).2
      ⟨hmpos, q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩⟩

end D5.S3.Combinatorics.Partitions.LyudogovskiySimplex
