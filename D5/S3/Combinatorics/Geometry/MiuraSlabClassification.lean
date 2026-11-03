/- GID: D5/S3/Combinatorics/Geometry/MiuraSlabClassification
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraSlabClassification
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: Every actual occupied slab beside frozen rows has a geometric type. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraSlabFrozen

/-! Classification of maximal occupied intervals by their actual cut signs. -/

@[expose] public section

namespace D5.S3.Combinatorics.Geometry.MiuraSlabClassification

open MiuraHeightEnvelope MiuraStripRigidity MiuraSlabExtrema MiuraSlabNeutral
open MiuraSlabIncidence MiuraSlabFrozen

variable {m n : ℕ}

private theorem row_slab_proper {h : Cell m n → ℤ} (I : Interval m)
    (hI : IsRowSlab h I) (hf : ∃ i, ¬ RowOccupied h i) : Proper I := by
  obtain ⟨i, hi⟩ := hf
  by_contra hnot
  have hzero : I.first.val = 0 := by change ¬ (0 < I.first.val ∨ I.last.val + 1 < m) at hnot; omega
  have hlast : I.last.val + 1 = m := by
    have := I.last.isLt
    change ¬ (0 < I.first.val ∨ I.last.val + 1 < m) at hnot
    omega
  exact hi (hI.1 i (by
    change I.first.val ≤ i.val ∧ i.val ≤ I.last.val
    have := i.isLt
    omega))

private theorem row_slab_top_cut {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n) (I : Interval m) (hI : IsRowSlab h I)
    (ht : 0 < I.first.val) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ j : Fin n,
      h (I.first, j) = h (⟨I.first.val - 1, by omega⟩, j) + s := by
  let k : Fin m := ⟨I.first.val - 1, by have := I.first.isLt; omega⟩
  have hk : ¬ RowOccupied h k := hI.2.1 k (by dsimp [k]; omega)
  have hk0 : 0 < k.val := by
    by_contra hnot
    have he : k = (⟨0, by omega⟩ : Fin m) := Fin.ext (by change k.val = 0; omega)
    exact hk (he.symm ▸ (boundary_rows_occupied hh hm hn).1)
  have hk1 : k.val + 1 < m := by dsimp [k]; have := I.first.isLt; omega
  obtain ⟨s, hs, _, hbottom⟩ := inactive_row_uniform_cuts hh hn k hk hk0 hk1
  refine ⟨s, hs, ?_⟩
  intro j
  have he : (⟨k.val + 1, hk1⟩ : Fin m) = I.first := Fin.ext (by dsimp [k] <;> omega)
  have hv := hbottom j
  rw [he] at hv
  exact hv

private theorem row_slab_bottom_cut {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n) (I : Interval m) (hI : IsRowSlab h I)
    (hb : I.last.val + 1 < m) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ j : Fin n,
      h (⟨I.last.val + 1, hb⟩, j) = h (I.last, j) + s := by
  let k : Fin m := ⟨I.last.val + 1, hb⟩
  have hk : ¬ RowOccupied h k := hI.2.2 k rfl
  have hk0 : 0 < k.val := by dsimp [k]; omega
  have hk1 : k.val + 1 < m := by
    by_contra hnot
    have he : k = (⟨m - 1, by omega⟩ : Fin m) := Fin.ext (by change k.val = m - 1; have := k.isLt; omega)
    exact hk (he.symm ▸ (boundary_rows_occupied hh hm hn).2)
  obtain ⟨s, hs, htop, _⟩ := inactive_row_uniform_cuts hh hn k hk hk0 hk1
  refine ⟨s, hs, ?_⟩
  intro j
  have he : (⟨k.val - 1, by omega⟩ : Fin m) = I.last := Fin.ext (by dsimp [k] <;> omega)
  have hv := htop j
  rw [he] at hv
  exact hv

theorem outward_of_cuts {h : Cell m n → ℤ} (I : Interval m) (t : ℤ)
    (htop : ∀ ht : 0 < I.first.val, ∀ j : Fin n,
      h (⟨I.first.val - 1, by omega⟩, j) = h (I.first, j) + t)
    (hbottom : ∀ hb : I.last.val + 1 < m, ∀ j : Fin n,
      h (⟨I.last.val + 1, hb⟩, j) = h (I.last, j) + t) : RowOutward h I t := by
  intro v u hv hu hadj
  have hv' : I.first.val ≤ v.1.val ∧ v.1.val ≤ I.last.val := hv
  have hu' : ¬ (I.first.val ≤ u.1.val ∧ u.1.val ≤ I.last.val) := hu
  have hd := hadj
  simp only [adj, gdist] at hd
  have hj : u.2 = v.2 := by apply Fin.ext; omega
  by_cases hlo : u.1.val < I.first.val
  · have ht : 0 < I.first.val := by omega
    have he1 : v.1 = I.first := Fin.ext (by omega)
    have he2 : u.1 = (⟨I.first.val - 1, by omega⟩ : Fin m) := Fin.ext (by change u.1.val = I.first.val - 1; omega)
    have hvcell : v = (I.first, v.2) := Prod.ext he1 rfl
    have hucell : u = (⟨I.first.val - 1, by omega⟩, v.2) := Prod.ext he2 hj
    rw [hvcell, hucell]
    exact htop ht v.2
  · have hb : I.last.val + 1 < m := by have := u.1.isLt; omega
    have he1 : v.1 = I.last := Fin.ext (by omega)
    have he2 : u.1 = (⟨I.last.val + 1, hb⟩ : Fin m) :=
      Fin.ext (by change u.1.val = I.last.val + 1; omega)
    have hvcell : v = (I.last, v.2) := Prod.ext he1 rfl
    have hucell : u = (⟨I.last.val + 1, hb⟩, v.2) := Prod.ext he2 hj
    rw [hvcell, hucell]
    exact hbottom hb v.2

/-- Every actual occupied slab is minimum, maximum or neutral whenever the
axis has a frozen row. The boundary and frozen-cut premises are derived. -/
theorem row_slab_classification {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n) (hf : ∃ i, ¬ RowOccupied h i)
    (I : Interval m) (hI : IsRowSlab h I) :
    I ∈ minRowSlabs h ∨ I ∈ maxRowSlabs h ∨ I ∈ neutralRowSlabs h := by
  classical
  have hp := row_slab_proper I hI hf
  have hmem : I ∈ rowSlabs h := by simp [rowSlabs, hI]
  by_cases ht : 0 < I.first.val
  · obtain ⟨s, hs, htop⟩ := row_slab_top_cut hh hm hn I hI ht
    by_cases hb : I.last.val + 1 < m
    · obtain ⟨t, ht', hbottom⟩ := row_slab_bottom_cut hh hm hn I hI hb
      by_cases he : s = t
      · right; right
        simp only [neutralRowSlabs, Finset.mem_filter]
        exact ⟨hmem, s, hs, ht, hb, htop, he.symm ▸ hbottom⟩
      · have hout : RowOutward h I t := outward_of_cuts I t (by
          intro _ j
          have he := htop j
          rcases hs with hs | hs <;> rcases ht' with htt | htt <;> omega)
          (fun _ j => hbottom j)
        rcases ht' with rfl | rfl
        · left; simp [minRowSlabs, hmem, hp, hout]
        · right; left; simp [maxRowSlabs, hmem, hp, hout]
    · have hout : RowOutward h I (-s) := outward_of_cuts I (-s) (by
        intro _ j
        have he := htop j
        omega) (by intro hb'; exact (hb hb').elim)
      rcases hs with rfl | rfl
      · right; left; simpa [maxRowSlabs, hmem, hp] using hout
      · left; simpa [minRowSlabs, hmem, hp] using hout
  · have hb : I.last.val + 1 < m := hp.resolve_left ht
    obtain ⟨t, ht', hbottom⟩ := row_slab_bottom_cut hh hm hn I hI hb
    have hout : RowOutward h I t := outward_of_cuts I t
      (by intro ht'; exact (ht ht').elim) (fun _ j => hbottom j)
    rcases ht' with rfl | rfl
    · left; simp [minRowSlabs, hmem, hp, hout]
    · right; left; simp [maxRowSlabs, hmem, hp, hout]


private theorem outward_sign_unique {h : Cell m n → ℤ} (hn : 0 < n)
    (I : Interval m) (hp : Proper I) (s t : ℤ)
    (hs : RowOutward h I s) (ht : RowOutward h I t) : s = t := by
  let j : Fin n := ⟨0, hn⟩
  rcases hp with hp | hp
  · let u : Cell m n := (⟨I.first.val - 1, by have := I.first.isLt; omega⟩, j)
    have hu : ¬ I.Contains u.1 := by
      change ¬ (I.first.val ≤ I.first.val - 1 ∧ I.first.val - 1 ≤ I.last.val)
      omega
    have ha : adj ((I.first, j) : Cell m n) u := by
      simp only [adj, gdist, u]; omega
    have he := hs (I.first, j) u ⟨le_rfl, I.ordered⟩ hu ha
    have hf := ht (I.first, j) u ⟨le_rfl, I.ordered⟩ hu ha
    omega
  · let u : Cell m n := (⟨I.last.val + 1, hp⟩, j)
    have hu : ¬ I.Contains u.1 := by
      change ¬ (I.first.val ≤ I.last.val + 1 ∧ I.last.val + 1 ≤ I.last.val)
      omega
    have ha : adj ((I.last, j) : Cell m n) u := by
      simp only [adj, gdist, u]; omega
    have he := hs (I.last, j) u ⟨I.ordered, le_rfl⟩ hu ha
    have hf := ht (I.last, j) u ⟨I.ordered, le_rfl⟩ hu ha
    omega

/-- The geometric types partition all actual row slabs on an axis with a
frozen row. There is no omitted boundary or neutral class. -/
theorem row_slab_card_partition {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n) (hf : ∃ i, ¬ RowOccupied h i) :
    (rowSlabs h).card = (minRowSlabs h).card + (maxRowSlabs h).card +
      (neutralRowSlabs h).card := by
  classical
  have he : rowSlabs h = (minRowSlabs h ∪ maxRowSlabs h) ∪ neutralRowSlabs h := by
    ext I
    simp only [Finset.mem_union]
    constructor
    · intro hI
      have hc := row_slab_classification hh hm hn hf I (Finset.mem_filter.mp hI).2
      tauto
    · rintro ((hI | hI) | hI) <;> exact (Finset.mem_filter.mp hI).1
  have hmn : Disjoint (minRowSlabs h) (maxRowSlabs h) := by
    apply Finset.disjoint_left.mpr
    intro I hI hJ
    have hi := (Finset.mem_filter.mp hI).2
    have hj := (Finset.mem_filter.mp hJ).2
    have he := outward_sign_unique hn I hi.1 1 (-1) hi.2 hj.2
    omega
  have hmn0 : Disjoint (minRowSlabs h ∪ maxRowSlabs h) (neutralRowSlabs h) := by
    apply Finset.disjoint_left.mpr
    intro I hI hJ
    obtain ⟨_, s, hs, hcuts⟩ := Finset.mem_filter.mp hJ
    rcases Finset.mem_union.mp hI with hI | hI
    · exact neutral_not_outward hn I s 1 (by norm_num) hcuts (Finset.mem_filter.mp hI).2.2
    · exact neutral_not_outward hn I s (-1) (by norm_num) hcuts (Finset.mem_filter.mp hI).2.2
  rw [he, Finset.card_union_of_disjoint hmn0, Finset.card_union_of_disjoint hmn]

end D5.S3.Combinatorics.Geometry.MiuraSlabClassification
