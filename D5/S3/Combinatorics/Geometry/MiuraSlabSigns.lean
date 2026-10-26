/- GID: D5/S3/Combinatorics/Geometry/MiuraSlabSigns
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraSlabSigns
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: Frozen cut signs force a minimum-type occupied slab. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraSlabClassification

/-! Actual sign transitions and nonneutral slab existence. -/

@[expose] public section

namespace D5.S3.Combinatorics.Geometry.MiuraSlabSigns

open MiuraHeightEnvelope MiuraStripRigidity MiuraSlabExtrema MiuraSlabNeutral
open MiuraSlabIncidence MiuraSlabFrozen MiuraSlabClassification

variable {m n : ℕ}

private theorem frozen_internal {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n) (i : Fin m) (hi : ¬ RowOccupied h i) :
    0 < i.val ∧ i.val + 1 < m := by
  constructor
  · by_contra hnot
    have he : i = (⟨0, by omega⟩ : Fin m) := Fin.ext (by change i.val = 0; omega)
    exact hi (he.symm ▸ (boundary_rows_occupied hh hm hn).1)
  · by_contra hnot
    have he : i = (⟨m - 1, by omega⟩ : Fin m) :=
      Fin.ext (by change i.val = m - 1; have := i.isLt; omega)
    exact hi (he.symm ▸ (boundary_rows_occupied hh hm hn).2)

private def slope (h : Cell m n → ℤ) (hn : 0 < n) (i : Fin m) : ℤ :=
  h (i, ⟨0, hn⟩) - h (⟨i.val - 1, by have := i.isLt; omega⟩, ⟨0, hn⟩)

private theorem frozen_cuts {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n) (i : Fin m) (hi : ¬ RowOccupied h i) :
    (slope h hn i = 1 ∨ slope h hn i = -1) ∧
    (∀ j : Fin n, h (i, j) = h (⟨i.val - 1, by have := i.isLt; omega⟩, j) + slope h hn i) ∧
    (∀ hb : i.val + 1 < m, ∀ j : Fin n,
      h (⟨i.val + 1, hb⟩, j) = h (i, j) + slope h hn i) := by
  obtain ⟨ht, hb⟩ := frozen_internal hh hm hn i hi
  obtain ⟨s, hs, htop, hbottom⟩ := inactive_row_uniform_cuts hh hn i hi ht hb
  have he : slope h hn i = s := by
    have := htop ⟨0, hn⟩
    dsimp [slope]
    omega
  rw [he]
  exact ⟨hs, htop, fun _ j => hbottom j⟩

private theorem first_frozen_positive {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n) (g : Fin m) (hg : ¬ RowOccupied h g)
    (hbefore : ∀ i : Fin m, i < g → RowOccupied h i)
    (hsg : slope h hn g = 1) : (minRowSlabs h).Nonempty := by
  classical
  obtain ⟨hg0, hg1⟩ := frozen_internal hh hm hn g hg
  let I : Interval m := ⟨⟨0, by omega⟩, ⟨g.val - 1, by omega⟩, by simp⟩
  have hI : IsRowSlab h I := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      apply hbefore i
      change 0 ≤ i.val ∧ i.val ≤ g.val - 1 at hi
      change i.val < g.val
      omega
    · intro k hk
      change k.val + 1 = 0 at hk
      omega
    · intro k hk
      have he : k = g := Fin.ext (by change g.val - 1 + 1 = k.val at hk; omega)
      exact he.symm ▸ hg
  have hout : RowOutward h I 1 := outward_of_cuts I 1 (by
    intro ht; change 0 < 0 at ht; omega) (by
    intro hb j
    have he := (frozen_cuts hh hm hn g hg).2.1 j
    rw [hsg] at he
    have hnext : (⟨I.last.val + 1, hb⟩ : Fin m) = g :=
      Fin.ext (by change g.val - 1 + 1 = g.val; omega)
    rw [hnext]
    exact he)
  refine ⟨I, ?_⟩
  simp only [minRowSlabs, rowSlabs, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hI, Or.inr (by change g.val - 1 + 1 < m; omega), hout⟩

private theorem last_frozen_negative {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n) (f : Fin m) (hf : ¬ RowOccupied h f)
    (hafter : ∀ i : Fin m, f < i → RowOccupied h i)
    (hsf : slope h hn f = -1) : (minRowSlabs h).Nonempty := by
  classical
  obtain ⟨hf0, hf1⟩ := frozen_internal hh hm hn f hf
  let I : Interval m := ⟨⟨f.val + 1, hf1⟩, ⟨m - 1, by omega⟩, by
    change f.val + 1 ≤ m - 1; omega⟩
  have hI : IsRowSlab h I := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      apply hafter i
      change f.val + 1 ≤ i.val ∧ i.val ≤ m - 1 at hi
      change f.val < i.val
      omega
    · intro k hk
      have he : k = f := Fin.ext (by change k.val + 1 = f.val + 1 at hk; omega)
      exact he.symm ▸ hf
    · intro k hk
      change m - 1 + 1 = k.val at hk
      have := k.isLt
      omega
  have hout : RowOutward h I 1 := outward_of_cuts I 1 (by
    intro ht j
    have he := (frozen_cuts hh hm hn f hf).2.2 hf1 j
    rw [hsf] at he
    have hprev : (⟨I.first.val - 1, by omega⟩ : Fin m) = f :=
      Fin.ext (by change f.val + 1 - 1 = f.val; omega)
    rw [hprev]
    change h (f, j) = h (⟨f.val + 1, hf1⟩, j) + 1
    omega) (by intro hb; change m - 1 + 1 < m at hb; omega)
  refine ⟨I, ?_⟩
  simp only [minRowSlabs, rowSlabs, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hI, Or.inl (by change 0 < f.val + 1; omega), hout⟩

private theorem frozen_negative_positive_gap {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n) (f g : Fin m)
    (hf : ¬ RowOccupied h f) (hg : ¬ RowOccupied h g) (hfg : f < g)
    (hgap : ∀ i : Fin m, f < i → i < g → RowOccupied h i)
    (hsf : slope h hn f = -1) (hsg : slope h hn g = 1) :
    (minRowSlabs h).Nonempty := by
  classical
  obtain ⟨hf0, hf1⟩ := frozen_internal hh hm hn f hf
  obtain ⟨hg0, hg1⟩ := frozen_internal hh hm hn g hg
  have hspace : f.val + 1 < g.val := by
    have he1 := (frozen_cuts hh hm hn f hf).2.2 hf1 ⟨0, hn⟩
    have he2 := (frozen_cuts hh hm hn g hg).2.1 ⟨0, hn⟩
    rw [hsf] at he1
    rw [hsg] at he2
    by_contra hnot
    have hnext : (⟨f.val + 1, hf1⟩ : Fin m) = g := Fin.ext (by change f.val + 1 = g.val; omega)
    have hprev : (⟨g.val - 1, by omega⟩ : Fin m) = f := Fin.ext (by change g.val - 1 = f.val; omega)
    rw [hnext] at he1
    rw [hprev] at he2
    omega
  let I : Interval m := ⟨⟨f.val + 1, hf1⟩, ⟨g.val - 1, by omega⟩, by
    change f.val + 1 ≤ g.val - 1; omega⟩
  have hI : IsRowSlab h I := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      apply hgap i
      · change f.val + 1 ≤ i.val ∧ i.val ≤ g.val - 1 at hi
        change f.val < i.val
        omega
      · change f.val + 1 ≤ i.val ∧ i.val ≤ g.val - 1 at hi
        change i.val < g.val
        omega
    · intro k hk
      have he : k = f := Fin.ext (by change k.val + 1 = f.val + 1 at hk; omega)
      exact he.symm ▸ hf
    · intro k hk
      have he : k = g := Fin.ext (by change g.val - 1 + 1 = k.val at hk; omega)
      exact he.symm ▸ hg
  have hout : RowOutward h I 1 := outward_of_cuts I 1 (by
    intro ht j
    have he := (frozen_cuts hh hm hn f hf).2.2 hf1 j
    rw [hsf] at he
    have hprev : (⟨I.first.val - 1, by omega⟩ : Fin m) = f := Fin.ext (by change f.val + 1 - 1 = f.val; omega)
    rw [hprev]
    change h (f, j) = h (⟨f.val + 1, hf1⟩, j) + 1
    omega) (by
    intro hb j
    have he := (frozen_cuts hh hm hn g hg).2.1 j
    rw [hsg] at he
    have hnext : (⟨I.last.val + 1, hb⟩ : Fin m) = g := Fin.ext (by change g.val - 1 + 1 = g.val; omega)
    rw [hnext]
    exact he)
  refine ⟨I, ?_⟩
  simp only [minRowSlabs, rowSlabs, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hI, Or.inl (by change 0 < f.val + 1; omega), hout⟩

/-- Every actual axis with a frozen row has a minimum-type occupied slab. -/
theorem minimum_row_slab_exists {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n) (hf : ∃ i, ¬ RowOccupied h i) :
    (minRowSlabs h).Nonempty := by
  classical
  let F : Finset (Fin m) := Finset.univ.filter (fun i => ¬ RowOccupied h i)
  have hF : F.Nonempty := by
    obtain ⟨i, hi⟩ := hf
    exact ⟨i, by simp [F, hi]⟩
  let P := F.filter (fun i => slope h hn i = 1)
  by_cases hP : P.Nonempty
  · let g := P.min' hP
    have hgP : g ∈ P := Finset.min'_mem P hP
    have hg : ¬ RowOccupied h g := (Finset.mem_filter.mp (Finset.mem_filter.mp hgP).1).2
    have hsg : slope h hn g = 1 := (Finset.mem_filter.mp hgP).2
    let L := F.filter (fun i => i < g)
    by_cases hL : L.Nonempty
    · let f := L.max' hL
      have hfL : f ∈ L := Finset.max'_mem L hL
      have hf' : ¬ RowOccupied h f := (Finset.mem_filter.mp (Finset.mem_filter.mp hfL).1).2
      have hfg : f < g := (Finset.mem_filter.mp hfL).2
      have hsf : slope h hn f = -1 := by
        rcases (frozen_cuts hh hm hn f hf').1 with he | he
        · have hfP : f ∈ P := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hfL).1, he⟩
          have hle := Finset.min'_le P f hfP
          omega
        · exact he
      apply frozen_negative_positive_gap hh hm hn f g hf' hg hfg ?_ hsf hsg
      intro i hfi hig
      by_contra hi
      have hiL : i ∈ L := by simp [L, F, hi, hig]
      have hle := Finset.le_max' L i hiL
      omega
    · apply first_frozen_positive hh hm hn g hg ?_ hsg
      intro i hig
      by_contra hi
      have hiL : i ∈ L := by simp [L, F, hi, hig]
      exact hL ⟨i, hiL⟩
  · let f := F.max' hF
    have hfF : f ∈ F := Finset.max'_mem F hF
    have hf' : ¬ RowOccupied h f := (Finset.mem_filter.mp hfF).2
    have hsf : slope h hn f = -1 := by
      rcases (frozen_cuts hh hm hn f hf').1 with he | he
      · exact (hP ⟨f, Finset.mem_filter.mpr ⟨hfF, he⟩⟩).elim
      · exact he
    apply last_frozen_negative hh hm hn f hf' ?_ hsf
    intro i hfi
    by_contra hi
    have hiF : i ∈ F := by simp [F, hi]
    have hle := Finset.le_max' F i hiF
    omega


private theorem neg_occupied (h : Cell m n → ℤ) (i : Fin m) :
    RowOccupied (fun v => -h v) i ↔ RowOccupied h i := by
  constructor
  · rintro ⟨j, hmin | hmax⟩
    · refine ⟨j, Or.inr ?_⟩
      intro u hu; have := hmin u hu; dsimp at this; omega
    · refine ⟨j, Or.inl ?_⟩
      intro u hu; have := hmax u hu; dsimp at this; omega
  · rintro ⟨j, hmin | hmax⟩
    · refine ⟨j, Or.inr ?_⟩
      intro u hu; have := hmin u hu; change -h u = -h (i, j) - 1; omega
    · refine ⟨j, Or.inl ?_⟩
      intro u hu; have := hmax u hu; change -h u = -h (i, j) + 1; omega

/-- The other actual nonneutral type exists as well, by height negation. -/
theorem maximum_row_slab_exists {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n) (hf : ∃ i, ¬ RowOccupied h i) :
    (maxRowSlabs h).Nonempty := by
  classical
  let g : Cell m n → ℤ := fun v => -h v
  have hg : IsHeight g := by
    intro v u hu
    simpa only [g, neg_sub_neg, abs_sub_comm] using hh v u hu
  have hfg : ∃ i, ¬ RowOccupied g i := by
    obtain ⟨i, hi⟩ := hf
    exact ⟨i, fun hc => hi ((neg_occupied h i).mp hc)⟩
  obtain ⟨I, hI⟩ := minimum_row_slab_exists hg hm hn hfg
  obtain ⟨hIg, hp, hout⟩ := Finset.mem_filter.mp hI
  have hslabg : IsRowSlab g I := (Finset.mem_filter.mp hIg).2
  have hslab : IsRowSlab h I := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      exact (neg_occupied h i).mp (hslabg.1 i hi)
    · intro i hi hocc
      exact hslabg.2.1 i hi ((neg_occupied h i).mpr hocc)
    · intro i hi hocc
      exact hslabg.2.2 i hi ((neg_occupied h i).mpr hocc)
  have hout' : RowOutward h I (-1) := by
    intro v u hv hu hadj
    have := hout v u hv hu hadj
    change -h u = -h v + 1 at this
    omega
  refine ⟨I, ?_⟩
  simp only [maxRowSlabs, rowSlabs, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hslab, hp, hout'⟩

end D5.S3.Combinatorics.Geometry.MiuraSlabSigns
