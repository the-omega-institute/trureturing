/- GID: D5/S3/Combinatorics/Geometry/MiuraSlabIncidence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraSlabIncidence
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: Canonical occupied intervals retain individual extremum incidences. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraSlabNeutral
public import D5.S3.Combinatorics.Geometry.MiuraResidualCount
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Actual maximal occupied intervals and their extremum incidences. -/

@[expose] public section

namespace D5.S3.Combinatorics.Geometry.MiuraSlabIncidence

open MiuraHeightEnvelope MiuraStripRigidity MiuraSlabExtrema MiuraSlabNeutral
open scoped BigOperators

variable {m n : ℕ}

noncomputable instance : Fintype (Interval m) :=
  Fintype.ofInjective (fun I : Interval m => (I.first, I.last)) (by
    intro I J he
    cases I
    cases J
    cases he
    rfl)

/-- A maximal consecutive interval of occupied rows of the actual array. -/
def IsRowSlab (h : Cell m n → ℤ) (I : Interval m) : Prop :=
  (∀ i, I.Contains i → RowOccupied h i) ∧
  (∀ k : Fin m, k.val + 1 = I.first.val → ¬ RowOccupied h k) ∧
  (∀ k : Fin m, I.last.val + 1 = k.val → ¬ RowOccupied h k)

/-- The finite family of actual maximal occupied row intervals. -/
noncomputable def rowSlabs (h : Cell m n → ℤ) : Finset (Interval m) := by
  classical
  exact Finset.univ.filter (IsRowSlab h)

private theorem slab_first_le {h : Cell m n → ℤ} {I J : Interval m}
    (hI : IsRowSlab h I) (hJ : IsRowSlab h J)
    (i : Fin m) (hi : I.Contains i) (hj : J.Contains i) : I.first ≤ J.first := by
  by_contra hnot
  have hlt : J.first.val < I.first.val := by exact Nat.lt_of_not_ge hnot
  let k : Fin m := ⟨I.first.val - 1, by have := I.first.isLt; omega⟩
  have hkJ : J.Contains k := by
    change J.first.val ≤ I.first.val - 1 ∧ I.first.val - 1 ≤ J.last.val
    change I.first.val ≤ i.val ∧ i.val ≤ I.last.val at hi
    change J.first.val ≤ i.val ∧ i.val ≤ J.last.val at hj
    omega
  exact (hI.2.1 k (by dsimp [k]; omega)) (hJ.1 k hkJ)

/-- Distinct actual row slabs are disjoint, including their endpoint rows. -/
theorem row_slab_unique {h : Cell m n → ℤ} {I J : Interval m}
    (hI : IsRowSlab h I) (hJ : IsRowSlab h J)
    (i : Fin m) (hi : I.Contains i) (hj : J.Contains i) : I = J := by
  have hfirst : I.first = J.first := le_antisymm (slab_first_le hI hJ i hi hj)
    (slab_first_le hJ hI i hj hi)
  have hlast_le : ∀ {A B : Interval m}, IsRowSlab h A → IsRowSlab h B →
      A.first = B.first → A.last ≤ B.last := by
    intro A B hA hB hf
    by_contra hnot
    have hlt : B.last.val < A.last.val := Nat.lt_of_not_ge hnot
    let k : Fin m := ⟨B.last.val + 1, by have := A.last.isLt; omega⟩
    have hkA : A.Contains k := by
      change A.first.val ≤ B.last.val + 1 ∧ B.last.val + 1 ≤ A.last.val
      have ho := B.ordered
      rw [← hf] at ho
      change A.first.val ≤ B.last.val at ho
      omega
    exact (hB.2.2 k rfl) (hA.1 k hkA)
  have hlast : I.last = J.last := le_antisymm (hlast_le hI hJ hfirst)
    (hlast_le hJ hI hfirst.symm)
  cases I
  cases J
  cases hfirst
  cases hlast
  rfl

/-- A proper coordinate interval has at least one actual outward cut. -/
def Proper (I : Interval m) : Prop := 0 < I.first.val ∨ I.last.val + 1 < m

noncomputable def minRowSlabs (h : Cell m n → ℤ) : Finset (Interval m) := by
  classical
  exact (rowSlabs h).filter (fun I => Proper I ∧ RowOutward h I 1)

noncomputable def maxRowSlabs (h : Cell m n → ℤ) : Finset (Interval m) := by
  classical
  exact (rowSlabs h).filter (fun I => Proper I ∧ RowOutward h I (-1))

noncomputable def neutralRowSlabs (h : Cell m n → ℤ) : Finset (Interval m) := by
  classical
  exact (rowSlabs h).filter (fun I => ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ EqualRowCuts h I s)

/-- Individual extrema are retained as cells, rather than projected graph edges. -/
noncomputable def extrema (h : Cell m n → ℤ) : Finset (Cell m n) := by
  classical
  exact Finset.univ.filter (fun v => IsStrictLocalMin h v ∨ IsStrictLocalMax h v)

noncomputable def rowIncidences (h : Cell m n → ℤ) (I : Interval m) : Finset (Cell m n) := by
  classical
  exact (extrema h).filter (fun v => I.Contains v.1)

private theorem minimum_not_maximum (hm : 2 ≤ m) (h : Cell m n → ℤ)
    (v : Cell m n) (hmin : IsStrictLocalMin h v) (hmax : IsStrictLocalMax h v) : False := by
  have hneigh : ∃ u : Cell m n, adj v u := by
    by_cases hi : v.1.val = 0
    · exact ⟨(⟨1, by omega⟩, v.2), by simp only [adj, gdist]; omega⟩
    · exact ⟨(⟨v.1.val - 1, by have := v.1.isLt; omega⟩, v.2), by
        simp only [adj, gdist]; omega⟩
  obtain ⟨u, hu⟩ := hneigh
  have := hmin u hu
  have := hmax u hu
  omega

/-- Every neutral actual row slab has two distinct individual incidences. -/
theorem neutral_row_degree {h : Cell m n → ℤ} (hh : IsHeight h) (hm : 2 ≤ m)
    (I : Interval m) (hI : I ∈ neutralRowSlabs h) :
    2 ≤ (rowIncidences h I).card := by
  classical
  obtain ⟨hslab, s, hs, hcuts⟩ := Finset.mem_filter.mp hI
  have hslab' : IsRowSlab h I := (Finset.mem_filter.mp hslab).2
  have hocc : ∃ i, I.Contains i ∧ RowOccupied h i :=
    ⟨I.first, ⟨le_rfl, I.ordered⟩, hslab'.1 I.first ⟨le_rfl, I.ordered⟩⟩
  obtain ⟨⟨u, hu, hmin⟩, ⟨v, hv, hmax⟩⟩ := neutral_row_has_both hh I s hs hcuts hocc
  have hne : u ≠ v := by
    intro he
    subst v
    exact minimum_not_maximum hm h u hmin hmax
  have hsub : {u, v} ⊆ rowIncidences h I := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp [rowIncidences, extrema, hu, hmin]
    · have he : w = v := Finset.mem_singleton.mp hw
      subst w
      simp [rowIncidences, extrema, hv, hmax]
  have hcard := Finset.card_le_card hsub
  simpa [hne] using hcard

/-- Two extrema in each actual neutral row slab give a cardinal lower bound.
Disjointness is proved from maximal occupied intervals, not assumed of a graph. -/
theorem neutral_rows_individual_count {h : Cell m n → ℤ} (hh : IsHeight h) (hm : 2 ≤ m) :
    2 * (neutralRowSlabs h).card ≤
      ((neutralRowSlabs h).biUnion (rowIncidences h)).card := by
  classical
  have hdisj : ((neutralRowSlabs h) : Set (Interval m)).PairwiseDisjoint (rowIncidences h) := by
    intro I hI J hJ hne
    apply Finset.disjoint_left.mpr
    intro v hvI hvJ
    have hsI : IsRowSlab h I := (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2
    have hsJ : IsRowSlab h J := (Finset.mem_filter.mp (Finset.mem_filter.mp hJ).1).2
    have he := row_slab_unique hsI hsJ v.1 (Finset.mem_filter.mp hvI).2
      (Finset.mem_filter.mp hvJ).2
    exact hne he
  rw [Finset.card_biUnion hdisj]
  calc
    2 * (neutralRowSlabs h).card = ∑ _I ∈ neutralRowSlabs h, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ I ∈ neutralRowSlabs h, (rowIncidences h I).card :=
      Finset.sum_le_sum fun I hI => neutral_row_degree hh hm I hI


/-- Transposition keeps the same actual height values and swaps the axes. -/
def transposeHeight (h : Cell m n → ℤ) : Cell n m → ℤ := fun v => h (v.2, v.1)

private theorem transpose_adj (v u : Cell m n) :
    adj ((v.2, v.1) : Cell n m) (u.2, u.1) ↔ adj v u := by
  simp only [adj, gdist]
  omega

/-- The original unit-edge law is preserved by transposition. -/
theorem transpose_isHeight {h : Cell m n → ℤ} (hh : IsHeight h) :
    IsHeight (transposeHeight h) := by
  intro v u hu
  exact hh _ _ ((transpose_adj v u).mpr hu)

noncomputable def neutralColSlabs (h : Cell m n → ℤ) : Finset (Interval n) :=
  neutralRowSlabs (transposeHeight h)

noncomputable def minColSlabs (h : Cell m n → ℤ) : Finset (Interval n) :=
  minRowSlabs (transposeHeight h)

noncomputable def maxColSlabs (h : Cell m n → ℤ) : Finset (Interval n) :=
  maxRowSlabs (transposeHeight h)

noncomputable def colIncidences (h : Cell m n → ℤ) (J : Interval n) : Finset (Cell m n) := by
  classical
  exact (extrema h).filter (fun v => J.Contains v.2)

private theorem transpose_min {h : Cell m n → ℤ} {v : Cell n m}
    (hv : IsStrictLocalMin (transposeHeight h) v) : IsStrictLocalMin h (v.2, v.1) := by
  intro u hu
  exact hv (u.2, u.1) ((transpose_adj v (u.2, u.1)).mp hu)

private theorem transpose_max {h : Cell m n → ℤ} {v : Cell n m}
    (hv : IsStrictLocalMax (transposeHeight h) v) : IsStrictLocalMax h (v.2, v.1) := by
  intro u hu
  exact hv (u.2, u.1) ((transpose_adj v (u.2, u.1)).mp hu)

/-- The transposed forcing argument counts distinct actual column incidences. -/
theorem neutral_col_degree {h : Cell m n → ℤ} (hh : IsHeight h) (hm : 2 ≤ m)
    (J : Interval n) (hJ : J ∈ neutralColSlabs h) :
    2 ≤ (colIncidences h J).card := by
  classical
  obtain ⟨hslab, s, hs, hcuts⟩ := Finset.mem_filter.mp hJ
  have hslab' : IsRowSlab (transposeHeight h) J := (Finset.mem_filter.mp hslab).2
  have hocc : ∃ i, J.Contains i ∧ RowOccupied (transposeHeight h) i :=
    ⟨J.first, ⟨le_rfl, J.ordered⟩, hslab'.1 J.first ⟨le_rfl, J.ordered⟩⟩
  obtain ⟨⟨u, hu, hmin⟩, ⟨v, hv, hmax⟩⟩ :=
    neutral_row_has_both (transpose_isHeight hh) J s hs hcuts hocc
  have hu' := transpose_min hmin
  have hv' := transpose_max hmax
  have hne : (u.2, u.1) ≠ (v.2, v.1) := by
    intro he
    rw [← he] at hv'
    exact minimum_not_maximum hm h _ hu' hv'
  have hsub : {(u.2, u.1), (v.2, v.1)} ⊆ colIncidences h J := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp [colIncidences, extrema, hu, hu']
    · have he : w = (v.2, v.1) := Finset.mem_singleton.mp hw
      subst w
      simp [colIncidences, extrema, hv, hv']
  have hcard := Finset.card_le_card hsub
  simpa [hne] using hcard

/-- Two extrema per neutral column slab, with parallel cells retained. -/
theorem neutral_cols_individual_count {h : Cell m n → ℤ} (hh : IsHeight h) (hm : 2 ≤ m) :
    2 * (neutralColSlabs h).card ≤
      ((neutralColSlabs h).biUnion (colIncidences h)).card := by
  classical
  have hdisj : ((neutralColSlabs h) : Set (Interval n)).PairwiseDisjoint (colIncidences h) := by
    intro I hI J hJ hne
    apply Finset.disjoint_left.mpr
    intro v hvI hvJ
    have hsI : IsRowSlab (transposeHeight h) I :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2
    have hsJ : IsRowSlab (transposeHeight h) J :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hJ).1).2
    exact hne (row_slab_unique hsI hsJ v.2 (Finset.mem_filter.mp hvI).2
      (Finset.mem_filter.mp hvJ).2)
  rw [Finset.card_biUnion hdisj]
  calc
    2 * (neutralColSlabs h).card = ∑ _J ∈ neutralColSlabs h, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ J ∈ neutralColSlabs h, (colIncidences h J).card :=
      Finset.sum_le_sum fun J hJ => neutral_col_degree hh hm J hJ

/-- An internal equal-slope interval cannot also have two equal nonzero
outward signs. This separates neutral and nonneutral incidence classes. -/
theorem neutral_not_outward {h : Cell m n → ℤ} (hn : 0 < n)
    (I : Interval m) (s t : ℤ) (ht : t ≠ 0) (hc : EqualRowCuts h I s) :
    ¬ RowOutward h I t := by
  obtain ⟨hi, hb, htop, hbottom⟩ := hc
  intro hout
  let j : Fin n := ⟨0, hn⟩
  let u : Cell m n := (⟨I.first.val - 1, by omega⟩, j)
  let v : Cell m n := (⟨I.last.val + 1, hb⟩, j)
  have hu : ¬ I.Contains u.1 := by
    change ¬ (I.first.val ≤ I.first.val - 1 ∧ I.first.val - 1 ≤ I.last.val)
    omega
  have hv : ¬ I.Contains v.1 := by
    change ¬ (I.first.val ≤ I.last.val + 1 ∧ I.last.val + 1 ≤ I.last.val)
    omega
  have ha := hout (I.first, j) u ⟨le_rfl, I.ordered⟩ hu (by
    simp only [adj, gdist, u]; omega)
  have hb' := hout (I.last, j) v ⟨I.ordered, le_rfl⟩ hv (by
    simp only [adj, gdist, v]; omega)
  have he1 := htop j
  have he2 := hbottom j
  dsimp [u, v] at ha hb'
  omega

/-- Every extremum belongs to the original exact minimum or maximum set. -/
theorem extrema_card_split (hm : 2 ≤ m) (h : Cell m n → ℤ) :
    (extrema h).card = (MiuraResidualCount.minima h).card + (MiuraResidualCount.maxima h).card := by
  classical
  have he : extrema h = MiuraResidualCount.minima h ∪ MiuraResidualCount.maxima h := by
    ext v
    simp [extrema, MiuraResidualCount.minima, MiuraResidualCount.maxima]
  have hd : Disjoint (MiuraResidualCount.minima h) (MiuraResidualCount.maxima h) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact minimum_not_maximum hm h v (by simpa [MiuraResidualCount.minima] using hv)
      (by simpa [MiuraResidualCount.maxima] using hw)
  rw [he, Finset.card_union_of_disjoint hd]

end D5.S3.Combinatorics.Geometry.MiuraSlabIncidence
