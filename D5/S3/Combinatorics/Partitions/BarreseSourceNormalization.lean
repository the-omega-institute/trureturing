/- GID: D5/S3/Combinatorics/Partitions/BarreseSourceNormalization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/BarreseSourceNormalization
   mirror-E: none(waiver:positive-column-normalization)
   anchors: []
   utility: none
   digest: Positive source column tuples give the entire normalized l-fiber without a width parameter. -/

import D5.S3.Combinatorics.Partitions.BarreseAllWidths

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Partitions.BarreseSourceNormalization
open D5.S3.Combinatorics.Partitions.FerrersLevelCounting
open D5.S3.Combinatorics.Partitions.BarreseAllWidths
open scoped BigOperators

/-- A normalized source board is its weakly increasing list of positive column heights. -/
abbrev PositiveColumns := {b : List ℕ // b.SortedLE ∧ ∀ x ∈ b, 0 < x}

/-- Horizontal reflection of transposed row notation gives source column notation. -/
def normalizedColumnsEquiv : YoungDiagram ≃ PositiveColumns where
  toFun μ := ⟨μ.transpose.rowLens.reverse, μ.transpose.rowLens_sorted.reverse,
    fun x hx => μ.transpose.pos_of_mem_rowLens x (List.mem_reverse.mp hx)⟩
  invFun b := (YoungDiagram.ofRowLens b.val.reverse b.property.1.reverse).transpose
  left_inv μ := by
    dsimp only
    simp only [List.reverse_reverse]
    change (YoungDiagram.ofRowLens μ.transpose.rowLens _).transpose = μ
    rw [YoungDiagram.ofRowLens_to_rowLens_eq_self, YoungDiagram.transpose_transpose]
  right_inv b := by
    apply Subtype.ext
    change ((YoungDiagram.ofRowLens b.val.reverse _).transpose.transpose.rowLens).reverse = b.val
    rw [YoungDiagram.transpose_transpose, YoungDiagram.rowLens_ofRowLens_eq_self]
    · exact List.reverse_reverse _
    · intro x hx
      exact b.property.2 x (List.mem_reverse.mp hx)

private theorem column_cell (b : PositiveColumns) (r : ℕ) (i : Fin b.val.length) :
    r < b.val[i.val] ↔ i.rev.val < (normalizedColumnsEquiv.symm b).rowLen r := by
  change r < b.val[i.val] ↔ i.rev.val <
    (YoungDiagram.ofRowLens b.val.reverse b.property.1.reverse).transpose.rowLen r
  rw [← YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_transpose,
    YoungDiagram.mem_ofRowLens]
  have hrev : b.val.reverse[i.rev.val]'(by simpa using i.rev.isLt) = b.val[i.val] := by
    rw [List.getElem_reverse]
    congr 1
    have hi := i.isLt
    simp only [Fin.val_rev]
    omega
  constructor
  · intro h
    refine ⟨by simpa using i.rev.isLt, ?_⟩
    change r < b.val.reverse[i.rev.val]
    simpa only [hrev] using h
  · rintro ⟨hi,h⟩
    change r < b.val.reverse[i.rev.val] at h
    simpa only [hrev] using h

private theorem columns_row_bound (b : PositiveColumns) (r : ℕ) :
    (normalizedColumnsEquiv.symm b).rowLen r ≤ b.val.length := by
  by_contra! h
  have hm := YoungDiagram.mem_iff_lt_rowLen.mpr h
  change (r,b.val.length) ∈
    (YoungDiagram.ofRowLens b.val.reverse b.property.1.reverse).transpose at hm
  rw [YoungDiagram.mem_transpose, YoungDiagram.mem_ofRowLens] at hm
  obtain ⟨hi,_⟩ := hm
  simpa using hi

private theorem columns_row_count (b : PositiveColumns) (r : ℕ) :
    Fintype.card {i : Fin b.val.length // r < b.val[i.val]} =
      (normalizedColumnsEquiv.symm b).rowLen r := by
  classical
  let w := (normalizedColumnsEquiv.symm b).rowLen r
  let e : {i : Fin b.val.length // r < b.val[i.val]} ≃ Fin w :=
    { toFun := fun i => ⟨i.val.rev.val, (column_cell b r i.val).mp i.property⟩
      invFun := fun k =>
        let i : Fin b.val.length := ⟨k.val, lt_of_lt_of_le k.isLt (columns_row_bound b r)⟩
        ⟨i.rev, (column_cell b r i.rev).mpr (by simpa only [Fin.rev_rev] using k.isLt)⟩
      left_inv := by intro i; apply Subtype.ext; exact Fin.rev_rev i.val
      right_inv := by intro k; apply Fin.ext; dsimp only; rw [Fin.rev_rev] }
  exact (Fintype.card_congr e).trans (Fintype.card_fin w)

/-- Direct cell counting on positive source column tuples, at any absolute level. -/
def columnLevel (m : ℕ) (b : PositiveColumns) (p : ℕ) : ℕ :=
  ∑ j : Fin m, Fintype.card {i : Fin b.val.length // m*p+j.val < b.val[i.val]}

private theorem columnLevel_shape (m : ℕ) (b : PositiveColumns) (p : ℕ) :
    columnLevel m b p = shapeLevel m (normalizedColumnsEquiv.symm b) p := by
  apply Finset.sum_congr rfl
  intro j _
  exact columns_row_count b _

/-- Exact nonempty-level tuple equality, with l(empty) defined to be the empty tuple. -/
abbrev LFiber (m : ℕ) (c : List ℕ) :=
  {b : PositiveColumns // (∀ x ∈ c, 0 < x) ∧
    ∀ p : ℕ, columnLevel m b p = c.reverse.getD p 0}

private def sourceShapeEquiv (m : ℕ) (c : List ℕ) (hc : ∀ x ∈ c, 0 < x) :
    LFiber m c ≃ ShapeFiber m c.reverse :=
  normalizedColumnsEquiv.symm.subtypeEquiv (fun b => by
    constructor
    · intro h p
      rw [← columnLevel_shape]
      exact h.2 p
    · intro h
      refine ⟨hc, ?_⟩
      intro p
      rw [columnLevel_shape]
      exact h p)

/-- The whole normalized 2015 l-fiber is evaluated for every positive m and every target tuple. -/
theorem source2015_count (m : ℕ) (hm : 0 < m) (c : List ℕ) :
    (Nat.card (LFiber m c) : ℤ) =
      if (∀ x ∈ c, 0 < x) then
        count (m-1) (c.reverse.getD 0 0) c.reverse
          ⟨c.reverse.getD 0 0, Nat.lt_succ_self _⟩ else 0 := by
  classical
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  split_ifs with hc
  · rw [Nat.card_congr (sourceShapeEquiv (r+1) c hc), all_width_count]
  · haveI : IsEmpty (LFiber (r+1) c) := ⟨fun b => hc b.property.1⟩
    simp

private theorem column_anti (m : ℕ) (b : PositiveColumns) : Antitone (columnLevel m b) := by
  intro p q hpq
  rw [columnLevel_shape, columnLevel_shape]
  apply Finset.sum_le_sum
  intro j _
  exact (normalizedColumnsEquiv.symm b).rowLen_anti _ _
    (Nat.add_le_add_right (Nat.mul_le_mul_left m hpq) j.val)

private theorem zero_exists (m : ℕ) (b : PositiveColumns) :
    ∃ p, columnLevel m b p = 0 := by
  by_cases hm : m = 0
  · subst m
    exact ⟨0, by simp [columnLevel]⟩
  let μ := normalizedColumnsEquiv.symm b
  refine ⟨μ.colLen 0, ?_⟩
  rw [columnLevel_shape]
  apply Finset.sum_eq_zero
  intro j _
  apply Nat.eq_zero_of_not_pos
  intro hz
  have hc : (m * μ.colLen 0 + j.val, 0) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hz
  have hh := YoungDiagram.mem_iff_lt_colLen.mp hc
  have hmul : μ.colLen 0 ≤ m * μ.colLen 0 := by
    simpa using Nat.mul_le_mul_right (μ.colLen 0) (show 1 ≤ m by omega)
  omega

private def firstZero (m : ℕ) (b : PositiveColumns) : ℕ := Nat.find (zero_exists m b)

/-- Reverse the nonempty bottom-up levels, stopping at the first empty level.
    The empty board has the empty tuple. -/
def lOperator (m : ℕ) (b : PositiveColumns) : List ℕ :=
  (List.ofFn (fun p : Fin (firstZero m b) => columnLevel m b p.val)).reverse

private theorem operator_spec (m : ℕ) (b : PositiveColumns) :
    (∀ x ∈ lOperator m b, 0 < x) ∧
    ∀ p, columnLevel m b p = (lOperator m b).reverse.getD p 0 := by
  constructor
  · intro x hx
    obtain ⟨p,rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hx)
    apply Nat.pos_of_ne_zero
    exact Nat.find_min (zero_exists m b) p.isLt
  · intro p
    simp only [lOperator, List.reverse_reverse]
    by_cases hp : p < firstZero m b
    · rw [List.getD_eq_getElem _ _ (by simpa using hp), List.getElem_ofFn]
    · rw [List.getD_eq_default _ _ (by simpa using (show firstZero m b ≤ p by omega))]
      have hz : columnLevel m b (firstZero m b) = 0 := Nat.find_spec (zero_exists m b)
      have hh := column_anti m b (show firstZero m b ≤ p by omega)
      omega

private theorem positive_data_unique (a b : List ℕ)
    (ha : ∀ x ∈ a, 0 < x) (hb : ∀ x ∈ b, 0 < x)
    (h : ∀ p, a.getD p 0 = b.getD p 0) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys =>
      have hy := hb y (by simp)
      have hh := h 0
      simp at hh
      omega
  | cons x xs ih =>
    cases b with
    | nil =>
      have hx := ha x (by simp)
      have hh := h 0
      simp at hh
      omega
    | cons y ys =>
      have hxy : x = y := by simpa using h 0
      subst y
      congr 1
      apply ih ys
      · intro z hz
        exact ha z (by simp [hz])
      · intro z hz
        exact hb z (by simp [hz])
      · intro p
        simpa using h (p+1)

private theorem operator_iff (m : ℕ) (b : PositiveColumns) (c : List ℕ) :
    lOperator m b = c ↔ (∀ x ∈ c, 0 < x) ∧
      ∀ p, columnLevel m b p = c.reverse.getD p 0 := by
  constructor
  · rintro rfl
    exact operator_spec m b
  · rintro ⟨hc,h⟩
    have hs := operator_spec m b
    have he : (lOperator m b).reverse = c.reverse := positive_data_unique _ _
      (fun x hx => hs.1 x (List.mem_reverse.mp hx))
      (fun x hx => hc x (List.mem_reverse.mp hx))
      (fun p => (hs.2 p).symm.trans (h p))
    exact List.reverse_injective he

/-- The native operator equality and the absolute-level cell specification are equivalent fibers. -/
def operatorFiberEquiv (m : ℕ) (c : List ℕ) :
    {b : PositiveColumns // lOperator m b = c} ≃ LFiber m c :=
  Equiv.subtypeEquivRight (fun b => operator_iff m b c)

/-- Complete all-width evaluation of the native l-operator fiber. -/
theorem lOperator_count (m : ℕ) (hm : 0 < m) (c : List ℕ) :
    (Nat.card {b : PositiveColumns // lOperator m b = c} : ℤ) =
      if (∀ x ∈ c, 0 < x) then
        count (m-1) (c.reverse.getD 0 0) c.reverse
          ⟨c.reverse.getD 0 0, Nat.lt_succ_self _⟩ else 0 := by
  rw [Nat.card_congr (operatorFiberEquiv m c)]
  exact source2015_count m hm c


end D5.S3.Combinatorics.Partitions.BarreseSourceNormalization
