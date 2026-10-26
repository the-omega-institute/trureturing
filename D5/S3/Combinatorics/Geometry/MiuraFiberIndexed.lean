/- GID: D5/S3/Combinatorics/Geometry/MiuraFiberIndexed
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraFiberIndexed
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Simultaneous indexed frozen-line insertions transport every individual extremum. -/

module
public import D5.S3.Combinatorics.Geometry.MiuraCoreStretch
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Indexed insertions into the actual array, with exact extremum positions. -/
@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraFiberIndexed
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreColumns MiuraCoreContract
  MiuraCoreCellExpand MiuraCoreExtremum MiuraCoreResidual MiuraCoreReduction
  MiuraCoreRestore MiuraCoreStretch MiuraCoreFrozenSlope MiuraSlabIncidence
open scoped BigOperators
variable {m n : ℕ}

/-- Extra copies at and before an original line shift its last surviving copy. -/
def columnPosition (w : Fin n → ℕ) (j : Fin n) : ℕ :=
  j.val + ∑ k ∈ Finset.univ.filter (fun k : Fin n => k ≤ j), w k

private theorem position_lt (w : Fin n → ℕ) (j : Fin n) :
    columnPosition w j < n + ∑ k, w k := by
  have hs : (∑ k ∈ Finset.univ.filter (fun k : Fin n => k ≤ j), w k) ≤ ∑ k, w k :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have := j.isLt
  unfold columnPosition
  omega

private theorem position_strict (w : Fin n → ℕ) : StrictMono (columnPosition w) := by
  intro j k hjk
  have hs : (∑ l ∈ Finset.univ.filter (fun l : Fin n => l ≤ j), w l) ≤
      ∑ l ∈ Finset.univ.filter (fun l : Fin n => l ≤ k), w l := by
    apply Finset.sum_le_sum_of_subset
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      le_trans (Finset.mem_filter.mp hl).2 (le_of_lt hjk)⟩
  have hv : j.val < k.val := hjk
  unfold columnPosition
  omega

private theorem increment_position (w v : Fin n → ℕ) (j k : Fin n)
    (hw : ∀ l, w l = v l + if l = j then 1 else 0) :
    columnPosition w k = columnPosition v k + if j ≤ k then 1 else 0 := by
  classical
  simp only [columnPosition, hw, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq']
  split_ifs <;> omega

private theorem increment_total (w v : Fin n → ℕ) (j : Fin n)
    (hw : ∀ l, w l = v l + if l = j then 1 else 0) :
    (∑ l, w l) = (∑ l, v l) + 1 := by
  classical
  simp only [hw, Finset.sum_add_distrib]
  simp

/-- Every extremum retains its original row and cumulative column coordinate. -/
def ColumnExtremaExpansion {N : ℕ} (h : Cell m n → ℤ) (w : Fin n → ℕ)
    (g : Cell m N → ℤ) : Prop :=
  (∀ q, IsStrictLocalMin g q ↔ ∃ p, IsStrictLocalMin h p ∧
    q.1 = p.1 ∧ q.2.val = columnPosition w p.2) ∧
  (∀ q, IsStrictLocalMax g q ↔ ∃ p, IsStrictLocalMax h p ∧
    q.1 = p.1 ∧ q.2.val = columnPosition w p.2)

private theorem expansion_active {N : ℕ} {h : Cell m n → ℤ} {w : Fin n → ℕ}
    {g : Cell m N → ℤ} (he : ColumnExtremaExpansion h w g) (k : Fin N) :
    activeColumn g k ↔ ∃ j, activeColumn h j ∧ k.val = columnPosition w j := by
  constructor
  · rintro ⟨i, hi | hi⟩
    · obtain ⟨p, hp, _, hq⟩ := (he.2 (i,k)).mp hi
      exact ⟨p.2, ⟨p.1, Or.inl hp⟩, hq⟩
    · obtain ⟨p, hp, _, hq⟩ := (he.1 (i,k)).mp hi
      exact ⟨p.2, ⟨p.1, Or.inr hp⟩, hq⟩
  · rintro ⟨j, ⟨i, hi | hi⟩, hpos⟩
    · exact ⟨i, Or.inl ((he.2 _).mpr ⟨(i,j), hi, rfl, hpos⟩)⟩
    · exact ⟨i, Or.inr ((he.1 _).mpr ⟨(i,j), hi, rfl, hpos⟩)⟩

private theorem expansion_frozen {N : ℕ} {h : Cell m n → ℤ} {w : Fin n → ℕ}
    {g : Cell m N → ℤ} (he : ColumnExtremaExpansion h w g)
    (hN : N = n + ∑ k, w k) (hg : IsHeight g) (hm : 0 < m)
    (j : Fin n) (hj : frozenColumn h j) :
    ∃ k : Fin N, frozenColumn g k ∧ k.val = columnPosition w j := by
  have hleft : 0 < columnPosition w j := by
    have := hj.1
    dsimp [columnPosition]
    omega
  have hright : columnPosition w j + 1 < N := by
    have hs : (∑ k ∈ Finset.univ.filter (fun k : Fin n => k ≤ j), w k) ≤ ∑ k, w k :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have := hj.2.1
    dsimp [columnPosition]
    omega
  let k : Fin N := ⟨columnPosition w j, by omega⟩
  refine ⟨k, ?_, rfl⟩
  apply (frozenColumn_iff_inactive g hg k hleft hright hm).mpr
  intro hactive
  obtain ⟨l, hl, heq⟩ := (expansion_active he _).mp hactive
  have hjl : j = l := (position_strict w).injective heq
  exact frozenColumn_not_active h j hj (hjl.symm ▸ hl)

private theorem insertion_extrema (g : Cell m N → ℤ) (hg : IsHeight g)
    (hm : 0 < m) (j : Fin N) (hj : frozenColumn g j) :
    let f := stretchColumn g hm j hj
    let j' : Fin (N+1) := ⟨j.val, by have := j.isLt; omega⟩
    (∀ q, IsStrictLocalMin f q ↔ ∃ p, IsStrictLocalMin g p ∧
      q = cellExpand j' p hj.1 (by simp only [Fin.val_mk]; have := hj.2.1; omega)) ∧
    (∀ q, IsStrictLocalMax f q ↔ ∃ p, IsStrictLocalMax g p ∧
      q = cellExpand j' p hj.1 (by simp only [Fin.val_mk]; have := hj.2.1; omega)) := by
  dsimp only
  let f := stretchColumn g hm j hj
  let j' : Fin (N+1) := ⟨j.val, by have := j.isLt; omega⟩
  have hs : SeamSlope g j' hj.1 (by simp only [Fin.val_mk]; have := hj.2.1; omega) (frozenSlope g hm j hj) := by
    intro i
    exact frozenSlope_eq g hg hm j hj i
  have hf : IsHeight f := restoreColumn_isHeight (n := N + 1) g hg j' hj.1 _ _
    (frozenSlope_pm g hg hm j hj)
  have hfr : frozenColumn f j' := restoreColumn_frozen (n := N + 1) g j' hj.1 _ _ hs
  have hc : contractAt f hm j' hfr = g := contractAt_restoreColumn (n := N + 1) g hm j' hj.1 _ _ hs
  constructor
  · intro q
    constructor
    · intro hq
      have hnq : q.2 ≠ j' := by
        intro e
        exact frozenColumn_no_extremum f j' hfr q.1 (by have hx : q = (q.1, j') := Prod.ext rfl e; exact hx ▸ Or.inr hq)
      obtain ⟨p, hp⟩ := cellExpand_surjOn j' hfr.1 hfr.2.1 q hnq
      refine ⟨p, ?_, hp.symm⟩
      rw [← hc]
      exact contractAt_isSLm_of_h_min f hf hm j' hfr p (hp.symm ▸ hq)
    · rintro ⟨p, hp, rfl⟩
      exact h_min_of_contractAt_isSLm f hf hm j' hfr p (hc.symm ▸ hp)
  · intro q
    constructor
    · intro hq
      have hnq : q.2 ≠ j' := by
        intro e
        exact frozenColumn_no_extremum f j' hfr q.1 (by have hx : q = (q.1, j') := Prod.ext rfl e; exact hx ▸ Or.inl hq)
      obtain ⟨p, hp⟩ := cellExpand_surjOn j' hfr.1 hfr.2.1 q hnq
      refine ⟨p, ?_, hp.symm⟩
      rw [← hc]
      exact contractAt_isSLM_of_h_max f hf hm j' hfr p (hp.symm ▸ hq)
    · rintro ⟨p, hp, rfl⟩
      exact h_max_of_contractAt_isSLM f hf hm j' hfr p (hc.symm ▸ hp)

end D5.S3.Combinatorics.Geometry.MiuraFiberIndexed
