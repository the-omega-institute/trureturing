/- GID: D5/S3/Combinatorics/Geometry/MiuraEqualityCrossed
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraEqualityCrossed
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: Both actual crossed equality patterns have exactly four extrema. -/
module
public import D5.S3.Combinatorics.Geometry.MiuraEqualityNeutral
public import D5.S3.Combinatorics.Geometry.MiuraEqualityOrder
import all D5.S3.Combinatorics.Geometry.MiuraEqualityNeutral
import all D5.S3.Combinatorics.Geometry.MiuraSlabSigns

/-! The exceptional crossed pattern is proved on the original actual grid. -/
@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraEqualityCrossed
open MiuraHeightEnvelope MiuraSlabExtrema MiuraSlabNeutral MiuraSlabIncidence
open MiuraSlabRunBound MiuraSlabSigns MiuraEqualityNeutral MiuraEqualityOrder
variable {m n : ℕ}

private theorem crossed_first_four {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hr : ∃ i, ¬ RowOccupied h i) (hc : ∃ j, ¬ RowOccupied (transposeHeight h) j)
    (heq : (extrema h).card = (frozenRowRunStarts h).card +
      (frozenRowRunStarts (transposeHeight h)).card)
    (hRmin : (minRowSlabs h).card = 1) (hRmax : (maxRowSlabs h).card = 2)
    (hCmin : (minColSlabs h).card = 2) (hCmax : (maxColSlabs h).card = 1) :
    (extrema h).card = 4 := by
  obtain ⟨I, hI, J, hJ, ht, hb⟩ := boundary_maximum_slabs hh hm (by omega) hr hRmin (by omega)
  obtain ⟨hr0, hc0⟩ := equality_crossed_no_neutral hh hm hn hr hc heq hRmin hCmax I J hI hJ ht hb
  have he := run_equality_charge hh hm hn hr hc heq
  rw [hr0, hc0, hRmin, hRmax, hCmin, hCmax] at he
  norm_num at he
  exact he

private theorem neg_min_iff (h : Cell m n → ℤ) (v : Cell m n) :
    IsStrictLocalMin (fun u => -h u) v ↔ IsStrictLocalMax h v := by
  constructor <;> intro hx u hu <;> have he := hx u hu <;> dsimp at he ⊢ <;> omega

private theorem neg_max_iff (h : Cell m n → ℤ) (v : Cell m n) :
    IsStrictLocalMax (fun u => -h u) v ↔ IsStrictLocalMin h v := by
  constructor <;> intro hx u hu <;> have he := hx u hu <;> dsimp at he ⊢ <;> omega

private theorem neg_outward (h : Cell m n → ℤ) (I : Interval m) (t : ℤ) :
    RowOutward (fun u => -h u) I t ↔ RowOutward h I (-t) := by
  constructor <;> intro hx v u hv hu ha <;> have he := hx v u hv hu ha <;>
    dsimp at he ⊢ <;> omega

private theorem neg_min_slabs (h : Cell m n → ℤ) :
    minRowSlabs (fun u => -h u) = maxRowSlabs h := by
  classical
  ext I
  simp only [minRowSlabs, maxRowSlabs, rowSlabs, Finset.mem_filter, Finset.mem_univ,
    true_and, IsRowSlab, neg_occupied, neg_outward]

private theorem neg_max_slabs (h : Cell m n → ℤ) :
    maxRowSlabs (fun u => -h u) = minRowSlabs h := by
  classical
  ext I
  simp only [minRowSlabs, maxRowSlabs, rowSlabs, Finset.mem_filter, Finset.mem_univ,
    true_and, IsRowSlab, neg_occupied, neg_outward, neg_neg]

private theorem neg_runs (h : Cell m n → ℤ) :
    frozenRowRunStarts (fun u => -h u) = frozenRowRunStarts h := by
  classical
  ext i
  simp only [frozenRowRunStarts, Finset.mem_filter, FrozenRowRunStart, neg_occupied]

private theorem neg_extrema (h : Cell m n → ℤ) :
    extrema (fun u => -h u) = extrema h := by
  classical
  ext v
  simp only [extrema, Finset.mem_filter, neg_min_iff, neg_max_iff, or_comm]

/-- Equality in the actual run bound has exactly four individual extrema in
either crossed nonneutral count pattern. Both signs retain physical sides. -/
theorem crossed_equality_four {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hr : ∃ i, ¬ RowOccupied h i) (hc : ∃ j, ¬ RowOccupied (transposeHeight h) j)
    (heq : (extrema h).card = (frozenRowRunStarts h).card +
      (frozenRowRunStarts (transposeHeight h)).card)
    (hpattern :
      ((minRowSlabs h).card = 1 ∧ (maxRowSlabs h).card = 2 ∧
        (minColSlabs h).card = 2 ∧ (maxColSlabs h).card = 1) ∨
      ((minRowSlabs h).card = 2 ∧ (maxRowSlabs h).card = 1 ∧
        (minColSlabs h).card = 1 ∧ (maxColSlabs h).card = 2)) :
    (extrema h).card = 4 := by
  rcases hpattern with ⟨hrm, hrM, hcm, hcM⟩ | ⟨hrm, hrM, hcm, hcM⟩
  · exact crossed_first_four hh hm hn hr hc heq hrm hrM hcm hcM
  · let g : Cell m n → ℤ := fun u => -h u
    have hg : IsHeight g := neg_height hh
    have hrg : ∃ i, ¬ RowOccupied g i := by
      obtain ⟨i, hi⟩ := hr
      exact ⟨i, fun h => hi ((neg_occupied _ i).mp h)⟩
    have hcg : ∃ j, ¬ RowOccupied (transposeHeight g) j := by
      obtain ⟨j, hj⟩ := hc
      exact ⟨j, fun h => hj ((neg_occupied _ j).mp h)⟩
    have he : (extrema g).card = (frozenRowRunStarts g).card +
        (frozenRowRunStarts (transposeHeight g)).card := by
      change (extrema (fun u => -h u)).card =
        (frozenRowRunStarts (fun u => -h u)).card +
        (frozenRowRunStarts (fun u => -(transposeHeight h) u)).card
      rw [neg_extrema, neg_runs, neg_runs]
      exact heq
    have hrmg : (minRowSlabs g).card = 1 := by simpa only [g, neg_min_slabs] using hrM
    have hrMg : (maxRowSlabs g).card = 2 := by simpa only [g, neg_max_slabs] using hrm
    have hcmg : (minColSlabs g).card = 2 := by
      change (minRowSlabs (fun u => -(transposeHeight h) u)).card = 2
      rw [neg_min_slabs]
      exact hcM
    have hcMg : (maxColSlabs g).card = 1 := by
      change (maxRowSlabs (fun u => -(transposeHeight h) u)).card = 1
      rw [neg_max_slabs]
      exact hcm
    have he4 := crossed_first_four hg hm hn hrg hcg he hrmg hrMg hcmg hcMg
    simpa only [g, neg_extrema] using he4
/-- Actual run equality reduces to an axis with one slab of each nonneutral
type or to the four-extremum exception. -/
theorem equality_two_slabs_or_four {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hr : ∃ i, ¬ RowOccupied h i) (hc : ∃ j, ¬ RowOccupied (transposeHeight h) j)
    (heq : (extrema h).card = (frozenRowRunStarts h).card +
      (frozenRowRunStarts (transposeHeight h)).card) :
    ((minRowSlabs h).card = 1 ∧ (maxRowSlabs h).card = 1) ∨
    ((minColSlabs h).card = 1 ∧ (maxColSlabs h).card = 1) ∨
    (extrema h).card = 4 := by
  have hrmin : 1 ≤ (minRowSlabs h).card :=
    (minimum_row_slab_exists hh hm (by omega) hr).card_pos
  have hrmax : 1 ≤ (maxRowSlabs h).card :=
    (maximum_row_slab_exists hh hm (by omega) hr).card_pos
  have hcmin : 1 ≤ (minColSlabs h).card :=
    (minimum_row_slab_exists (transpose_isHeight hh) hn (by omega) hc).card_pos
  have hcmax : 1 ≤ (maxColSlabs h).card :=
    (maximum_row_slab_exists (transpose_isHeight hh) hn (by omega) hc).card_pos
  obtain ⟨_, _, hpmin, hpmax⟩ := frozen_run_equality_incidence hh hm hn hr hc heq
  have hmin : (minRowSlabs h).card = 1 ∨ (minColSlabs h).card = 1 := by
    rcases Nat.mul_eq_zero.mp hpmin with he | he <;> omega
  have hmax : (maxRowSlabs h).card = 1 ∨ (maxColSlabs h).card = 1 := by
    rcases Nat.mul_eq_zero.mp hpmax with he | he <;> omega
  have hrowMinBound (he : (maxRowSlabs h).card = 1) : (minRowSlabs h).card ≤ 2 := by
    have hg := one_minimum_slab_maximum_card_le_two (neg_height hh) hm (by omega)
      (by rw [neg_min_slabs]; exact he)
    rwa [neg_max_slabs] at hg
  have hcolMinBound (he : (maxColSlabs h).card = 1) : (minColSlabs h).card ≤ 2 := by
    have hg := one_minimum_slab_maximum_card_le_two (neg_height (transpose_isHeight hh)) hn (by omega)
      (by rw [neg_min_slabs]; exact he)
    rwa [neg_max_slabs] at hg
  rcases hmin with hrm | hcm <;> rcases hmax with hrM | hcM
  · exact Or.inl ⟨hrm, hrM⟩
  · by_cases hrM : (maxRowSlabs h).card = 1
    · exact Or.inl ⟨hrm, hrM⟩
    by_cases hcm : (minColSlabs h).card = 1
    · exact Or.inr (Or.inl ⟨hcm, hcM⟩)
    have hrB := one_minimum_slab_maximum_card_le_two hh hm (by omega) hrm
    have hcB := hcolMinBound hcM
    exact Or.inr (Or.inr (crossed_equality_four hh hm hn hr hc heq
      (Or.inl ⟨hrm, by omega, by omega, hcM⟩)))
  · by_cases hrm : (minRowSlabs h).card = 1
    · exact Or.inl ⟨hrm, hrM⟩
    by_cases hcM : (maxColSlabs h).card = 1
    · exact Or.inr (Or.inl ⟨hcm, hcM⟩)
    have hrB := hrowMinBound hrM
    have hcB := one_minimum_slab_maximum_card_le_two (transpose_isHeight hh) hn (by omega) hcm
    change (maxColSlabs h).card ≤ 2 at hcB
    exact Or.inr (Or.inr (crossed_equality_four hh hm hn hr hc heq
      (Or.inr ⟨by omega, hrM, hcm, by omega⟩)))
  · exact Or.inr (Or.inl ⟨hcm, hcM⟩)

end D5.S3.Combinatorics.Geometry.MiuraEqualityCrossed
