/- GID: D5/S3/Combinatorics/Partitions/RookAugmentedLevels
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/RookAugmentedLevels
   mirror-E: none(waiver:native-augmented-level-product)
   anchors: []
   utility: none
   digest: Actual Ferrers levels with auxiliary full columns have the level-total product count. -/

import D5.S3.Combinatorics.Partitions.RookLevelSelection

/-! A native combinatorial side of the level-total factorization. Auxiliary
    columns are distinguished from the original columns by a disjoint sum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Partitions.RookAugmentedLevels

open D5.S3.Combinatorics.Partitions.BarreseSourceNormalization
open D5.S3.Combinatorics.Partitions.RookLevelSelection
open scoped BigOperators

/-- Original source columns and t new full columns are disjoint. -/
abbrev Columns (b : PositiveColumns) (t : ℕ) := Fin b.val.length ⊕ Fin t

/-- Level p is counted from the top of N levels. An original cell retains its
    source column and within-level row; auxiliary columns contain all m rows. -/
def level (m N t : ℕ) (b : PositiveColumns) (p : Fin N) :
    Finset (Columns b t × Fin m) := by
  classical
  exact Finset.univ.filter fun x => Sum.elim
    (fun i : Fin b.val.length => m*(N-1-p.val)+x.2.val < b.val[i.val])
    (fun _ : Fin t => True) x.1

private theorem levels_nested (m N t : ℕ) (b : PositiveColumns) :
    NestedFull m (level m N t b) := by
  classical
  intro i j hij x hx r
  rcases x with ⟨c,s⟩
  cases c with
  | inr c => simp [level]
  | inl c =>
    have hx' : m*(N-1-i.val)+s.val < b.val[c.val] := by simpa [level] using hx
    have hq : N-1-j.val+1 ≤ N-1-i.val := by
      have hi := i.isLt
      have hj := j.isLt
      have hij' : i.val < j.val := hij
      omega
    have hmul := Nat.mul_le_mul_left m hq
    rw [Nat.mul_add, Nat.mul_one] at hmul
    have hr := r.isLt
    simp only [level, Finset.mem_filter, Finset.mem_univ, true_and, Sum.elim_inl]
    simp only [Nat.sub_sub] at hx' hmul ⊢
    omega

private theorem level_card (m N t : ℕ) (b : PositiveColumns) (p : Fin N) :
    (level m N t b p).card = columnLevel m b (N-1-p.val) + m*t := by
  classical
  unfold level columnLevel
  rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product,
    Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, ↓reduceIte]
  simp only [Fintype.card_subtype, Finset.card_filter]
  rw [Finset.sum_comm]
  simp [Nat.mul_comm]

/-- Count actual full placements on the augmented board by its level totals.
    This holds for arbitrary normalized original boards, with no singleton
    hypothesis. It is the product side of the native factorization route. -/
theorem augmented_selections_count (m N t : ℕ) (b : PositiveColumns) :
    Fintype.card (Selections m (level m N t b)) =
      ∏ i : Fin N, (columnLevel m b (N-1-i.val) + m*t - m*i.val) := by
  rw [selections_count m N _ (levels_nested m N t b)]
  exact Finset.prod_congr rfl (fun i _ => by rw [level_card])

end D5.S3.Combinatorics.Partitions.RookAugmentedLevels
