/- GID: D5/S1/Words/Compositions/FirstSumsPartitionCharacterization
   generality: G
   mirror-B: D5/B/S1/Words/Compositions/FirstSumsPartitionCharacterization
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Decreasing partitions are first sums exactly when every part is at least four. -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# First sums of decreasing partitions

Wiseman's OEIS A391620 conjecture is read with the partition parts in weakly
decreasing order. The private construction starts at the right endpoint with
2 and prepends `a - u`, where `u` is the previously constructed first part.
Its invariant `2 ≤ u ≤ b - 2`, together with `b ≤ a`, preserves the lower
bound and the adjacent sum. These are unbounded symbolic results; no finite
enumeration or certified numerical instance is included.
-/

namespace D5.S1.Words.Compositions.FirstSumsPartitionCharacterization

/-- Adjacent ("first") sums of a list: `(a+b, b+c, ...)`. -/
def firstSums (x : List ℕ) : List ℕ := List.zipWith (· + ·) x x.tail

/-- The first sums of some list whose parts are all at least two. -/
def IsFirstSums (q : List ℕ) : Prop :=
  ∃ x : List ℕ, (∀ y ∈ x, 2 ≤ y) ∧ firstSums x = q

/-- A first-sums list has one fewer entry, with natural subtraction. -/
theorem firstSums_length (x : List ℕ) : (firstSums x).length = x.length - 1 := by
  simp [firstSums]

private theorem firstSums_cons_cons (a b : ℕ) (x : List ℕ) :
    firstSums (a :: b :: x) = (a + b) :: firstSums (b :: x) := rfl

private theorem firstSums_lower_bound (x : List ℕ) (hx : ∀ y ∈ x, 2 ≤ y) :
    ∀ y ∈ firstSums x, 4 ≤ y := by
  induction x with
  | nil => simp [firstSums]
  | cons a x ih =>
    cases x with
    | nil => simp [firstSums]
    | cons b x =>
      have ha := hx a (by simp)
      have hb := hx b (by simp)
      rw [firstSums_cons_cons]
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · exact ih (fun z hz => hx z (List.mem_cons_of_mem a hz)) y hy

/-- Every part of a first-sums list is at least four. -/
theorem min_ge_four_of_isFirstSums {q : List ℕ} (h : IsFirstSums q) :
    ∀ y ∈ q, 4 ≤ y := by
  have hx := Classical.choose_spec h
  rw [← hx.2]
  exact firstSums_lower_bound (Classical.choose h) hx.1

-- Keeping the first reconstructed part bounded lets the next larger part be prepended.
private theorem reconstruct (a : ℕ) (q : List ℕ)
    (hs : (a :: q).Pairwise (· ≥ ·)) (h4 : ∀ y ∈ a :: q, 4 ≤ y) :
    ∃ u : ℕ, ∃ x : List ℕ, (∀ y ∈ u :: x, 2 ≤ y) ∧
      firstSums (u :: x) = a :: q ∧ u ≤ a - 2 := by
  induction q generalizing a with
  | nil =>
    have ha := h4 a (by simp)
    refine ⟨a - 2, [2], ?_, ?_, le_rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      intro y hy
      rcases hy with rfl | rfl <;> omega
    · simp [firstSums, Nat.sub_add_cancel (by omega : 2 ≤ a)]
  | cons b q ih =>
    obtain ⟨u, x, hx, hsum, hu⟩ :=
      ih b hs.of_cons (fun y hy => h4 y (List.mem_cons_of_mem a hy))
    have hab : b ≤ a := (List.pairwise_cons.mp hs).1 b (by simp)
    have hb := h4 b (by simp)
    have hu2 := hx u (by simp)
    refine ⟨a - u, u :: x, ?_, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · exact hx y hy
    · rw [firstSums_cons_cons, hsum, Nat.sub_add_cancel (by omega : u ≤ a)]
    · omega

/-- Backward reconstruction realizes every nonempty decreasing list with parts at least four. -/
theorem isFirstSums_of_sorted_min_ge_four {q : List ℕ} (hq : q ≠ [])
    (hs : q.Pairwise (· ≥ ·)) (h4 : ∀ y ∈ q, 4 ≤ y) : IsFirstSums q := by
  cases q with
  | nil => exact False.elim (hq rfl)
  | cons a q =>
    obtain ⟨x, hx, hsum, _⟩ := Classical.choose_spec (reconstruct a q hs h4)
    exact ⟨Classical.choose (reconstruct a q hs h4) :: x, hx, hsum⟩

/-- Wiseman's conjecture in the ordered-part reading; positivity is not needed. -/
theorem wiseman_conjecture {q : List ℕ} (hq : q ≠ [])
    (hs : q.Pairwise (· ≥ ·)) : ¬ IsFirstSums q ↔ ∃ y ∈ q, y < 4 := by
  constructor
  · intro h
    by_contra hn
    apply h (isFirstSums_of_sorted_min_ge_four hq hs ?_)
    intro y hy
    by_contra h4
    exact hn ⟨y, hy, by omega⟩
  · rintro ⟨y, hy, h4⟩ h
    have := min_ge_four_of_isFirstSums h y hy
    omega

private theorem characterization_including_empty {q : List ℕ}
    (hs : q.Pairwise (· ≥ ·)) : ¬ IsFirstSums q ↔ ∃ y ∈ q, y < 4 := by
  by_cases hq : q = []
  · subst q
    have h : IsFirstSums [] := ⟨[2], by simp, rfl⟩
    simp [h]
  · exact wiseman_conjecture hq hs

open scoped Classical in
/-- The two predicates select equally many Mathlib partitions, also for `n = 0`. -/
theorem card_not_firstSums_eq (n : ℕ) :
    ((Finset.univ : Finset (Nat.Partition n)).filter
      (fun p => ¬ IsFirstSums (p.parts.sort (· ≥ ·)))).card =
    ((Finset.univ : Finset (Nat.Partition n)).filter
      (fun p => ∃ y ∈ p.parts, y < 4)).card := by
  congr 1
  apply Finset.filter_congr
  intro p _
  simpa only [Multiset.mem_sort] using
    characterization_including_empty (Multiset.pairwise_sort p.parts (· ≥ ·))

#print axioms firstSums_length
#print axioms min_ge_four_of_isFirstSums
#print axioms isFirstSums_of_sorted_min_ge_four
#print axioms wiseman_conjecture
#print axioms card_not_firstSums_eq

end D5.S1.Words.Compositions.FirstSumsPartitionCharacterization
