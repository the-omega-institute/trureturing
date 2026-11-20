/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CubeClosedNeighborhoodRecurrence
   generality: G
   mirror-B: none(waiver:isolated-verification)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: A coordinate split gives a closed-neighborhood recurrence and a seven-cube table. -/

import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi

/-! Splitting off the first coordinate bounds the closed neighborhood in terms of
the two projected halves. The exact recurrence through dimension seven gives a
bound on the closed neighborhood of a folded parity side in dimension eight. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CubeClosedNeighborhoodRecurrence

open Finset

/-- The cube vertices at distance at most one from the support. -/
def closedNeighborhood {n : ℕ} (S : Finset (Fin n → Bool)) : Finset (Fin n → Bool) :=
  univ.filter fun x => ∃ y ∈ S, hammingDist x y ≤ 1

/-- The support in the half with first bit `c`, with that bit removed. -/
def half {n : ℕ} (c : Bool) (S : Finset (Fin (n + 1) → Bool)) : Finset (Fin n → Bool) :=
  univ.filter fun x => Fin.cons c x ∈ S

private theorem mem_half {n : ℕ} {c : Bool} {S : Finset (Fin (n + 1) → Bool)}
    {x : Fin n → Bool} : x ∈ half c S ↔ Fin.cons c x ∈ S := by
  simp [half]

private theorem mem_closedNeighborhood {n : ℕ} {S : Finset (Fin n → Bool)}
    {x : Fin n → Bool} : x ∈ closedNeighborhood S ↔ ∃ y ∈ S, hammingDist x y ≤ 1 := by
  simp [closedNeighborhood]

private theorem hamming_cons {n : ℕ} (c d : Bool) (x y : Fin n → Bool) :
    hammingDist (Fin.cons (α := fun _ => Bool) c x) (Fin.cons d y) =
      (if c = d then 0 else 1) + hammingDist x y := by
  unfold hammingDist
  rw [Fin.card_filter_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  by_cases h : c = d <;> simp [h, Nat.add_comm]

private theorem card_halves {n : ℕ} (S : Finset (Fin (n + 1) → Bool)) :
    S.card = (half false S).card + (half true S).card := by
  have card_half (c : Bool) :
      (S.filter fun x => x 0 = c).card = (half c S).card := by
    let lift : (Fin n → Bool) ↪ (Fin (n + 1) → Bool) :=
      ⟨Fin.cons (α := fun _ => Bool) c, Fin.cons_right_injective (α := fun _ => Bool) c⟩
    have hmap : (half c S).map lift = S.filter (fun x => x 0 = c) := by
      ext x
      simp only [mem_map, mem_half, mem_filter]
      change (∃ y, Fin.cons c y ∈ S ∧ Fin.cons c y = x) ↔ x ∈ S ∧ x 0 = c
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨hy, Fin.cons_zero _ _⟩
      · rintro ⟨hx, hc⟩
        have he : Fin.cons c (Fin.tail x) = x := by rw [← hc, Fin.cons_self_tail]
        exact ⟨Fin.tail x, he.symm ▸ hx, he⟩
    rw [← hmap, card_map]
  rw [← card_half false, ← card_half true]
  simpa only [Bool.not_eq_false] using
    (Finset.card_filter_add_card_filter_not (s := S) (fun x => x 0 = false)).symm

private theorem half_closedNeighborhood {n : ℕ} (c : Bool) (S : Finset (Fin (n + 1) → Bool)) :
    half c (closedNeighborhood S) = closedNeighborhood (half c S) ∪ half (!c) S := by
  ext x
  simp only [mem_union, mem_half, mem_closedNeighborhood]
  constructor
  · rintro ⟨y, hy, hd⟩
    rw [← Fin.cons_self_tail y, hamming_cons] at hd
    by_cases hc : c = y 0
    · left
      refine ⟨Fin.tail y, ?_, by simpa [hc] using hd⟩
      simpa only [hc, Fin.cons_self_tail] using hy
    · right
      have hyc : (!c) = y 0 := by
        cases c <;> cases hb : y 0 <;> simp_all
      have hdist : hammingDist x (Fin.tail y) = 0 := by
        simp only [ite_eq_right hc] at hd
        omega
      have he := hammingDist_eq_zero.mp hdist
      rw [he, hyc, Fin.cons_self_tail]
      exact hy
  · rintro (⟨y, hy, hd⟩ | hx)
    · exact ⟨Fin.cons c y, hy, by simpa [hamming_cons] using hd⟩
    · exact ⟨Fin.cons (!c) x, hx, by cases c <;> simp [hamming_cons]⟩

private def splitCost (h : ℕ → ℕ) (a b : ℕ) : ℕ :=
  max (h a) b + max (h b) a

private def splitSizes (capacity s : ℕ) : List ℕ :=
  (List.range (min capacity s + 1)).filter fun a => s - capacity ≤ a

private theorem mem_splitSizes {capacity s a : ℕ} :
    a ∈ splitSizes capacity s ↔ a ≤ capacity ∧ a ≤ s ∧ s - a ≤ capacity := by
  simp only [splitSizes, List.mem_filter, List.mem_range, decide_eq_true_eq]
  omega

private def next (capacity : ℕ) (h : ℕ → ℕ) (s : ℕ) : ℕ :=
  ((splitSizes capacity s).map fun a => splitCost h a (s - a)).min?.getD 0

/-- Starting with `h 0 0 = 0` and `h 0 1 = 1`, take the minimum of
`max (h n a) b + max (h n b) a` over `a + b = s` and `a, b ≤ 2^n` at each step. -/
def h : ℕ → ℕ → ℕ
  | 0, s => s
  | n + 1, s => next (2 ^ n) (h n) s

private theorem next_le_splitCost (c : ℕ) (f : ℕ → ℕ) {a b : ℕ} (ha : a ≤ c) (hb : b ≤ c) :
    next c f (a + b) ≤ splitCost f a b := by
  have ha' : a ∈ splitSizes c (a + b) := mem_splitSizes.mpr ⟨ha, by omega, by simpa⟩
  have hmem : splitCost f a b ∈ (splitSizes c (a + b)).map
      (fun z => splitCost f z (a + b - z)) :=
    List.mem_map.mpr ⟨a, ha', by simp⟩
  unfold next Option.getD
  split
  · rename_i hm
    exact (List.min?_eq_some_iff.mp hm).2 _ hmem
  · exact Nat.zero_le _

private theorem splitCost_le_card {n : ℕ} (S : Finset (Fin (n + 1) → Bool)) (f : ℕ → ℕ)
    (hfalse : f (half false S).card ≤ (closedNeighborhood (half false S)).card)
    (htrue : f (half true S).card ≤ (closedNeighborhood (half true S)).card) :
    splitCost f (half false S).card (half true S).card ≤ (closedNeighborhood S).card := by
  rw [card_halves (closedNeighborhood S), half_closedNeighborhood, half_closedNeighborhood]
  apply Nat.add_le_add
  · exact max_le (hfalse.trans (card_le_card subset_union_left)) (card_le_card subset_union_right)
  · exact max_le (htrue.trans (card_le_card subset_union_left)) (card_le_card subset_union_right)

/-- The recurrence bounds the closed neighborhood of every support. -/
theorem h_le_closedNeighborhood_card {n : ℕ} (S : Finset (Fin n → Bool)) :
    h n S.card ≤ (closedNeighborhood S).card := by
  induction n with
  | zero =>
      exact card_le_card (fun x hx => mem_closedNeighborhood.mpr ⟨x, hx, by simp⟩)
  | succ n ih =>
      have capacity (A : Finset (Fin n → Bool)) : A.card ≤ 2 ^ n := by
        simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using A.card_le_univ
      calc
        h (n + 1) S.card ≤ splitCost (h n) (half false S).card (half true S).card := by
          rw [h, card_halves S]
          exact next_le_splitCost _ _ (capacity _) (capacity _)
        _ ≤ (closedNeighborhood S).card := splitCost_le_card S _ (ih _) (ih _)

/-- Row `n` lists the recurrence values in order of support size. -/
private def row : ℕ → Array ℕ
  | 0 => #[0, 1]
  | 1 => #[0, 2, 2]
  | 2 => #[0, 3, 4, 4, 4]
  | 3 => #[0, 4, 6, 7, 7, 8, 8, 8, 8]
  | 4 => #[0, 5, 8, 10, 11, 11, 13, 14, 14, 15, 15, 15, 16, 16, 16, 16, 16]
  | 5 => #[0, 6, 10, 13, 15, 16, 16, 19, 21, 22, 22, 24, 25, 25, 26, 26, 26, 28, 29, 29, 30, 30,
      30, 31, 31, 31, 31, 32, 32, 32, 32, 32, 32]
  | 6 => #[0, 7, 12, 16, 19, 21, 22, 22, 26, 29, 31, 32, 32, 35, 37, 38, 38, 40, 41, 41, 42, 42,
      42, 45, 47, 48, 48, 50, 51, 51, 52, 52, 52, 54, 55, 55, 56, 56, 56, 57, 57, 57, 57, 59,
      60, 60, 61, 61, 61, 62, 62, 62, 62, 63, 63, 63, 63, 63, 64, 64, 64, 64, 64, 64, 64]
  | 7 => #[0, 8, 14, 19, 23, 26, 28, 29, 29, 34, 38, 41, 43, 44, 44, 48, 51, 53, 54, 54, 57, 59,
      60, 60, 62, 63, 63, 64, 64, 64, 68, 71, 73, 74, 74, 77, 79, 80, 80, 82, 83, 83, 84, 84,
      84, 87, 89, 90, 90, 92, 93, 93, 94, 94, 94, 96, 97, 97, 98, 98, 98, 99, 99, 99, 99, 102,
      104, 105, 105, 107, 108, 108, 109, 109, 109, 111, 112, 112, 113, 113, 113, 114, 114, 114,
      114, 116, 117, 117, 118, 118, 118, 119, 119, 119, 119, 120, 120, 120, 120, 120, 122, 123,
      123, 124, 124, 124, 125, 125, 125, 125, 126, 126, 126, 126, 126, 127, 127, 127, 127, 127,
      127, 128, 128, 128, 128, 128, 128, 128, 128]
  | _ => #[]

private def table (n s : ℕ) : ℕ := (row n)[s]?.getD 0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- Check all feasible table entries through dimension seven.
private theorem table_step (n : Fin 7) (s : Fin 129) (hs : s.val ≤ 2 ^ (n.val + 1)) :
    table (n.val + 1) s.val = next (2 ^ n.val) (table n.val) s.val := by
  decide +revert +kernel

private theorem table_eq_h {n s : ℕ} (hn : n ≤ 7) (hs : s ≤ 2 ^ n) : table n s = h n s := by
  induction n generalizing s with
  | zero =>
      have hcases : s = 0 ∨ s = 1 := by omega
      rcases hcases with rfl | rfl <;> rfl
  | succ n ih =>
      have hs' : s < 129 := by
        have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hn
        omega
      have hstep : table (n + 1) s = next (2 ^ n) (table n) s :=
        table_step ⟨n, by omega⟩ ⟨s, hs'⟩ hs
      rw [hstep, h]
      unfold next
      congr 2
      apply List.map_congr_left
      intro a ha
      obtain ⟨ha, _, hb⟩ := mem_splitSizes.mp ha
      unfold splitCost
      rw [ih (by omega) ha, ih (by omega) hb]

/-- The lower limit on either half of a folded parity side of size `3 * m`. -/
def minHalfSize (m : ℕ) : ℕ :=
  if m = 12 then 10 else if m = 13 then 11 else (2 * m + 2) / 3

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- Check all size pairs in the folded parity sides at once.
private theorem table_q7 (m : Fin 32) (a : Fin 94)
    (hm : 12 ≤ m.val) (ha : minHalfSize m.val ≤ a.val)
    (hb : a.val + minHalfSize m.val ≤ 3 * m.val) :
    3 * m.val + 65 ≤ table 7 a.val + table 7 (3 * m.val - a.val) := by
  decide +revert +kernel

/-- All permitted pairs of seven-cube half sizes give at least `3 * m + 65`. -/
theorem q7_split_bound {m a b : ℕ} (hm : 12 ≤ m) (hm' : m ≤ 31) (hab : a + b = 3 * m)
    (ha : minHalfSize m ≤ a) (hb : minHalfSize m ≤ b) :
    3 * m + 65 ≤ h 7 a + h 7 b := by
  have hb' : a + minHalfSize m ≤ 3 * m := by omega
  have htab := table_q7 ⟨m, by omega⟩ ⟨a, by omega⟩ hm ha hb'
  change 3 * m + 65 ≤ table 7 a + table 7 (3 * m - a) at htab
  rw [show 3 * m - a = b by omega, table_eq_h (by decide) (by omega),
    table_eq_h (by decide) (by omega)] at htab
  exact htab

/-- The folded parity side in the eight-cube expands by at least 65
when both first-coordinate halves meet the stated size limit. -/
theorem q8_closedNeighborhood_card_ge (S : Finset (Fin 8 → Bool)) {m : ℕ}
    (hm : 12 ≤ m) (hm' : m ≤ 31) (hsize : S.card = 3 * m)
    (hfalse : minHalfSize m ≤ (half false S).card) (htrue : minHalfSize m ≤ (half true S).card) :
    3 * m + 65 ≤ (closedNeighborhood S).card := by
  have hs := q7_split_bound hm hm' ((card_halves S).symm.trans hsize) hfalse htrue
  have hsplit := splitCost_le_card S (h 7)
    (h_le_closedNeighborhood_card _) (h_le_closedNeighborhood_card _)
  exact hs.trans ((Nat.add_le_add (le_max_left _ _) (le_max_left _ _)).trans hsplit)

#print axioms h_le_closedNeighborhood_card
#print axioms table_eq_h
#print axioms q7_split_bound
#print axioms q8_closedNeighborhood_card_ge

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CubeClosedNeighborhoodRecurrence
