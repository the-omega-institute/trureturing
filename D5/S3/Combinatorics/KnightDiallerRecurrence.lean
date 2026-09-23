/- GID: D5/S3/Combinatorics/KnightDiallerRecurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/KnightDiallerRecurrence
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: Knight walks on the digit keypad satisfy the conjectured fourth-order recurrence. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option maxRecDepth 8000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.KnightDiallerRecurrence

open scoped BigOperators

/-- Knight adjacency on the ten dialable keypad digits. Digit `5` has no neighbours. -/
abbrev adjacency (i j : Fin 10) : Prop :=
  (i = 0 ∧ (j = 4 ∨ j = 6)) ∨
  (i = 1 ∧ (j = 6 ∨ j = 8)) ∨
  (i = 2 ∧ (j = 7 ∨ j = 9)) ∨
  (i = 3 ∧ (j = 4 ∨ j = 8)) ∨
  (i = 4 ∧ (j = 3 ∨ j = 9 ∨ j = 0)) ∨
  (i = 6 ∧ (j = 1 ∨ j = 7 ∨ j = 0)) ∨
  (i = 7 ∧ (j = 2 ∨ j = 6)) ∨
  (i = 8 ∧ (j = 1 ∨ j = 3)) ∨
  (i = 9 ∧ (j = 2 ∨ j = 4))

/-- The number of digit sequences with `n` knight moves, starting at any digit. -/
def dial (n : ℕ) : ℕ :=
  ((Fintype.piFinset
      (fun _ : Fin (n + 1) => (Finset.univ : Finset (Fin 10)))).filter
    (fun s : Fin (n + 1) → Fin 10 =>
      ∀ i : Fin n, adjacency (s i.castSucc) (s i.succ))).card

/-- The additive form of the conjectured recurrence, avoiding truncated natural subtraction. -/
def claim : Prop :=
  ∀ n : ℕ, dial (n + 5) + 4 * dial (n + 1) = 6 * dial (n + 3)

/-- The knight-dialler recurrence conjectured in OEIS A327692. -/
theorem result : claim := by
  let sequences (n : ℕ) : Finset (Fin (n + 1) → Fin 10) :=
    (Fintype.piFinset
      (fun _ : Fin (n + 1) => (Finset.univ : Finset (Fin 10)))).filter
      (fun s : Fin (n + 1) → Fin 10 =>
        ∀ i : Fin n, adjacency (s i.castSucc) (s i.succ))
  let starts (n : ℕ) (i : Fin 10) : Finset (Fin (n + 1) → Fin 10) :=
    (sequences n).filter (fun s : Fin (n + 1) → Fin 10 => s 0 = i)
  let step (v : Fin 10 → ℕ) (i : Fin 10) : ℕ :=
    ∑ j : Fin 10, if adjacency i j then v j else 0
  let u : ℕ → Fin 10 → ℕ := fun n =>
    Nat.rec (fun _ : Fin 10 => 1) (fun _ v => step v) n
  -- membership in the two finite sets
  have mem_sequences (n : ℕ) (s : Fin (n + 1) → Fin 10) :
      s ∈ sequences n ↔
        ∀ i : Fin n, adjacency (s i.castSucc) (s i.succ) := by
    simp only [sequences, Finset.mem_filter, Fintype.mem_piFinset,
      Finset.mem_univ, forall_const, true_and]
  have mem_starts (n : ℕ) (i : Fin 10) (s : Fin (n + 1) → Fin 10) :
      s ∈ starts n i ↔
        (∀ k : Fin n, adjacency (s k.castSucc) (s k.succ)) ∧ s 0 = i := by
    simp only [starts, Finset.mem_filter, mem_sequences]
  -- the single sequence of length one
  have starts_zero (i : Fin 10) : (starts 0 i).card = 1 := by
    have heq : starts 0 i = {fun _ : Fin 1 => i} := by
      ext s
      rw [mem_starts, Finset.mem_singleton]
      constructor
      · intro hs
        funext k
        have hk : k = (0 : Fin 1) := Fin.eq_zero k
        simpa only [hk] using hs.2
      · rintro rfl
        exact ⟨fun k => Fin.elim0 k, rfl⟩
    rw [heq, Finset.card_singleton]
  -- splitting a sequence off its second entry
  have fiber_card (n : ℕ) (i j : Fin 10) :
      ((starts (n + 1) i).filter
        (fun s : Fin ((n + 1) + 1) → Fin 10 => s 1 = j)).card =
        if adjacency i j then (starts n j).card else 0 := by
    by_cases hij : adjacency i j
    · rw [if_pos hij]
      symm
      apply Finset.card_bij
        (s := starts n j)
        (t := (starts (n + 1) i).filter
          (fun s : Fin ((n + 1) + 1) → Fin 10 => s 1 = j))
        (fun (tail : Fin (n + 1) → Fin 10) _ =>
          (Fin.cons i tail : Fin ((n + 1) + 1) → Fin 10))
      · intro tail htail
        rw [Finset.mem_filter]
        have ht := (mem_starts n j tail).1 htail
        refine ⟨(mem_starts (n + 1) i (Fin.cons i tail)).2 ⟨?_, ?_⟩, ?_⟩
        · intro k
          refine Fin.cases ?_ (fun l => ?_) k
          · simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ht.2] using hij
          · simpa only [Fin.castSucc_succ, Fin.cons_succ] using ht.1 l
        · simp only [Fin.cons_zero]
        · simpa only [← Fin.succ_zero_eq_one, Fin.cons_succ] using ht.2
      · intro tail₁ _ tail₂ _ h
        have htail := congrArg Fin.tail h
        simpa only [Fin.tail_cons] using htail
      · intro s hs
        have hs' := Finset.mem_filter.mp hs
        have hstart := (mem_starts (n + 1) i s).1 hs'.1
        refine ⟨Fin.tail s, ?_, ?_⟩
        · apply (mem_starts n j (Fin.tail s)).2
          refine ⟨?_, ?_⟩
          · intro k
            have hk := hstart.1 k.succ
            simpa only [Fin.tail, Fin.succ_castSucc] using hk
          · simpa only [Fin.tail, Fin.succ_zero_eq_one] using hs'.2
        · simpa only [hstart.2] using Fin.cons_self_tail s
    · have hempty :
          (starts (n + 1) i).filter
            (fun s : Fin ((n + 1) + 1) → Fin 10 => s 1 = j) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro s hs
        have hs' := Finset.mem_filter.mp hs
        have hstart := (mem_starts (n + 1) i s).1 hs'.1
        apply hij
        have hzero := hstart.1 (0 : Fin (n + 1))
        simpa only [Fin.castSucc_zero, hstart.2, Fin.succ_zero_eq_one, hs'.2] using hzero
      rw [hempty, Finset.card_empty, if_neg hij]
  -- the transfer step for the fibre counts
  have starts_succ (n : ℕ) (i : Fin 10) :
      (starts (n + 1) i).card =
        ∑ j : Fin 10, if adjacency i j then (starts n j).card else 0 := by
    calc
      (starts (n + 1) i).card =
          ∑ j : Fin 10,
            ((starts (n + 1) i).filter
              (fun s : Fin ((n + 1) + 1) → Fin 10 => s 1 = j)).card := by
        simpa only using
          (Finset.card_eq_sum_card_fiberwise
            (s := starts (n + 1) i) (t := Finset.univ)
            (f := fun s : Fin ((n + 1) + 1) → Fin 10 => s 1) (by simp))
      _ = ∑ j : Fin 10,
          if adjacency i j then (starts n j).card else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        exact fiber_card n i j
  -- the transfer vector and its defining equations
  have u_zero (i : Fin 10) : u 0 i = 1 := by
    rfl
  have u_succ (n : ℕ) (i : Fin 10) : u n.succ i = step (u n) i := by
    rfl
  -- the fibre counts are the transfer vector
  have starts_bridge : ∀ n : ℕ, ∀ i : Fin 10,
      (starts n i).card = u n i := by
    intro n
    induction n with
    | zero =>
        intro i
        rw [starts_zero, u_zero]
    | succ n ih =>
        intro i
        rw [starts_succ, u_succ]
        dsimp only [step]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : adjacency i j
        · simp only [hij, if_true, ih j]
        · simp only [hij, if_false]
  -- the total count is the sum of the transfer vector
  have dial_bridge (n : ℕ) : dial n = ∑ i : Fin 10, u n i := by
    calc
      dial n = (sequences n).card := by
        rfl
      _ = ∑ i : Fin 10, (starts n i).card := by
        simpa only [starts] using
          (Finset.card_eq_sum_card_fiberwise
            (s := sequences n) (t := Finset.univ)
            (f := fun s : Fin (n + 1) → Fin 10 => s 0) (by simp))
      _ = ∑ i : Fin 10, u n i := by
        apply Finset.sum_congr rfl
        intro i _
        exact starts_bridge n i
  -- the identity at the first five steps, by evaluation
  have base : ∀ i : Fin 10, u 5 i + 4 * u 1 i = 6 * u 3 i := by
    intro i
    fin_cases i <;> decide
  -- the transfer step preserves the identity
  have step_recurrence (a b c : Fin 10 → ℕ)
      (h : ∀ j, a j + 4 * b j = 6 * c j) (i : Fin 10) :
      step a i + 4 * step b i = 6 * step c i := by
    dsimp only [step]
    calc
      (∑ j : Fin 10, if adjacency i j then a j else 0) +
          4 * (∑ j : Fin 10, if adjacency i j then b j else 0) =
          ∑ j : Fin 10,
            ((if adjacency i j then a j else 0) +
              4 * (if adjacency i j then b j else 0)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      _ = ∑ j : Fin 10, if adjacency i j then 6 * c j else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : adjacency i j
        · simpa only [hij, if_true] using h j
        · simp only [hij, if_false, mul_zero, add_zero]
      _ = ∑ j : Fin 10, 6 * (if adjacency i j then c j else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : adjacency i j <;> simp only [hij, if_true, if_false, mul_zero]
      _ = 6 * ∑ j : Fin 10, if adjacency i j then c j else 0 := by
        rw [Finset.mul_sum]
  -- hence the identity holds at every step
  have vector_recurrence : ∀ n : ℕ, ∀ i : Fin 10,
      u (n + 5) i + 4 * u (n + 1) i = 6 * u (n + 3) i := by
    intro n
    induction n with
    | zero =>
        simpa only [Nat.zero_add] using base
    | succ n ih =>
        intro i
        simp only [Nat.succ_add, u_succ]
        exact step_recurrence (u (n + 5)) (u (n + 1)) (u (n + 3)) ih i
  -- summing over the starting digit
  intro n
  rw [dial_bridge, dial_bridge, dial_bridge]
  calc
    (∑ i : Fin 10, u (n + 5) i) + 4 * (∑ i : Fin 10, u (n + 1) i) =
        ∑ i : Fin 10, (u (n + 5) i + 4 * u (n + 1) i) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ = ∑ i : Fin 10, 6 * u (n + 3) i := by
      apply Finset.sum_congr rfl
      intro i _
      exact vector_recurrence n i
    _ = 6 * ∑ i : Fin 10, u (n + 3) i := by
      rw [Finset.mul_sum]

end D5.S3.Combinatorics.KnightDiallerRecurrence
