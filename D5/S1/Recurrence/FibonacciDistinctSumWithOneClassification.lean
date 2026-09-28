/- GID: D5/S1/Recurrence/FibonacciDistinctSumWithOneClassification
   generality: I
   mirror-B: D5/B/S1/Recurrence/FibonacciDistinctSumWithOneClassification
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Fibonacci sets containing one have Fibonacci sum exactly in alternating form. -/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace D5.S1.Recurrence.FibonacciDistinctSumWithOneClassification

open Finset

/-- Positive Fibonacci values, with the repeated value one represented at index two. -/
def PositiveFibonacci (x : ℕ) : Prop := ∃ n, 2 ≤ n ∧ Nat.fib n = x

/-- One together with the odd-indexed Fibonacci values from index three to index `2*r-1`. -/
def alternatingSet (r : ℕ) : Finset ℕ :=
  insert 1 ((Ico 1 r).image fun j => Nat.fib (2 * j + 1))

/-- Classification, value of the sum, and uniqueness of the alternating initial set.
There is no restriction forbidding adjacent Fibonacci indices in the input set. -/
theorem classification (S : Finset ℕ)
    (hS : ∀ x ∈ S, PositiveFibonacci x) (hone : 1 ∈ S) :
    (PositiveFibonacci (∑ x ∈ S, x) ↔ ∃ r, 1 ≤ r ∧ S = alternatingSet r) ∧
    (∀ r, 1 ≤ r → S = alternatingSet r →
      (∑ x ∈ S, x) = Nat.fib (2 * r) ∧
      ∀ t, 1 ≤ t → S = alternatingSet t → t = r) := by
  have hinj : Set.InjOn Nat.fib (Set.Ici 2) := Nat.fib_strictMonoOn.injOn
  have step (r : ℕ) (hr : 1 ≤ r) :
      alternatingSet (r + 1) = insert (Nat.fib (2 * r + 1)) (alternatingSet r) := by
    simp only [alternatingSet, Nat.Ico_succ_right_eq_insert_Ico hr, image_insert]
    exact insert_comm _ _ _
  have values : ∀ r, 1 ≤ r → (∑ x ∈ alternatingSet r, x) = Nat.fib (2 * r) := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base => norm_num [alternatingSet]
    | succ r hr ih =>
      have hbig : 1 < Nat.fib (2 * r + 1) := by
        have h := (Nat.fib_lt_fib (by decide : 2 ≤ 2)).2 (show 2 < 2 * r + 1 by omega)
        simpa using h
      have hnot : Nat.fib (2 * r + 1) ∉ alternatingSet r := by
        simp only [alternatingSet, mem_insert, mem_image, mem_Ico]
        rintro (heq | ⟨j, hj, heq⟩)
        · omega
        · have hlt := (Nat.fib_lt_fib (show 2 ≤ 2 * j + 1 by omega)).2
              (show 2 * j + 1 < 2 * r + 1 by omega)
          omega
      rw [step r hr, sum_insert hnot, ih]
      rw [show 2 * (r + 1) = 2 * r + 2 by omega, Nat.fib_add_two]
      omega
  have forward : ∀ n, 2 ≤ n → ∀ T : Finset ℕ,
      (∀ x ∈ T, PositiveFibonacci x) → 1 ∈ T → (∑ x ∈ T, x) = Nat.fib n →
      ∃ r, 1 ≤ r ∧ n = 2 * r ∧ T = alternatingSet r := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn T hT h1 hsum
      have pos (x : ℕ) (hx : x ∈ T) : 0 < x := by
        rcases hT x hx with ⟨i, hi, rfl⟩
        exact Nat.fib_pos.mpr (by omega)
      have small (hs : (∑ x ∈ T, x) = 1) : T = {1} := by
        apply Subset.antisymm
        · intro x hx
          have hle : x ≤ ∑ y ∈ T, y :=
            single_le_sum (f := fun y : ℕ => y) (fun _ _ => Nat.zero_le _) hx
          have hp := pos x hx
          simp only [mem_singleton]
          omega
        · simpa using h1
      by_cases hn2 : n = 2
      · subst n
        refine ⟨1, by omega, by omega, ?_⟩
        simpa [alternatingSet] using small (by simpa using hsum)
      have hn3 : 3 ≤ n := by omega
      have strict (x : ℕ) (hx : x ∈ T) : x < Nat.fib n := by
        by_cases hx1 : x = 1
        · subst x
          have h := (Nat.fib_lt_fib (by decide : 2 ≤ 2)).2 (show 2 < n by omega)
          simpa using h
        · have he : 1 ∈ T.erase x := mem_erase.mpr ⟨Ne.symm hx1, h1⟩
          have hle : 1 ≤ ∑ y ∈ T.erase x, y :=
            single_le_sum (f := fun y : ℕ => y) (fun _ _ => Nat.zero_le _) he
          have hadd := sum_erase_add T (fun y : ℕ => y) hx
          omega
      have hn4 : 4 ≤ n := by
        by_contra h
        have hn : n = 3 := by omega
        have heq : T = {1} := by
          apply Subset.antisymm
          · intro x hx
            have hp := pos x hx
            have hb := strict x hx
            simp only [hn] at hb
            norm_num at hb
            simp only [mem_singleton]
            omega
          · simpa using h1
        subst n
        norm_num [heq] at hsum
      have forced : Nat.fib (n - 1) ∈ T := by
        by_contra hmissing
        have hsub : T ⊆ (Ico 2 (n - 1)).image Nat.fib := by
          intro x hx
          rcases hT x hx with ⟨i, hi, rfl⟩
          have hil : i < n := (Nat.fib_lt_fib hi).mp (strict _ hx)
          have hine : i ≠ n - 1 := by
            intro heq
            subst i
            exact hmissing hx
          exact mem_image.mpr ⟨i, mem_Ico.mpr ⟨hi, by omega⟩, rfl⟩
        have hle : (∑ x ∈ T, x) ≤ ∑ x ∈ (Ico 2 (n - 1)).image Nat.fib, x :=
          sum_le_sum_of_subset hsub
        have himage : (∑ x ∈ (Ico 2 (n - 1)).image Nat.fib, x) =
            ∑ i ∈ Ico 2 (n - 1), Nat.fib i := by
          apply sum_image
          intro i hi j hj heq
          exact hinj (mem_Ico.mp hi).1 (mem_Ico.mp hj).1 heq
        have hprefix := sum_range_add_sum_Ico Nat.fib (show 2 ≤ n - 1 by omega)
        have hall := Nat.fib_succ_eq_succ_sum (n - 1)
        rw [show n - 1 + 1 = n by omega] at hall
        norm_num [sum_range_succ] at hprefix
        rw [himage, hsum] at hle
        omega
      have hpred : 1 < Nat.fib (n - 1) := by
        have h := (Nat.fib_lt_fib (by decide : 2 ≤ 2)).2 (show 2 < n - 1 by omega)
        simpa using h
      have herase : (∑ x ∈ T.erase (Nat.fib (n - 1)), x) = Nat.fib (n - 2) := by
        have hadd := sum_erase_add T (fun y : ℕ => y) forced
        have hrec := @Nat.fib_add_two (n - 2)
        rw [show n - 2 + 2 = n by omega, show n - 2 + 1 = n - 1 by omega] at hrec
        omega
      obtain ⟨r, hr, hnr, hshape⟩ := ih (n - 2) (by omega) (by omega)
        (T.erase (Nat.fib (n - 1)))
        (fun x hx => hT x (mem_of_mem_erase hx))
        (mem_erase.mpr ⟨by omega, h1⟩) herase
      refine ⟨r + 1, by omega, by omega, ?_⟩
      rw [step r hr, ← hshape, show 2 * r + 1 = n - 1 by omega]
      exact (insert_erase forced).symm
  constructor
  · constructor
    · rintro ⟨n, hn, heq⟩
      obtain ⟨r, hr, _, hshape⟩ := forward n hn S hS hone heq.symm
      exact ⟨r, hr, hshape⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨2 * r, by omega, (values r hr).symm⟩
  · intro r hr hshape
    refine ⟨hshape ▸ values r hr, ?_⟩
    intro t ht htshape
    have heq : Nat.fib (2 * t) = Nat.fib (2 * r) := by
      rw [← values t ht, ← values r hr, ← hshape, ← htshape]
    have := hinj (by omega : 2 ≤ 2 * t) (by omega : 2 ≤ 2 * r) heq
    omega

end D5.S1.Recurrence.FibonacciDistinctSumWithOneClassification
