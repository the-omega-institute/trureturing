/- GID: D5/S1/Words/Palindromes/FridPrefix/RankCyclesA
   generality: I
   mirror-B: D5/B/S1/Words/Palindromes/FridPrefix/RankCyclesA
   mirror-E: none(waiver:exact-chunk-cycle)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/Palindromes/FridPrefix/FridPrefixPalindromicLength.result; instance=D5/S1/Words/Palindromes/FridPrefix/RankA.rankA
   digest: Zero padding and the 100100 cycle give the exact score of every target word. -/

/-
proof_shape: content (a_seed_cycle).
escape_witness: induction on the weighted six-bit seed cycle.
admission_basis: escape-witness.
Direct frozen dependencies: none; remaining dependencies are pinned Mathlib or this delivery.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.FridPrefix.RankA
import Mathlib.Data.Int.Cast.Lemmas

namespace D5.S1.Words.FridPrefix

/-- Whole zero chunks preserve the score of the repeated 100100 seed ending in 100101. -/
theorem a_seed_cycle (k z : ℕ) :
    chunkScore rankA (List.replicate z 0 ++ List.replicate k 36 ++ [37]) = 2*(k : ℤ)+3 := by
  let advance (s : ℕ × ℤ) (x : ℕ) :=
    ((rankA.transitions.getD s.1 #[]).getD x 0,s.2+(rankA.weights.getD s.1 #[]).getD x 0)
  have table :
      (rankA.transitions.getD 0 #[]).getD 0 0 = 0 ∧
      (rankA.weights.getD 0 #[]).getD 0 0 = 0 ∧
      (rankA.transitions.getD 0 #[]).getD 36 0 = 16 ∧
      (rankA.weights.getD 0 #[]).getD 36 0 = 2 ∧
      (rankA.transitions.getD 16 #[]).getD 36 0 = 16 ∧
      (rankA.weights.getD 16 #[]).getD 36 0 = 2 ∧
      (rankA.transitions.getD 0 #[]).getD 37 0 = 17 ∧
      (rankA.weights.getD 0 #[]).getD 37 0 = 3 ∧
      (rankA.transitions.getD 16 #[]).getD 37 0 = 17 ∧
      (rankA.weights.getD 16 #[]).getD 37 0 = 3 := by decide +kernel
  obtain ⟨h00,w00,h036,w036,h1636,w1636,h037,w037,h1637,w1637⟩ := table
  have zero_cycle (z : ℕ) (t : ℤ) :
      (List.replicate z 0).foldl advance (0,t) = (0,t) := by
    induction z with
    | zero => rfl
    | succ z ih => simpa only [List.replicate_succ,List.foldl_cons,advance,Prod.fst,Prod.snd,h00,w00,add_zero] using ih
  have cycle (k : ℕ) (t : ℤ) :
      (List.replicate k 36 ++ [37]).foldl advance (16,t) = (17,t+2*(k : ℤ)+3) := by
    induction k generalizing t with
    | zero => simp only [List.replicate_zero,List.nil_append,List.foldl_cons,List.foldl_nil,advance,
        Prod.fst,Prod.snd,h1637,w1637,Nat.cast_zero,mul_zero,add_zero]
    | succ k ih =>
      simp only [List.replicate_succ,List.cons_append,List.foldl_cons,advance,
        Prod.fst,Prod.snd,h1636,w1636]
      rw [ih]
      congr 1
      omega
  change ((List.replicate z 0 ++ List.replicate k 36 ++ [37]).foldl advance (0,0)).2 = _
  rw [List.append_assoc,List.foldl_append,zero_cycle]
  cases k with
  | zero => simp only [List.replicate_zero,List.nil_append,List.foldl_cons,List.foldl_nil,advance,
      Prod.fst,Prod.snd,h037,w037,zero_add,Nat.cast_zero,mul_zero]
  | succ k =>
    simp only [List.replicate_succ,List.cons_append,List.foldl_cons,advance,
      Prod.fst,Prod.snd,h036,w036,zero_add]
    rw [cycle]
    simp only [Prod.snd]
    omega

end D5.S1.Words.FridPrefix
