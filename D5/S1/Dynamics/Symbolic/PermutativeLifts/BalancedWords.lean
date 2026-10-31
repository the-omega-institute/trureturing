/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedWords
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/BalancedWords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equal-height factorial words, type separation, common thirds and finite holonomy. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.FactorialWords
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-! Balanced factorial words for equal-height symbolic towers.
The shared outer thirds and type distinction are combinatorial statements;
no existence or dynamical property of a Toeplitz subshift is assumed here. -/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts.Balanced

open D5.S1.Dynamics.Symbolic.PermutativeLifts

/-- Both types contain three factorial blocks, with the doubled type depending on `a`. -/
def balancedWord : ℕ → Bool → List Bool
  | 0, a => [a]
  | n + 1, a =>
      repeatWord (balancedWord n false) ((if a then 1 else 2) * (n + 1).factorial) ++
      repeatWord (balancedWord n true) ((if a then 2 else 1) * (n + 1).factorial)

/-- The common height of the two level-`n` words. -/
def height : ℕ → ℕ
  | 0 => 1
  | n + 1 => 3 * (n + 1).factorial * height n

@[simp] theorem balancedWord_zero (a : Bool) : balancedWord 0 a = [a] := rfl

theorem balancedWord_succ (n : ℕ) (a : Bool) :
    balancedWord (n + 1) a =
      repeatWord (balancedWord n false) ((if a then 1 else 2) * (n + 1).factorial) ++
      repeatWord (balancedWord n true) ((if a then 2 else 1) * (n + 1).factorial) := rfl

@[simp] theorem height_zero : height 0 = 1 := rfl

theorem height_succ (n : ℕ) : height (n + 1) = 3 * (n + 1).factorial * height n := rfl

@[simp] theorem balancedWord_length (n : ℕ) (a : Bool) :
    (balancedWord n a).length = height n := by
  induction n generalizing a with
  | zero => simp [height]
  | succ n ih =>
      cases a <;> simp [balancedWord_succ, ih, height_succ] <;> omega

theorem height_pos (n : ℕ) : 0 < height n := by
  induction n with
  | zero => simp
  | succ n ih => exact Nat.mul_pos (Nat.mul_pos (by decide) (Nat.factorial_pos _)) ih

theorem height_growth (n : ℕ) : 3 * height n ≤ height (n + 1) := by
  have h := Nat.mul_le_mul_left (3 * height n) (Nat.factorial_pos (n + 1))
  simpa [height_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

theorem height_lower_bound (n : ℕ) : n + 1 ≤ height n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hg := height_growth n
      omega

theorem height_tendsto_atTop : Filter.Tendsto height Filter.atTop Filter.atTop := by
  exact Filter.tendsto_atTop_mono (fun n => Nat.le_trans (Nat.le_succ n) (height_lower_bound n))
    Filter.tendsto_id

private theorem count_repeatWord {α : Type*} [DecidableEq α] (w : List α) (k : ℕ)
    (a : α) : (repeatWord w k).count a = k * w.count a := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, Nat.succ_mul, Nat.add_comm]

/-- The imbalance survives every substitution, so equal height does not merge the types. -/
theorem balancedWord_count_false_lt (n : ℕ) :
    (balancedWord n true).count false < (balancedWord n false).count false := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hm := Nat.mul_lt_mul_of_pos_left ih (Nat.factorial_pos (n + 1))
      simp only [balancedWord_succ, Bool.false_eq_true, reduceIte, one_mul,
        List.count_append, count_repeatWord]
      nlinarith

theorem balancedWord_injective (n : ℕ) : Function.Injective (balancedWord n) := by
  intro a b h
  have hd := balancedWord_count_false_lt n
  cases a <;> cases b <;> simp_all

/-- A whole factorial third, rather than merely one child word, is a common prefix. -/
theorem balancedWord_common_prefix (n : ℕ) (a : Bool) :
    repeatWord (balancedWord n false) (n + 1).factorial <+: balancedWord (n + 1) a := by
  cases a
  · simp only [balancedWord_succ, Bool.false_eq_true, reduceIte, one_mul]
    rw [show 2 * (n + 1).factorial = (n + 1).factorial + (n + 1).factorial by omega,
      repeatWord_add, List.append_assoc]
    exact List.prefix_append _ _
  · simp only [balancedWord_succ, reduceIte, one_mul]
    exact List.prefix_append _ _

/-- The terminal factorial third is also independent of the parent type. -/
theorem balancedWord_common_suffix (n : ℕ) (a : Bool) :
    repeatWord (balancedWord n true) (n + 1).factorial <:+ balancedWord (n + 1) a := by
  cases a
  · simp only [balancedWord_succ, Bool.false_eq_true, reduceIte, one_mul]
    exact List.suffix_append _ _
  · simp only [balancedWord_succ, reduceIte, one_mul]
    rw [show 2 * (n + 1).factorial = (n + 1).factorial + (n + 1).factorial by omega,
      repeatWord_add, ← List.append_assoc]
    exact List.suffix_append _ _

theorem common_third_length (n : ℕ) (a : Bool) :
    (repeatWord (balancedWord n a) (n + 1).factorial).length = height (n + 1) / 3 := by
  rw [length_repeatWord, balancedWord_length, height_succ]
  omega

theorem balancedWord_prefix_false (n : ℕ) (a : Bool) :
    balancedWord n false <+: balancedWord (n + 1) a :=
  (prefix_repeatWord _ (Nat.factorial_pos _)).trans (balancedWord_common_prefix n a)

theorem balancedWord_suffix_true (n : ℕ) (a : Bool) :
    balancedWord n true <:+ balancedWord (n + 1) a :=
  (suffix_repeatWord _ (Nat.factorial_pos _)).trans (balancedWord_common_suffix n a)

theorem balancedWord_block_infix (n : ℕ) (a b : Bool) :
    balancedWord n b <:+: balancedWord (n + 1) a := by
  cases b
  · exact (balancedWord_prefix_false n a).isInfix
  · exact (balancedWord_suffix_true n a).isInfix

private theorem same_pair_next (n : ℕ) (hn : 1 ≤ n) (a b : Bool) :
    balancedWord n b ++ balancedWord n b <:+: balancedWord (n + 1) a := by
  have hf : 2 ≤ (n + 1).factorial := by
    have := (Nat.one_lt_factorial).mpr (show 1 < n + 1 by omega)
    omega
  rw [balancedWord_succ]
  cases b
  · have hk : 2 ≤ (if a then 1 else 2) * (n + 1).factorial := by
      cases a <;> simp <;> omega
    exact List.infix_append_of_infix_left (repeatWord_pair_prefix _ hk).isInfix
  · have hk : 2 ≤ (if a then 2 else 1) * (n + 1).factorial := by
      cases a <;> simp <;> omega
    exact List.infix_append_of_infix_right (repeatWord_pair_prefix _ hk).isInfix

private theorem zero_one_pair_next (n : ℕ) (a : Bool) :
    balancedWord n false ++ balancedWord n true <:+: balancedWord (n + 1) a := by
  rw [balancedWord_succ]
  have h0 : 0 < (if a then 1 else 2) * (n + 1).factorial := by
    cases a <;> simp [Nat.factorial_pos]
  have h1 : 0 < (if a then 2 else 1) * (n + 1).factorial := by
    cases a <;> simp [Nat.factorial_pos]
  exact suffix_prefix_infix (suffix_repeatWord _ h0) (prefix_repeatWord _ h1)

/-- Every ordered pair of child types occurs two levels later, including the seam pair 10. -/
theorem balancedWord_pair_infix (n : ℕ) (hn : 1 ≤ n) (a b c : Bool) :
    balancedWord n b ++ balancedWord n c <:+: balancedWord (n + 2) a := by
  cases b <;> cases c
  · exact (same_pair_next n hn false false).trans (balancedWord_block_infix (n + 1) a false)
  · exact (zero_one_pair_next n false).trans (balancedWord_block_infix (n + 1) a false)
  · exact (suffix_prefix_infix (balancedWord_suffix_true n false)
      (balancedWord_prefix_false n true)).trans (zero_one_pair_next (n + 1) a)
  · exact (same_pair_next n hn false true).trans (balancedWord_block_infix (n + 1) a false)

/-- Factorial exponents kill the two factors separately, without commuting them. -/
theorem balancedWord_holonomy_eq_one {G : Type*} [Group G] [Finite G] (π : Bool → G)
    (n : ℕ) (hn : Nat.card G ≤ n + 1) (a : Bool) :
    wordHolonomy π (balancedWord (n + 1) a) = 1 := by
  rw [balancedWord_succ, wordHolonomy_append, wordHolonomy_repeat, wordHolonomy_repeat]
  have h0 := finite_group_pow_factorial (wordHolonomy π (balancedWord n false)) hn
  have h1 := finite_group_pow_factorial (wordHolonomy π (balancedWord n true)) hn
  rw [Nat.mul_comm (if a then 2 else 1), Nat.mul_comm (if a then 1 else 2),
    pow_mul, pow_mul, h0, h1]
  simp

end D5.S1.Dynamics.Symbolic.PermutativeLifts.Balanced
