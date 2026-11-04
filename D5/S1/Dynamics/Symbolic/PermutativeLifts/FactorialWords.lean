/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialWords
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/FactorialWords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Factorial S-adic words, recurrent block pairs and finite-action holonomy. -/

import Mathlib.Data.List.Infix
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Actual factorial words and their block-recurrence and finite-action identities. -/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts

/-- Repetition is literal concatenation of finitely many copies of a word. -/
def repeatWord {α : Type*} (w : List α) (k : ℕ) : List α :=
  (List.replicate k w).flatten

@[simp] theorem repeatWord_zero {α : Type*} (w : List α) : repeatWord w 0 = [] := rfl

@[simp] theorem repeatWord_succ {α : Type*} (w : List α) (k : ℕ) :
    repeatWord w (k + 1) = w ++ repeatWord w k := by
  simp [repeatWord, List.replicate_succ]

@[simp] theorem repeatWord_one {α : Type*} (w : List α) : repeatWord w 1 = w := by
  simp

theorem repeatWord_add {α : Type*} (w : List α) (m k : ℕ) :
    repeatWord w (m + k) = repeatWord w m ++ repeatWord w k := by
  induction m with
  | zero => simp
  | succ m ih => simp [Nat.succ_add, ih, List.append_assoc]

@[simp] theorem length_repeatWord {α : Type*} (w : List α) (k : ℕ) :
    (repeatWord w k).length = k * w.length := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, Nat.succ_mul, Nat.add_comm]

/-- Reading a repeated word uses the actual offset modulo its positive length. -/
theorem repeatWord_getElem {α : Type*} (w : List α) {k i : ℕ}
    (hw : 0 < w.length) (hi : i < k * w.length) :
    (repeatWord w k)[i]'(by simpa only [length_repeatWord] using hi) =
      w[i % w.length]'(Nat.mod_lt _ hw) := by
  induction k generalizing i with
  | zero => simp at hi
  | succ k ih =>
      have hip : i < (w ++ repeatWord w k).length := by
        simp only [List.length_append, length_repeatWord]
        simp only [Nat.succ_mul] at hi
        omega
      have hget : (w ++ repeatWord w k)[i]'hip =
          w[i % w.length]'(Nat.mod_lt _ hw) := by
        by_cases hfirst : i < w.length
        · simp only [List.getElem_append_left hfirst, Nat.mod_eq_of_lt hfirst]
        · have hge : w.length ≤ i := by omega
          have hi' : i - w.length < k * w.length := by
            simp only [Nat.succ_mul] at hi
            omega
          rw [List.getElem_append_right hge, ih hi']
          have hm : (i - w.length) % w.length = i % w.length :=
            (Nat.mod_eq_sub_mod hge).symm
          simp only [hm]
      simpa only [repeatWord_succ] using hget

/-- The actual binary words in the universal finite-permutation construction. -/
def word : ℕ → Bool → List Bool
  | 0, a => [a]
  | n + 1, a => repeatWord (word n false) (n + 1).factorial ++
      repeatWord (word n true) ((if a then 2 else 1) * (n + 1).factorial)

@[simp] theorem word_zero (a : Bool) : word 0 a = [a] := rfl

theorem word_succ (n : ℕ) (a : Bool) :
    word (n + 1) a = repeatWord (word n false) (n + 1).factorial ++
      repeatWord (word n true) ((if a then 2 else 1) * (n + 1).factorial) := rfl

@[simp] theorem word_length_succ (n : ℕ) (a : Bool) :
    (word (n + 1) a).length =
      (n + 1).factorial * (word n false).length +
      ((if a then 2 else 1) * (n + 1).factorial) * (word n true).length := by
  simp [word_succ]

theorem word_false_length_le_true (n : ℕ) :
    (word n false).length ≤ (word n true).length := by
  cases n with
  | zero => simp
  | succ n =>
      simp only [word_length_succ, Bool.false_eq_true, reduceIte, one_mul]
      nlinarith

theorem word_length_growth (n : ℕ) (a : Bool) :
    2 * (word n false).length ≤ (word (n + 1) a).length := by
  have hf : 1 ≤ (n + 1).factorial := Nat.factorial_pos _
  have hfirst := Nat.mul_le_mul_right (word n false).length hf
  have hsecond := Nat.mul_le_mul_right (word n true).length hf
  have htypes := word_false_length_le_true n
  cases a <;> simp only [word_length_succ, Bool.false_eq_true, reduceIte, one_mul] <;>
    nlinarith

theorem word_length_lower_bound (n : ℕ) (a : Bool) :
    n + 1 ≤ (word n a).length := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
      have hg := word_length_growth n a
      have hl := ih false
      omega

theorem word_length_pos (n : ℕ) (a : Bool) : 0 < (word n a).length := by
  have := word_length_lower_bound n a
  omega

theorem word_false_length_lt_true {n : ℕ} (hn : 0 < n) :
    (word n false).length < (word n true).length := by
  cases n with
  | zero => omega
  | succ n =>
      have hf := Nat.factorial_pos (n + 1)
      have hl := word_length_pos n true
      simp only [word_length_succ, Bool.false_eq_true, reduceIte, one_mul]
      nlinarith

theorem prefix_repeatWord {α : Type*} (w : List α) {k : ℕ} (hk : 0 < k) :
    w <+: repeatWord w k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simp

theorem suffix_repeatWord {α : Type*} (w : List α) {k : ℕ} (hk : 0 < k) :
    w <:+ repeatWord w k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  change w <:+ repeatWord w (k + 1)
  rw [repeatWord_add, repeatWord_one]
  exact List.suffix_append _ _

theorem word_prefix_false (n : ℕ) (a : Bool) : word n false <+: word (n + 1) a := by
  exact (prefix_repeatWord _ (Nat.factorial_pos _)).trans (List.prefix_append _ _)

theorem word_suffix_true (n : ℕ) (a : Bool) : word n true <:+ word (n + 1) a := by
  have hk : 0 < (if a then 2 else 1) * (n + 1).factorial := by
    cases a <;> simp [Nat.factorial_pos]
  exact (suffix_repeatWord _ hk).trans (List.suffix_append _ _)

theorem word_block_infix (n : ℕ) (a b : Bool) : word n b <:+: word (n + 1) a := by
  cases b
  · exact (word_prefix_false n a).isInfix
  · exact (word_suffix_true n a).isInfix

theorem repeatWord_pair_prefix {α : Type*} (w : List α) {k : ℕ}
    (hk : 2 ≤ k) : w ++ w <+: repeatWord w k := by
  have he : k = 2 + (k - 2) := by omega
  rw [he, repeatWord_add]
  simp

theorem suffix_prefix_infix {α : Type*} {u v U V : List α}
    (hu : u <:+ U) (hv : v <+: V) : u ++ v <:+: U ++ V := by
  obtain ⟨p, rfl⟩ := hu
  obtain ⟨s, rfl⟩ := hv
  exact ⟨p, s, by simp [List.append_assoc]⟩

private theorem same_pair_next (n : ℕ) (hn : 1 ≤ n) (a b : Bool) :
    word n b ++ word n b <:+: word (n + 1) a := by
  have hf : 2 ≤ (n + 1).factorial := by
    have := (Nat.one_lt_factorial).mpr (show 1 < n + 1 by omega)
    omega
  rw [word_succ]
  cases b
  · exact List.infix_append_of_infix_left (repeatWord_pair_prefix _ hf).isInfix
  · have hk : 2 ≤ (if a then 2 else 1) * (n + 1).factorial := by
      cases a <;> simp <;> omega
    exact List.infix_append_of_infix_right (repeatWord_pair_prefix _ hk).isInfix

private theorem zero_one_pair_next (n : ℕ) (a : Bool) :
    word n false ++ word n true <:+: word (n + 1) a := by
  have hk : 0 < (if a then 2 else 1) * (n + 1).factorial := by
    cases a <;> simp [Nat.factorial_pos]
  exact suffix_prefix_infix
    (suffix_repeatWord _ (Nat.factorial_pos _)) (prefix_repeatWord _ hk)

/-- Every level-n block pair, including the crossing pair 10, occurs in each
actual level-(n+2) word. This is the recurrence input used for minimality. -/
theorem word_pair_infix (n : ℕ) (hn : 1 ≤ n) (a b c : Bool) :
    word n b ++ word n c <:+: word (n + 2) a := by
  cases b <;> cases c
  · exact (same_pair_next n hn false false).trans (word_block_infix (n + 1) a false)
  · exact (zero_one_pair_next n false).trans (word_block_infix (n + 1) a false)
  · exact (suffix_prefix_infix (word_suffix_true n false) (word_prefix_false n true)).trans
      (zero_one_pair_next (n + 1) a)
  · exact (same_pair_next n hn false true).trans (word_block_infix (n + 1) a false)

/-- Products follow the time order of a left permutation action: the last
letter acts on the left. In particular this is an antihomomorphism of words. -/
def wordHolonomy {G : Type*} [Monoid G] (π : Bool → G) : List Bool → G
  | [] => 1
  | a :: w => wordHolonomy π w * π a

@[simp] theorem wordHolonomy_nil {G : Type*} [Monoid G] (π : Bool → G) :
    wordHolonomy π [] = 1 := rfl

@[simp] theorem wordHolonomy_cons {G : Type*} [Monoid G] (π : Bool → G)
    (a : Bool) (w : List Bool) : wordHolonomy π (a :: w) = wordHolonomy π w * π a := rfl

theorem wordHolonomy_append {G : Type*} [Monoid G] (π : Bool → G) (u v : List Bool) :
    wordHolonomy π (u ++ v) = wordHolonomy π v * wordHolonomy π u := by
  induction u with
  | nil => simp
  | cons a u ih => simp [ih, mul_assoc]

theorem wordHolonomy_repeat {G : Type*} [Monoid G] (π : Bool → G)
    (w : List Bool) (k : ℕ) : wordHolonomy π (repeatWord w k) = wordHolonomy π w ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp [wordHolonomy_append, ih, pow_succ]

theorem finite_group_pow_factorial {G : Type*} [Group G] [Finite G]
    (g : G) {n : ℕ} (hn : Nat.card G ≤ n) : g ^ n.factorial = 1 := by
  obtain ⟨k, hk⟩ := Nat.dvd_factorial (Nat.card_pos (α := G)) hn
  rw [hk, pow_mul, pow_card_eq_one', one_pow]

/-- Every finite group-valued letter cocycle has trivial holonomy on BOTH
actual words at all sufficiently large levels. No commutativity is assumed. -/
theorem word_holonomy_eq_one {G : Type*} [Group G] [Finite G] (π : Bool → G)
    {n : ℕ} (hn0 : 0 < n) (hn : Nat.card G ≤ n) (a : Bool) :
    wordHolonomy π (word n a) = 1 := by
  cases n with
  | zero => omega
  | succ n =>
      rw [word_succ, wordHolonomy_append, wordHolonomy_repeat, wordHolonomy_repeat]
      have h0 := finite_group_pow_factorial (wordHolonomy π (word n false)) hn
      have h1 := finite_group_pow_factorial (wordHolonomy π (word n true)) hn
      rw [Nat.mul_comm (if a then 2 else 1), pow_mul, h0, h1]
      simp

end D5.S1.Dynamics.Symbolic.PermutativeLifts
