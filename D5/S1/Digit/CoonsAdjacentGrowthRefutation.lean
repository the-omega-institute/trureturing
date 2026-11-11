/- GID: D5/S1/Digit/CoonsAdjacentGrowthRefutation
   generality: I
   mirror-B: D5/B/S1/Digit/CoonsAdjacentGrowthRefutation
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: [mathlib/module/Mathlib.Data.Nat.Digits.Lemmas]
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Digit/CoonsAdjacentGrowthRefutation.claim; result=D5/S1/Digit/CoonsAdjacentGrowthRefutation.result; claim=D5/S1/Digit/CoonsAdjacentGrowthRefutation.claim
   digest: Radix four has equal adjacent bounded-digit logarithmic growth exponents. -/

import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Tactic

namespace D5.S1.Digit.CoonsAdjacentGrowthRefutation

open scoped BigOperators

noncomputable section

/-- Each function occurs once, independently of any zero padding. -/
def weight (ell : ℕ) (a : ℕ →₀ ℕ) : ℕ := a.sum (fun i d => d * ell ^ i)

def Partitions (k ell n : ℕ) :=
  {a : ℕ →₀ ℕ // (∀ i, a i ≤ k) ∧ weight ell a = n}

def count (k ell n : ℕ) : ℕ := Nat.card (Partitions k ell n)

/-- The values at zero and one do not enter any of the tails below. -/
def readout (k ell n : ℕ) : ℝ := Real.log (count k ell n) / Real.log n

/-- The literal extended-real, all-natural every-tail definition. -/
def exponent (k ell : ℕ) : EReal :=
  ⨅ (N : ℕ) (_ : 2 ≤ N), ⨆ (n : ℕ) (_ : N ≤ n), (readout k ell n : EReal)

def claim : Prop :=
  ∀ ell : ℕ, 2 ≤ ell → ∀ k : ℕ, ell - 1 ≤ k →
    exponent k ell < exponent (k + 1) ell

private def window (ell m : ℕ) (u : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, u i * ell ^ i

private lemma window_succ (ell m : ℕ) (u : ℕ → ℕ) :
    window ell (m + 1) u = u 0 + ell * window ell m (fun i => u (i + 1)) := by
  simp only [window, Finset.sum_range_succ', pow_zero, mul_one, pow_succ,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

private def pack (m : ℕ) (u : ℕ → ℕ) : ℕ →₀ ℕ :=
  Finsupp.onFinset (Finset.range m) (fun i => if i < m then u i else 0)
    (by intro i hi; simp only [Finset.mem_range]; by_contra h; simp [h] at hi)

private lemma pack_apply (m : ℕ) (u : ℕ → ℕ) (i : ℕ) :
    pack m u i = if i < m then u i else 0 := rfl

private lemma weight_window (ell m : ℕ) (a : ℕ →₀ ℕ)
    (h : ∀ i, m ≤ i → a i = 0) : weight ell a = window ell m a := by
  unfold weight window
  apply Finsupp.sum_of_support_subset
  · intro i hi
    simp only [Finset.mem_range]
    by_contra hn
    exact Finsupp.mem_support_iff.mp hi (h i (by omega))
  · simp

private lemma weight_pack (ell m : ℕ) (u : ℕ → ℕ) :
    weight ell (pack m u) = window ell m u := by
  rw [weight_window ell m _ (by intro i hi; simp [pack_apply, not_lt.mpr hi])]
  apply Finset.sum_congr rfl
  intro i hi
  simp [pack_apply, Finset.mem_range.mp hi]

private lemma term_le_weight (ell : ℕ) (a : ℕ →₀ ℕ) (i : ℕ) :
    a i * ell ^ i ≤ weight ell a := by
  by_cases hi : a i = 0
  · simp [hi]
  · exact Finset.single_le_sum (fun j _ => Nat.zero_le (a j * ell ^ j))
      (Finsupp.mem_support_iff.mpr hi)

private lemma support_bound {ell n m : ℕ} (hell : 2 ≤ ell) (hn : n < ell ^ m)
    (a : ℕ →₀ ℕ) (ha : weight ell a = n) : ∀ i, m ≤ i → a i = 0 := by
  intro i hi
  by_contra h
  have hp : ell ^ m ≤ ell ^ i := Nat.pow_le_pow_right (by omega) hi
  have ht := term_le_weight ell a i
  have : 1 ≤ a i := by omega
  rw [ha] at ht
  nlinarith

/-- Actual finite-support representations form a finite set for every admissible radix. -/
theorem partitions_finite (k ell n : ℕ) (hell : 2 ≤ ell) :
    Finite (Partitions k ell n) := by
  let m := n + 1
  have hn : n < ell ^ m := by
    have h := Nat.lt_pow_self (by omega : 1 < ell) (n := m)
    omega
  let f : Partitions k ell n → (Fin m → Fin (k + 1)) :=
    fun a i => ⟨a.val i, Nat.lt_succ_of_le (a.property.1 i)⟩
  apply Finite.of_injective f
  intro a b hab
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  by_cases hi : i < m
  · exact congrArg Fin.val (congrFun hab ⟨i, hi⟩)
  · rw [support_bound hell hn a.val a.property.2 i (by omega),
      support_bound hell hn b.val b.property.2 i (by omega)]

private lemma window_digits (ell : ℕ) (l : List ℕ) :
    window ell l.length (fun i => l[i]?.getD 0) = Nat.ofDigits ell l := by
  induction l with
  | nil => simp [window]
  | cons d l ih =>
    rw [List.length_cons, window_succ]
    simpa [Nat.ofDigits_cons] using congrArg (fun x => d + ell * x) ih

/-- Ordinary radix digits give positivity for the entire quantified parameter range. -/
theorem count_positive (k ell n : ℕ) (hell : 2 ≤ ell) (hk : ell - 1 ≤ k) :
    0 < count k ell n := by
  let l := Nat.digits ell n
  let a := pack l.length (fun i => l[i]?.getD 0)
  have ha : ∀ i, a i ≤ k := by
    intro i
    dsimp [a]
    rw [pack_apply]
    split_ifs with hi
    · have hmem : l[i]?.getD 0 ∈ l := by
        simpa [List.getElem?_eq_getElem hi] using List.getElem_mem hi
      have hd := Nat.digits_lt_base (by omega : 1 < ell) hmem
      omega
    · omega
  have hw : weight ell a = n := by
    rw [weight_pack, window_digits, Nat.ofDigits_digits]
  letI := partitions_finite k ell n hell
  haveI : Nonempty (Partitions k ell n) := ⟨⟨a, ha, hw⟩⟩
  exact Nat.card_pos

private lemma quotient_injective (m : ℕ) (u v : ℕ → ℕ)
    (hs : window 4 m u = window 4 m v)
    (hq : ∀ i, i < m → u i / 4 = v i / 4) :
    ∀ i, i < m → u i = v i := by
  induction m generalizing u v with
  | zero => simp
  | succ m ih =>
    rw [window_succ, window_succ] at hs
    have h0 := hq 0 (by omega)
    have hmod : u 0 % 4 = v 0 % 4 := by omega
    have huv : u 0 = v 0 := by omega
    have ht : window 4 m (fun i => u (i+1)) = window 4 m (fun i => v (i+1)) := by omega
    have hh := ih (fun i => u (i+1)) (fun i => v (i+1)) ht
      (by intro i hi; exact hq (i+1) (by omega))
    intro i hi
    cases i with
    | zero => exact huv
    | succ i => exact hh i (by omega)

/-- Quotient digits give at most two choices at each non-top coordinate. -/
theorem count_upper (k m n : ℕ) (hk : k ≤ 6) (hn : n < 4 ^ (m + 1)) :
    count k 4 n ≤ 2 ^ m := by
  let f : Partitions k 4 n → (Fin m → Fin 2) :=
    fun a i => ⟨a.val i / 4, by have := a.property.1 i; omega⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hza := support_bound (by norm_num : 2 ≤ 4) hn a.val a.property.2
    have hzb := support_bound (by norm_num : 2 ≤ 4) hn b.val b.property.2
    have hs : window 4 (m+1) a.val = window 4 (m+1) b.val := by
      rw [← weight_window 4 (m+1) a.val hza, ← weight_window 4 (m+1) b.val hzb,
        a.property.2, b.property.2]
    have htop (c : Partitions k 4 n) : c.val m / 4 = 0 := by
      have ht := term_le_weight 4 c.val m
      rw [c.property.2, pow_succ] at hn ht ⊢
      have hp : 0 < 4 ^ m := by positivity
      have : c.val m < 4 := by nlinarith
      omega
    have heq := quotient_injective (m+1) a.val b.val hs (by
      intro i hi
      by_cases him : i < m
      · exact congrArg Fin.val (congrFun hab ⟨i, him⟩)
      · have : i = m := by omega
        subst i
        rw [htop a, htop b])
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    by_cases hi : i < m+1
    · exact heq i hi
    · rw [hza i (by omega), hzb i (by omega)]
  have hcard := Nat.card_le_card_of_injective f hinj
  simpa [count, Nat.card_fun] using hcard

private lemma count_square_le (k n : ℕ) (hk : k ≤ 6) (hn : 1 ≤ n) :
    (count k 4 n) ^ 2 ≤ n := by
  have hu := count_upper k (Nat.log 4 n) n hk (Nat.lt_pow_succ_log_self (by norm_num) n)
  have hl : 4 ^ Nat.log 4 n ≤ n := Nat.pow_log_le_self 4 (by omega)
  have hp : (2 ^ Nat.log 4 n) ^ 2 = 4 ^ Nat.log 4 n := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  calc
    (count k 4 n) ^ 2 ≤ (2 ^ Nat.log 4 n) ^ 2 := Nat.pow_le_pow_left hu 2
    _ = 4 ^ Nat.log 4 n := hp
    _ ≤ n := hl

end

end D5.S1.Digit.CoonsAdjacentGrowthRefutation
