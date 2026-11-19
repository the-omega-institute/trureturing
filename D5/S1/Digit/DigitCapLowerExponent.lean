/- GID: D5/S1/Digit/DigitCapLowerExponent
   generality: I
   mirror-B: D5/B/S1/Digit/DigitCapLowerExponent
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Below twice the radix, ell^s-1 has one bounded-digit representation and the lower exponent is zero. -/

import D5.S1.Digit.CoonsAdjacentGrowthRefutation

/-! # Singleton representations and the zero lower growth exponent

For a radix `ell ≥ 2` and a digit cap `k` with `ell - 1 ≤ k ≤ 2 * ell - 2`, the input
`ell ^ s - 1` has exactly one bounded-digit representation, namely the digit `ell - 1`
at each of the positions `0, ..., s - 1`. Along these inputs the logarithmic readout
vanishes, while it is nonnegative everywhere from two on, so the extended-real lower
limit of the readout is zero.
-/

namespace D5.S1.Digit.DigitCapLowerExponent

open D5.S1.Digit.CoonsAdjacentGrowthRefutation
open scoped BigOperators

noncomputable section

/-- The literal extended-real every-tail lower limit of the logarithmic readout. -/
def lowerExponent (k ell : ℕ) : EReal :=
  ⨆ (N : ℕ) (_ : 2 ≤ N), ⨅ (n : ℕ) (_ : N ≤ n), (readout k ell n : EReal)

private def window (ell m : ℕ) (u : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, u i * ell ^ i

private lemma window_succ (ell m : ℕ) (u : ℕ → ℕ) :
    window ell (m + 1) u = u 0 + ell * window ell m (fun i => u (i + 1)) := by
  simp only [window, Finset.sum_range_succ', pow_zero, mul_one, pow_succ,
    Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma weight_window (ell m : ℕ) (a : ℕ →₀ ℕ)
    (h : ∀ i, m ≤ i → a i = 0) : weight ell a = window ell m a := by
  unfold weight window
  apply Finsupp.sum_of_support_subset
  · intro i hi
    simp only [Finset.mem_range]
    by_contra hn
    exact Finsupp.mem_support_iff.mp hi (h i (by omega))
  · simp

private lemma term_le_weight (ell : ℕ) (a : ℕ →₀ ℕ) (i : ℕ) :
    a i * ell ^ i ≤ weight ell a := by
  by_cases hi : a i = 0
  · simp [hi]
  · unfold weight Finsupp.sum
    exact Finset.single_le_sum (f := fun j => a j * ell ^ j)
      (fun j _ => Nat.zero_le (a j * ell ^ j)) (Finsupp.mem_support_iff.mpr hi)

private lemma support_bound {ell n m : ℕ} (hell : 2 ≤ ell) (hn : n < ell ^ m)
    (a : ℕ →₀ ℕ) (ha : weight ell a = n) : ∀ i, m ≤ i → a i = 0 := by
  intro i hi
  by_contra h
  have hp : ell ^ m ≤ ell ^ i := Nat.pow_le_pow_right (by omega) hi
  have ht := term_le_weight ell a i
  have : 1 ≤ a i := by omega
  rw [ha] at ht
  nlinarith

private lemma window_top (ell s : ℕ) (hell : 1 ≤ ell) :
    window ell s (fun _ => ell - 1) + 1 = ell ^ s := by
  induction s with
  | zero => simp [window]
  | succ s ih =>
    rw [window_succ, pow_succ]
    have h : ell * window ell s (fun _ => ell - 1) + ell = ell * ell ^ s := by
      rw [← ih, Nat.mul_add, Nat.mul_one]
    have h1 : ell - 1 + 1 = ell := Nat.sub_add_cancel hell
    nlinarith

private lemma digits_forced (ell : ℕ) (hell : 1 ≤ ell) (s : ℕ) (u : ℕ → ℕ)
    (hu : ∀ i, i < s → u i ≤ 2 * ell - 2)
    (hs : window ell s u = window ell s (fun _ => ell - 1)) :
    ∀ i, i < s → u i = ell - 1 := by
  induction s generalizing u with
  | zero => simp
  | succ s ih =>
    rw [window_succ, window_succ] at hs
    have hmod : u 0 % ell = (ell - 1) % ell := by
      have h := congrArg (· % ell) hs
      simpa only [Nat.add_mul_mod_self_left] using h
    have hlt : ell - 1 < ell := by omega
    rw [Nat.mod_eq_of_lt hlt] at hmod
    have h0 : u 0 = ell - 1 := by
      have hd := Nat.div_add_mod (u 0) ell
      have hb := hu 0 (by omega)
      rcases Nat.eq_zero_or_pos (u 0 / ell) with hq | hq
      · rw [hq, hmod] at hd
        omega
      · have : ell * 1 ≤ ell * (u 0 / ell) := Nat.mul_le_mul_left ell hq
        omega
    have ht : window ell s (fun i => u (i + 1)) = window ell s (fun _ => ell - 1) := by
      rw [h0] at hs
      exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_left_cancel hs)
    have hh := ih (fun i => u (i + 1)) (by intro i hi; exact hu (i + 1) (by omega)) ht
    intro i hi
    cases i with
    | zero => exact h0
    | succ i => exact hh i (by omega)

/-- For every radix `ell ≥ 2`, every digit cap `ell - 1 ≤ k ≤ 2 * ell - 2` and every `s`,
the input `ell ^ s - 1` has exactly one bounded-digit representation. -/
theorem count_pow_sub_one (ell k s : ℕ) (hell : 2 ≤ ell) (hk : ell - 1 ≤ k)
    (hk' : k ≤ 2 * ell - 2) : count k ell (ell ^ s - 1) = 1 := by
  have hpos : 1 ≤ ell ^ s := Nat.one_le_pow _ _ (by omega)
  have hn : ell ^ s - 1 < ell ^ s := by omega
  have hsub : Subsingleton (Partitions k ell (ell ^ s - 1)) := by
    constructor
    intro a b
    have hza := support_bound hell hn a.val a.property.2
    have hzb := support_bound hell hn b.val b.property.2
    have hval : window ell s (fun _ => ell - 1) = ell ^ s - 1 := by
      have := window_top ell s (by omega)
      omega
    have hwa : window ell s a.val = window ell s (fun _ => ell - 1) := by
      rw [← weight_window ell s a.val hza, a.property.2, hval]
    have hwb : window ell s b.val = window ell s (fun _ => ell - 1) := by
      rw [← weight_window ell s b.val hzb, b.property.2, hval]
    have ha := digits_forced ell (by omega) s a.val
      (fun i _ => le_trans (a.property.1 i) hk') hwa
    have hb := digits_forced ell (by omega) s b.val
      (fun i _ => le_trans (b.property.1 i) hk') hwb
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    by_cases hi : i < s
    · rw [ha i hi, hb i hi]
    · rw [hza i (by omega), hzb i (by omega)]
  have hcount := count_positive k ell (ell ^ s - 1) hell hk
  have := partitions_finite k ell (ell ^ s - 1) hell
  have hne : Nonempty (Partitions k ell (ell ^ s - 1)) := (Nat.card_pos_iff.mp hcount).1
  exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, hne⟩

private lemma readout_nonneg (k ell n : ℕ) (hell : 2 ≤ ell) (hk : ell - 1 ≤ k)
    (hn : 2 ≤ n) : 0 ≤ readout k ell n := by
  unfold readout
  have hc : (1 : ℝ) ≤ (count k ell n : ℝ) := by
    exact_mod_cast count_positive k ell n hell hk
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  exact div_nonneg (Real.log_nonneg hc) hl.le

/-- For every radix `ell ≥ 2` and every digit cap `ell - 1 ≤ k ≤ 2 * ell - 2`,
the extended-real lower limit of `log (count k ell n) / log n` is zero. -/
theorem lowerExponent_eq_zero (ell k : ℕ) (hell : 2 ≤ ell) (hk : ell - 1 ≤ k)
    (hk' : k ≤ 2 * ell - 2) : lowerExponent k ell = 0 := by
  have htail : ∀ N : ℕ, 2 ≤ N →
      ⨅ (n : ℕ) (_ : N ≤ n), (readout k ell n : EReal) = 0 := by
    intro N hN
    apply le_antisymm
    · have hlarge : N ≤ ell ^ (N + 1) - 1 := by
        have h1 : N + 1 < ell ^ (N + 1) :=
          lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_left hell _)
        omega
      apply iInf₂_le_of_le (ell ^ (N + 1) - 1) hlarge
      have hz : readout k ell (ell ^ (N + 1) - 1) = 0 := by
        simp [readout, count_pow_sub_one ell k (N + 1) hell hk hk']
      rw [hz]
      simp
    · apply le_iInf₂
      intro n hn
      exact EReal.coe_nonneg.mpr (readout_nonneg k ell n hell hk (by omega))
  unfold lowerExponent
  apply le_antisymm
  · exact iSup₂_le fun N hN => le_of_eq (htail N hN)
  · exact le_iSup₂_of_le 2 le_rfl (le_of_eq (htail 2 le_rfl).symm)

end

end D5.S1.Digit.DigitCapLowerExponent
