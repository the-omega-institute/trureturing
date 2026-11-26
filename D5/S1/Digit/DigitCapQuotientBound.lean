/- GID: D5/S1/Digit/DigitCapQuotientBound
   generality: I
   mirror-B: D5/B/S1/Digit/DigitCapQuotientBound
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: A digit cap below q times the radix allows at most q^m representations below ell^(m+1). -/

import D5.S1.Digit.CoonsAdjacentGrowthRefutation

/-! # Quotient-digit bound for bounded-digit representations at every radix

For a radix `ell ≥ 2`, a digit cap `k ≤ q * ell - 1` and an input `n < ell ^ (m + 1)`,
the number of finitely supported digit functions `a` with `a i ≤ k` and weighted value
`n` is at most `q ^ m`. Each such function is determined by its quotients `a i / ell`
at the positions `i < m`, and every quotient is smaller than `q`.
-/

namespace D5.S1.Digit.DigitCapQuotientBound

open D5.S1.Digit.CoonsAdjacentGrowthRefutation
open scoped BigOperators

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

private lemma quotient_injective (ell : ℕ) (hell : 0 < ell) (m : ℕ) (u v : ℕ → ℕ)
    (hs : window ell m u = window ell m v)
    (hq : ∀ i, i < m → u i / ell = v i / ell) :
    ∀ i, i < m → u i = v i := by
  induction m generalizing u v with
  | zero => simp
  | succ m ih =>
    rw [window_succ, window_succ] at hs
    have h0 := hq 0 (by omega)
    have hmod : u 0 % ell = v 0 % ell := by
      have h := congrArg (· % ell) hs
      simpa only [Nat.add_mul_mod_self_left] using h
    have huv : u 0 = v 0 := by
      rw [← Nat.div_add_mod (u 0) ell, ← Nat.div_add_mod (v 0) ell, h0, hmod]
    have ht : window ell m (fun i => u (i + 1)) = window ell m (fun i => v (i + 1)) := by
      rw [huv] at hs
      exact Nat.eq_of_mul_eq_mul_left hell (Nat.add_left_cancel hs)
    have hh := ih (fun i => u (i + 1)) (fun i => v (i + 1)) ht
      (by intro i hi; exact hq (i + 1) (by omega))
    intro i hi
    cases i with
    | zero => exact huv
    | succ i => exact hh i (by omega)

/-- For every radix `ell ≥ 2`, every `q ≥ 1` and every digit cap `k ≤ q * ell - 1`,
an input below `ell ^ (m + 1)` has at most `q ^ m` bounded-digit representations. -/
theorem count_le_pow (ell q m k n : ℕ) (hell : 2 ≤ ell) (hq : 1 ≤ q)
    (hk : k ≤ q * ell - 1) (hn : n < ell ^ (m + 1)) :
    count k ell n ≤ q ^ m := by
  have hqe : 0 < q * ell := Nat.mul_pos (by omega) (by omega)
  let f : Partitions k ell n → (Fin m → Fin q) :=
    fun a i => ⟨a.val i / ell, by
      have h := a.property.1 i
      apply Nat.div_lt_of_lt_mul
      rw [Nat.mul_comm]
      omega⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hza := support_bound hell hn a.val a.property.2
    have hzb := support_bound hell hn b.val b.property.2
    have hs : window ell (m + 1) a.val = window ell (m + 1) b.val := by
      rw [← weight_window ell (m + 1) a.val hza, ← weight_window ell (m + 1) b.val hzb,
        a.property.2, b.property.2]
    have htop (c : Partitions k ell n) : c.val m / ell = 0 := by
      have ht := term_le_weight ell c.val m
      rw [c.property.2] at ht
      have hp : 0 < ell ^ m := by positivity
      have hlt : c.val m * ell ^ m < ell * ell ^ m := by
        calc c.val m * ell ^ m ≤ n := ht
          _ < ell ^ (m + 1) := hn
          _ = ell * ell ^ m := by rw [pow_succ, Nat.mul_comm]
      exact Nat.div_eq_of_lt (Nat.lt_of_mul_lt_mul_right hlt)
    have heq := quotient_injective ell (by omega) (m + 1) a.val b.val hs (by
      intro i hi
      by_cases him : i < m
      · exact congrArg Fin.val (congrFun hab ⟨i, him⟩)
      · have : i = m := by omega
        subst i
        rw [htop a, htop b])
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    by_cases hi : i < m + 1
    · exact heq i hi
    · rw [hza i (by omega), hzb i (by omega)]
  have hcard := Nat.card_le_card_of_injective f hinj
  simpa [count, Nat.card_fun] using hcard

end D5.S1.Digit.DigitCapQuotientBound
