/- GID: D5/S3/Arith/FactorialRatio/BalaA295462Quotient
   generality: I
   mirror-B: D5/B/S3/Arith/FactorialRatio/BalaA295462Quotient
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: The A295462 quotient over (6n+1)(10n+1) is a positive integer of the same parity. -/

import D5.S3.Arith.FactorialRatio.BalaA295462Parity

/-! # The reduced A295462 quotient

For every natural `n`, the rational number
`(15n)! (2n)! / ((10n)! (6n)! n! (6n+1) (10n+1))` is a positive integer, and it is odd
exactly when every two occupied binary positions of `n` differ by at least four.
-/

namespace D5.S3.Arith.FactorialRatio.BalaA295462Quotient

open D5.S3.Arith.FactorialRatio.BalaA295462Parity
open scoped BigOperators

private lemma fact_dvd (a1 a2 b1 b2 b3 : ℕ)
    (h : ∀ q : ℕ, 2 ≤ q → b1 / q + b2 / q + b3 / q ≤ a1 / q + a2 / q) :
    b1.factorial * b2.factorial * b3.factorial ∣ a1.factorial * a2.factorial := by
  have hne1 : b1.factorial * b2.factorial * b3.factorial ≠ 0 := by positivity
  have hne2 : a1.factorial * a2.factorial ≠ 0 := by positivity
  apply (Nat.factorization_prime_le_iff_dvd hne1 hne2).mp
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
    padicValNat.mul (by positivity) (by positivity),
    padicValNat.mul (by positivity) (by positivity),
    padicValNat.mul (by positivity) (by positivity)]
  set B := a1 + a2 + b1 + b2 + b3 + 1
  have vf (x : ℕ) (hx : x < B) :
      padicValNat p x.factorial = ∑ j ∈ Finset.Ico 1 B, x / p ^ j :=
    padicValNat_factorial (lt_of_le_of_lt (Nat.log_le_self p x) hx)
  rw [vf a1 (by omega), vf a2 (by omega), vf b1 (by omega), vf b2 (by omega),
    vf b3 (by omega), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have hj1 : j ≠ 0 := by
    have := (Finset.mem_Ico.mp hj).1
    omega
  exact h (p ^ j) (le_trans hp.two_le (Nat.le_self_pow hj1 p))

private lemma floor_six (r q : ℕ) (hq : 2 ≤ q) (hr : r < q) :
    10 * r / q + (6 * r + 1) / q + r / q ≤ 15 * r / q + 2 * r / q := by
  have hq0 : 0 < q := by omega
  have g15 := OeisA347854BalaHalfIndexIntegral.grid_floor 30 15 2 r q hq0 (by decide) (by decide)
  have g2 := OeisA347854BalaHalfIndexIntegral.grid_floor 30 2 15 r q hq0 (by decide) (by decide)
  have g10 := OeisA347854BalaHalfIndexIntegral.grid_floor 30 10 3 r q hq0 (by decide) (by decide)
  have g6 := OeisA347854BalaHalfIndexIntegral.grid_floor 30 6 5 r q hq0 (by decide) (by decide)
  have hb : 30 * r / q < 30 := (Nat.div_lt_iff_lt_mul hq0).mpr (by omega)
  rw [g15, g2, g10, Nat.div_eq_of_lt hr]
  by_cases hd : q ∣ 6 * r + 1
  · obtain ⟨t, ht⟩ := hd
    have hqt : (6 * r + 1) / q = t := by rw [ht, Nat.mul_div_cancel_left t hq0]
    have ht5 : t ≤ 5 := by
      by_contra h
      have : q * 6 ≤ q * t := Nat.mul_le_mul_left q (by omega)
      omega
    have hj : 30 * r / q = 5 * t - 1 := by
      apply Nat.div_eq_of_lt_le <;> interval_cases t <;> omega
    rw [hqt, hj]
    interval_cases t <;> omega
  · rw [Nat.succ_div_of_not_dvd hd, g6]
    generalize 30 * r / q = j at *
    omega

private lemma floor_ten (r q : ℕ) (hq : 2 ≤ q) (hr : r < q) :
    (10 * r + 1) / q + 6 * r / q + r / q ≤ 15 * r / q + 2 * r / q := by
  have hq0 : 0 < q := by omega
  have g15 := OeisA347854BalaHalfIndexIntegral.grid_floor 30 15 2 r q hq0 (by decide) (by decide)
  have g2 := OeisA347854BalaHalfIndexIntegral.grid_floor 30 2 15 r q hq0 (by decide) (by decide)
  have g10 := OeisA347854BalaHalfIndexIntegral.grid_floor 30 10 3 r q hq0 (by decide) (by decide)
  have g6 := OeisA347854BalaHalfIndexIntegral.grid_floor 30 6 5 r q hq0 (by decide) (by decide)
  have hb : 30 * r / q < 30 := (Nat.div_lt_iff_lt_mul hq0).mpr (by omega)
  rw [g15, g2, g6, Nat.div_eq_of_lt hr]
  by_cases hd : q ∣ 10 * r + 1
  · obtain ⟨t, ht⟩ := hd
    have hqt : (10 * r + 1) / q = t := by rw [ht, Nat.mul_div_cancel_left t hq0]
    have ht9 : t ≤ 9 := by
      by_contra h
      have : q * 10 ≤ q * t := Nat.mul_le_mul_left q (by omega)
      omega
    have hj : 30 * r / q = 3 * t - 1 := by
      apply Nat.div_eq_of_lt_le <;> interval_cases t <;> omega
    rw [hqt, hj]
    interval_cases t <;> omega
  · rw [Nat.succ_div_of_not_dvd hd, g10]
    generalize 30 * r / q = j at *
    omega

private lemma split_div (c n q : ℕ) (hq : 0 < q) :
    (c * n + 1) / q = c * (n / q) + (c * (n % q) + 1) / q := by
  have h : c * n + 1 = (c * (n % q) + 1) + q * (c * (n / q)) := by
    calc c * n + 1 = c * (q * (n / q) + n % q) + 1 := by rw [Nat.div_add_mod]
      _ = (c * (n % q) + 1) + q * (c * (n / q)) := by ring
  rw [h, Nat.add_mul_div_left _ _ hq]
  ring

private lemma floor_six_all (n q : ℕ) (hq : 2 ≤ q) :
    10 * n / q + (6 * n + 1) / q + n / q ≤ 15 * n / q + 2 * n / q := by
  have hq0 : 0 < q := by omega
  have h1 := OeisA347854BalaHalfIndexIntegral.mul_div_reduce 15 n q hq0
  have h2 := OeisA347854BalaHalfIndexIntegral.mul_div_reduce 2 n q hq0
  have h3 := OeisA347854BalaHalfIndexIntegral.mul_div_reduce 10 n q hq0
  have h4 := split_div 6 n q hq0
  have hz : n % q / q = 0 := Nat.div_eq_of_lt (Nat.mod_lt n hq0)
  have hr := floor_six (n % q) q hq (Nat.mod_lt n hq0)
  rw [h1, h2, h3, h4]
  rw [hz] at hr
  omega

private lemma floor_ten_all (n q : ℕ) (hq : 2 ≤ q) :
    (10 * n + 1) / q + 6 * n / q + n / q ≤ 15 * n / q + 2 * n / q := by
  have hq0 : 0 < q := by omega
  have h1 := OeisA347854BalaHalfIndexIntegral.mul_div_reduce 15 n q hq0
  have h2 := OeisA347854BalaHalfIndexIntegral.mul_div_reduce 2 n q hq0
  have h3 := OeisA347854BalaHalfIndexIntegral.mul_div_reduce 6 n q hq0
  have h4 := split_div 10 n q hq0
  have hz : n % q / q = 0 := Nat.div_eq_of_lt (Nat.mod_lt n hq0)
  have hr := floor_ten (n % q) q hq (Nat.mod_lt n hq0)
  rw [h1, h2, h3, h4]
  rw [hz] at hr
  omega

private lemma coprime_six_ten (n : ℕ) : Nat.Coprime (6 * n + 1) (10 * n + 1) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  set d := Nat.gcd (6 * n + 1) (10 * n + 1)
  have h1 : d ∣ 6 * n + 1 := Nat.gcd_dvd_left _ _
  have h2 : d ∣ 10 * n + 1 := Nat.gcd_dvd_right _ _
  have h3 : d ∣ 5 * (6 * n + 1) - 3 * (10 * n + 1) :=
    Nat.dvd_sub (dvd_mul_of_dvd_right h1 5) (dvd_mul_of_dvd_right h2 3)
  have h4 : 5 * (6 * n + 1) - 3 * (10 * n + 1) = 2 := by omega
  rw [h4] at h3
  have hle : d ≤ 2 := Nat.le_of_dvd (by norm_num) h3
  obtain ⟨c, hc⟩ := h1
  interval_cases d <;> omega

/-- For every natural `n`, dividing the A295462 factorial quotient by `(6n+1)(10n+1)`
gives a positive integer, which is odd exactly when the binary positions of `n` are
four-separated. -/
theorem reduced_quotient (n : ℕ) :
    ∃ b : ℕ, 0 < b ∧ a n / ((6 * (n : ℚ) + 1) * (10 * (n : ℚ) + 1)) = (b : ℚ) ∧
      (Odd b ↔ spacedBits n) := by
  obtain ⟨m, ham, hodd⟩ := result n
  set D := (10 * n).factorial * (6 * n).factorial * n.factorial
  have hD : D ≠ 0 := by positivity
  have heq : (15 * n).factorial * (2 * n).factorial = D * m := by
    have hq : ((15 * n).factorial : ℚ) * ((2 * n).factorial : ℚ) = (D : ℚ) * (m : ℚ) := by
      have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
      rw [← ham]
      unfold a
      simp only [D, Nat.cast_mul]
      field_simp
    exact_mod_cast hq
  have hm : m ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at heq
    exact (by positivity : (15 * n).factorial * (2 * n).factorial ≠ 0) heq
  have h6 : 6 * n + 1 ∣ m := by
    have hf := fact_dvd (15 * n) (2 * n) (10 * n) (6 * n + 1) n (floor_six_all n)
    rw [Nat.factorial_succ, heq] at hf
    have : D * (6 * n + 1) ∣ D * m := by
      have he : (10 * n).factorial * ((6 * n + 1) * (6 * n).factorial) * n.factorial =
          D * (6 * n + 1) := by simp only [D]; ring
      rwa [he] at hf
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hD) this
  have h10 : 10 * n + 1 ∣ m := by
    have hf := fact_dvd (15 * n) (2 * n) (10 * n + 1) (6 * n) n (floor_ten_all n)
    rw [Nat.factorial_succ, heq] at hf
    have : D * (10 * n + 1) ∣ D * m := by
      have he : (10 * n + 1) * (10 * n).factorial * (6 * n).factorial * n.factorial =
          D * (10 * n + 1) := by simp only [D]; ring
      rwa [he] at hf
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hD) this
  obtain ⟨b, hb⟩ := (coprime_six_ten n).mul_dvd_of_dvd_of_dvd h6 h10
  refine ⟨b, ?_, ?_, ?_⟩
  · apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, mul_zero] at hb
    exact hm hb
  · rw [ham, hb]
    push_cast
    have h1 : (6 * (n : ℚ) + 1) ≠ 0 := by positivity
    have h2 : (10 * (n : ℚ) + 1) ≠ 0 := by positivity
    field_simp
  · rw [← hodd, hb, Nat.odd_mul, Nat.odd_mul]
    have o6 : Odd (6 * n + 1) := ⟨3 * n, by ring⟩
    have o10 : Odd (10 * n + 1) := ⟨5 * n, by ring⟩
    simp [o6, o10]

end D5.S3.Arith.FactorialRatio.BalaA295462Quotient
