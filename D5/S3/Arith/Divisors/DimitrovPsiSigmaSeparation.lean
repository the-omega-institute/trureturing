/- GID: D5/S3/Arith/Divisors/DimitrovPsiSigmaSeparation
   generality: I
   mirror-B: D5/B/S3/Arith/Divisors/DimitrovPsiSigmaSeparation
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: For n ≥ 2, (ψ+σ)/(φ+σ) ≥ (n+1)/n, with equality exactly at the primes. -/

import D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5

/-! # Prime separation for the ratio `(ψ + σ) / (φ + σ)`

For every `n ≥ 2`, with `u = φ(n)`, `v = ψ(n)` (Dedekind psi) and `w = σ(n)`, the ratio
`(v + w) / (u + w)` is at least `(n + 1) / n`, and equality holds exactly when `n` is prime.
-/

namespace D5.S3.Arith.Divisors.DimitrovPsiSigmaSeparation

open D5.S3.Arith.Divisors.OeisA344695GcdSigmaPsiPrimes
open D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5

/-- The `n / p` multiples of the least prime factor `p` below `n` are not coprime to `n`. -/
private lemma totient_add_le {n : ℕ} (hn : 2 ≤ n) : Nat.totient n + n / n.minFac ≤ n := by
  classical
  set p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  set m := n / p
  have hpm : p * m = n := Nat.mul_div_cancel' (Nat.minFac_dvd n)
  rw [Nat.totient_eq_card_coprime]
  have hdisj : Disjoint ((Finset.range n).filter n.Coprime)
      ((Finset.range m).image (· * p)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image] at hx hx'
    obtain ⟨k, _, rfl⟩ := hx'
    have hdvd : p ∣ Nat.gcd n (k * p) := Nat.dvd_gcd (Nat.minFac_dvd n) (dvd_mul_left p k)
    rw [hx.2] at hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd)
  have hsub : (Finset.range n).filter n.Coprime ∪ (Finset.range m).image (· * p) ⊆
      Finset.range n := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_image] at hx ⊢
    rcases hx with hx | ⟨k, hk, rfl⟩
    · exact hx.1
    · have := Nat.mul_lt_mul_of_pos_right hk hp.pos
      rw [← hpm, mul_comm p m]
      exact this
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_range,
    Finset.card_image_of_injective _ (mul_left_injective₀ hp.ne_zero), Finset.card_range] at hcard
  exact hcard

/-- Every proper divisor of `n` is at most `n / p`, so `σ(n) ≤ n + (n / p)^2`. -/
private lemma sigma_le {n : ℕ} (hn : 2 ≤ n) :
    ArithmeticFunction.sigma 1 n ≤ n + n / n.minFac * (n / n.minFac) := by
  classical
  set p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  set m := n / p
  have hpm : p * m = n := Nat.mul_div_cancel' (Nat.minFac_dvd n)
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have hsub : n.properDivisors ⊆ Finset.Icc 1 m := by
    intro d hd
    rw [Nat.mem_properDivisors] at hd
    obtain ⟨⟨e, he⟩, hdn⟩ := hd
    have he2 : 2 ≤ e := by
      rcases e with _ | _ | e
      · omega
      · omega
      · omega
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have hpe : p ≤ e := Nat.minFac_le_of_dvd he2 ⟨d, by rw [mul_comm]; exact he⟩
    rw [Finset.mem_Icc]
    refine ⟨hd0, ?_⟩
    have h1 : p * d ≤ p * m := by
      rw [hpm, he, mul_comm p d]
      exact Nat.mul_le_mul_left d hpe
    exact Nat.le_of_mul_le_mul_left h1 hp.pos
  have hsum : ∑ d ∈ n.properDivisors, d ≤ ∑ _d ∈ n.properDivisors, m :=
    Finset.sum_le_sum (fun d hd => (Finset.mem_Icc.mp (hsub hd)).2)
  rw [Finset.sum_const, smul_eq_mul] at hsum
  have hcard : n.properDivisors.card ≤ m := by
    simpa using Finset.card_le_card hsub
  have := Nat.mul_le_mul_right m hcard
  omega

/-- The integer form: `(n + 1) φ(n) + σ(n) ≤ n ψ(n)`, with equality exactly at primes. -/
private lemma key {n : ℕ} (hn : 2 ≤ n) :
    (n + 1) * Nat.totient n + ArithmeticFunction.sigma 1 n ≤ n * psi n ∧
    ((n + 1) * Nat.totient n + ArithmeticFunction.sigma 1 n = n * psi n ↔ n.Prime) := by
  by_cases hpr : n.Prime
  · have hpsi : psi n = n + 1 := by
      unfold psi
      rw [Nat.Prime.primeFactors hpr, Finset.prod_singleton, Finset.prod_singleton,
        Nat.div_self hpr.pos, one_mul]
    have hsig : ArithmeticFunction.sigma 1 n = n + 1 := by
      rw [ArithmeticFunction.sigma_one_apply, Nat.Prime.sum_divisors hpr]
    have htot : Nat.totient n = n - 1 := Nat.totient_prime hpr
    rw [hpsi, hsig, htot]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, hpr, iff_true]
    exact ⟨le_of_eq (by ring), by ring⟩
  · have aux : ∀ T Ψ S m r n : ℕ, n = m + r → T ≤ r → n + 1 ≤ Ψ → S ≤ n + m * m →
        2 ≤ m → m ≤ r → (n + 1) * T + S < n * Ψ := by
      intro T Ψ S m r n hn hT hΨ hS hm hr
      subst hn
      have h1 : 2 * r ≤ m * r := Nat.mul_le_mul_right r hm
      have h2 : (m + r + 1) * T ≤ (m + r + 1) * r := Nat.mul_le_mul_left _ hT
      have h3 : (m + r) * (m + r + 1) ≤ (m + r) * Ψ := Nat.mul_le_mul_left _ hΨ
      nlinarith
    have h1 := psi_ge hn
    have h2 := totient_add_le hn
    have h3 := sigma_le hn
    have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
    obtain ⟨m, hm⟩ := Nat.minFac_dvd n
    have hq : n / n.minFac = m :=
      Nat.div_eq_of_eq_mul_left hp.pos (by rw [mul_comm]; exact hm)
    rw [hq] at h2 h3
    have hm2 : 2 ≤ m := by
      rcases (by omega : m = 0 ∨ m = 1 ∨ 2 ≤ m) with h | h | h
      · rw [h, mul_zero] at hm; omega
      · rw [h, mul_one] at hm; exact absurd (hm ▸ hp) hpr
      · exact h
    have hmn : 2 * m ≤ n := by
      have := Nat.mul_le_mul_right m hp.two_le
      omega
    have hlt := aux (Nat.totient n) (psi n) (ArithmeticFunction.sigma 1 n) m (n - m) n
      (by omega) (by omega) h1 h3 hm2 (by omega)
    exact ⟨hlt.le, by simp only [hpr, iff_false]; omega⟩

/-- For every `n ≥ 2`, with `u = φ(n)`, `v = ψ(n)` and `w = σ(n)`,
`(v + w) / (u + w) ≥ (n + 1) / n`, with equality if and only if `n` is prime. -/
theorem separation (n : ℕ) (hn : 2 ≤ n) :
    ((n : ℝ) + 1) / n ≤
      ((psi n : ℝ) + ArithmeticFunction.sigma 1 n) /
        ((Nat.totient n : ℝ) + ArithmeticFunction.sigma 1 n) ∧
    (((psi n : ℝ) + ArithmeticFunction.sigma 1 n) /
        ((Nat.totient n : ℝ) + ArithmeticFunction.sigma 1 n) = ((n : ℝ) + 1) / n ↔
      n.Prime) := by
  obtain ⟨hle, hiff⟩ := key hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsig : (0 : ℝ) < ArithmeticFunction.sigma 1 n := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 n (by omega)
  have hden : (0 : ℝ) < (Nat.totient n : ℝ) + ArithmeticFunction.sigma 1 n := by positivity
  have hleR : ((n : ℝ) + 1) * Nat.totient n + ArithmeticFunction.sigma 1 n ≤
      (n : ℝ) * psi n := by exact_mod_cast hle
  constructor
  · rw [div_le_div_iff₀ hn0 hden]
    nlinarith
  · rw [div_eq_div_iff hden.ne' hn0.ne', ← hiff]
    constructor
    · intro h
      have : ((n : ℝ) + 1) * Nat.totient n + ArithmeticFunction.sigma 1 n = (n : ℝ) * psi n := by
        linarith
      exact_mod_cast this
    · intro h
      have : ((n : ℝ) + 1) * Nat.totient n + ArithmeticFunction.sigma 1 n = (n : ℝ) * psi n := by
        exact_mod_cast h
      linarith

end D5.S3.Arith.Divisors.DimitrovPsiSigmaSeparation
