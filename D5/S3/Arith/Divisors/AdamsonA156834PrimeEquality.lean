/- GID: D5/S3/Arith/Divisors/AdamsonA156834PrimeEquality
   generality: I
   mirror-B: D5/B/S3/Arith/Divisors/AdamsonA156834PrimeEquality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Adamson's A156834 equals its index exactly at primes greater than one. -/

/- proof_shape: a: bind-only; consumers=excess_identity, prime_equality, composite_strict, result.
   proof_shape: claim: bind-only; consumer=result.
   proof_shape: binomial_bounds: bind-only; consumers=prime_equality, composite_strict.
   proof_shape: excess_identity: bind-only; consumers=prime_equality, composite_strict.
   proof_shape: prime_equality: bind-only; consumer=result.
   proof_shape: composite_strict: bind-only; consumer=result.
   proof_shape: result: bind-only; consumer=none.
   escape_witness: none.
   admission_basis: open-problem-resolution (#23238; Proved).
   Direct frozen dependencies: none.
   The source's finite divisor sum defines a; claim retains the restriction 1 < n.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30277
-/

import Mathlib.Data.Nat.Totient

/-! # Adamson's totient-weighted prime-equality characterization -/

namespace D5.S3.Arith.Divisors.AdamsonA156834PrimeEquality

/-- OEIS A156834's explicit divisor-sum formula, for positive indices.
The extension at zero is unused by the source assertion. -/
def a (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, Nat.totient d * Nat.choose (d + n / d - 2) (d - 1)

/-- Adamson's OEIS A156834 conjecture, retaining the exclusion of one. -/
def claim : Prop :=
  ∀ n : ℕ, 1 < n → (a n = n ↔ Nat.Prime n)

private theorem binomial_bounds {n d : ℕ} (hd : d ∈ n.divisors) :
    0 < Nat.choose (d + n / d - 2) (d - 1) ∧
      (Nat.choose (d + n / d - 2) (d - 1) = 1 ↔ d = 1 ∨ d = n) := by
  have hdpos := Nat.pos_of_mem_divisors hd
  have hdle := Nat.divisor_le hd
  have hqpos := Nat.div_pos hdle hdpos
  have hmul := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
  constructor
  · exact Nat.choose_pos (by omega)
  · rw [Nat.choose_eq_one_iff]
    constructor
    · rintro (h | h)
      · left; omega
      · right
        have hq : n / d = 1 := by omega
        simpa [hq] using hmul
    · rintro (rfl | rfl)
      · simp
      · right
        rw [Nat.div_self hdpos]
        omega

private theorem excess_identity (n : ℕ) :
    (a n : ℤ) - n = ∑ d ∈ n.divisors,
      (Nat.totient d : ℤ) * ((Nat.choose (d + n / d - 2) (d - 1) : ℤ) - 1) := by
  simp only [a, Nat.cast_sum, Nat.cast_mul, mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [← Nat.cast_sum, Nat.sum_totient]

private theorem prime_equality {n : ℕ} (hn : Nat.Prime n) : a n = n := by
  have hz : (a n : ℤ) - n = 0 := by
    rw [excess_identity]
    apply Finset.sum_eq_zero
    intro d hd
    have hb := (binomial_bounds hd).2.mpr ((Nat.dvd_prime hn).mp (Nat.dvd_of_mem_divisors hd))
    simp [hb]
  exact_mod_cast (sub_eq_zero.mp hz)

private theorem composite_strict {n : ℕ} (hn : 1 < n) (hc : ¬ Nat.Prime n) : n < a n := by
  have hex : ∃ d, d ∣ n ∧ 1 < d ∧ d < n := by
    by_contra h
    apply hc
    apply Nat.prime_def_lt'.mpr
    refine ⟨hn, ?_⟩
    intro d hd hdn hdvd
    exact h ⟨d, hdvd, hd, hdn⟩
  obtain ⟨d, hdvd, hdgt, hdlt⟩ := hex
  have hmem : d ∈ n.divisors := Nat.mem_divisors.mpr ⟨hdvd, by omega⟩
  have hnonneg : ∀ e ∈ n.divisors, 0 ≤
      (Nat.totient e : ℤ) * ((Nat.choose (e + n / e - 2) (e - 1) : ℤ) - 1) := by
    intro e he
    apply mul_nonneg (Int.natCast_nonneg _)
    have h := (binomial_bounds he).1
    omega
  have hpositive : 0 <
      (Nat.totient d : ℤ) * ((Nat.choose (d + n / d - 2) (d - 1) : ℤ) - 1) := by
    have hp := Nat.totient_pos.mpr (Nat.pos_of_mem_divisors hmem)
    have hb := binomial_bounds hmem
    have hne : Nat.choose (d + n / d - 2) (d - 1) ≠ 1 := by
      intro h
      rcases hb.2.mp h with h | h <;> omega
    apply mul_pos (by exact_mod_cast hp)
    omega
  have htotal : 0 < (a n : ℤ) - n := by
    rw [excess_identity]
    exact lt_of_lt_of_le hpositive (Finset.single_le_sum hnonneg hmem)
  exact_mod_cast (sub_pos.mp htotal)

theorem result : claim := by
  intro n hn
  constructor
  · intro heq
    by_contra hc
    have hlt := composite_strict hn hc
    omega
  · exact prime_equality


end D5.S3.Arith.Divisors.AdamsonA156834PrimeEquality
