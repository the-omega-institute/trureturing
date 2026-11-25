/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/Reduction
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/MakowskiSchinzel/Reduction
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: Minimal odd counterexamples and radical ratio monotonicity. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.FactorisationProperties
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic

/-! Divisor-closed minimality and radical lifting. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.MakowskiSchinzel

open Finset UniqueFactorizationMonoid

/-- The sigma-totient ratio, with value zero at zero. -/
def alpha (n : ℕ) : ℚ := (ArithmeticFunction.sigma 1 n.totient : ℚ) / n

/-- The non-Fermat odd prime support; multiplicities are discarded. -/
noncomputable def nonFermatFactors (n : ℕ) : Finset ℕ := by
  classical
  exact n.primeFactors.filter fun q => q ≠ 2 ∧ ¬∃ k : ℕ, q - 1 = 2 ^ k

/-- Number of non-Fermat odd prime factors. -/
noncomputable def eta (n : ℕ) : ℕ := (nonFermatFactors n).card

/-- The finite reciprocal geometric factor at a prime. -/
def geom (r k : ℕ) : ℚ := ∑ j ∈ range (k + 1), (r : ℚ)⁻¹ ^ j

theorem alpha_factorization (n : ℕ) :
    alpha n = n.totient.abundancyIndex *
      ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) := by
  by_cases hn : n = 0
  · simp [hn, alpha, Nat.abundancyIndex]
  have hphi : (n.totient : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  rw [alpha, Nat.abundancyIndex, ← ArithmeticFunction.sigma_one_apply]
  apply (div_eq_iff hnq).mpr
  rw [mul_assoc, mul_comm (∏ p ∈ n.primeFactors, _) (n : ℚ),
    ← Nat.totient_eq_mul_prod_factors, div_mul_cancel₀ _ hphi]

/-- Taking the radical cannot increase the normalized sigma-totient ratio. -/
theorem alpha_radical_le {n : ℕ} (hn : n ≠ 0) : alpha (radical n) ≤ alpha n := by
  rw [alpha_factorization (radical n), alpha_factorization n,
    Nat.primeFactors_radical]
  apply mul_le_mul_of_nonneg_right
  · exact Nat.abundancyIndex_le_of_dvd
      (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
      (Nat.totient_dvd_of_dvd radical_dvd_self)
  · apply prod_nonneg
    intro p hp
    have hp1 : (1 : ℚ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hp1)

#print axioms alpha_radical_le

/-- At an odd integer, adjoining the prime two halves the ratio exactly. -/
theorem alpha_two_mul {m : ℕ} (hm : Odd m) : alpha (2 * m) = alpha m / 2 := by
  simp only [alpha, Nat.totient_two_mul_of_odd hm, Nat.cast_mul, Nat.cast_ofNat]
  ring


/-- A minimal odd counterexample in any divisor-closed class is squarefree. -/
theorem exists_minimal_odd_counterexample (P : ℕ → Prop)
    (hclosed : ∀ {a b : ℕ}, Odd b → a ∣ b → P b → P a)
    (hex : ∃ n : ℕ, Odd n ∧ P n ∧ alpha n < 1) :
    ∃ m : ℕ, Odd m ∧ P m ∧ Squarefree m ∧ alpha m < 1 ∧
      (∀ d : ℕ, d ∣ m → d < m → 1 ≤ alpha d) ∧
      (∀ d : ℕ, Odd d → P d → d < m → 1 ≤ alpha d) := by
  classical
  let m := Nat.find hex
  have hm := Nat.find_spec hex
  change Odd m ∧ P m ∧ alpha m < 1 at hm
  have hm0 : m ≠ 0 := by obtain ⟨k, hk⟩ := hm.1; omega
  have hmin (d : ℕ) (hd : d ∣ m) (hlt : d < m) : 1 ≤ alpha d := by
    by_contra h
    have hdodd := hm.1.of_dvd_nat hd
    have hc : Odd d ∧ P d ∧ alpha d < 1 :=
      ⟨hdodd, hclosed hm.1 hd hm.2.1, lt_of_not_ge h⟩
    have := Nat.find_min' hex hc
    change m ≤ d at this
    omega
  have hrad : radical m = m := by
    have hle := Nat.radical_le_self_iff.mpr hm0
    by_contra hne
    have hlt : radical m < m := lt_of_le_of_ne hle hne
    have hge := hmin _ radical_dvd_self hlt
    have hlow := alpha_radical_le hm0
    linarith [hm.2.2]
  refine ⟨m, hm.1, hm.2.1, hrad ▸ squarefree_radical, hm.2.2, hmin, ?_⟩
  intro d hdo hP hlt
  by_contra h
  have hh := Nat.find_min' hex ⟨hdo, hP, lt_of_not_ge h⟩
  change m ≤ d at hh
  omega

#print axioms exists_minimal_odd_counterexample

end D5.S3.Arith.MakowskiSchinzel
