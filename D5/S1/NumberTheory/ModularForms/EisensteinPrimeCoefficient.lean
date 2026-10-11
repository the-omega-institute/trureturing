/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Prime coefficients of Eisenstein series

The classical bridge from Eisenstein q-expansions to Hecke eigenvalues starts with
the divisor sum at a prime.  Mathlib already supplies the analytic q-expansion and
the arithmetic-function API; this file records the coefficient calculation in a
form that can be consumed by a later Hecke-action formalization.
-/

open scoped ArithmeticFunction.sigma

open ArithmeticFunction
open ModularForm
open ModularFormClass
open EisensteinSeries
open UpperHalfPlane

namespace D5.S1.NumberTheory.ModularForms

theorem eisenstein_qExpansion_coeff_prime {k p : ℕ} (hk : 3 ≤ k) (hk2 : Even k)
    (hp : p.Prime) :
    (qExpansion 1 (E hk)).coeff p =
      -(2 * k / bernoulli k : ℂ) * (1 + (p : ℂ) ^ (k - 1)) := by
  have hs : σ (k - 1) p = 1 + p ^ (k - 1) := by
    rw [ArithmeticFunction.sigma_apply, hp.divisors, Finset.sum_insert]
    · simp
    · simpa using hp.ne_one.symm
  rw [EisensteinSeries.E_qExpansion_coeff hk hk2]
  simp [hp.ne_zero, hs]

theorem eisenstein_qExpansion_coeff_prime_mul {k p n : ℕ} (hk : 3 ≤ k) (hk2 : Even k)
    (hp : p.Prime) (hcop : p.Coprime n) :
    (qExpansion 1 (E hk)).coeff (p * n) =
      -(2 * k / bernoulli k : ℂ) *
        ((1 + (p : ℂ) ^ (k - 1)) * (σ (k - 1) n)) := by
  have hn : n ≠ 0 := by
    intro hn
    subst n
    have hcop' : p = 1 := by simpa only [Nat.coprime_zero_right] using hcop
    exact hp.ne_one hcop'
  have hpn : p * n ≠ 0 := mul_ne_zero hp.ne_zero hn
  have hs : σ (k - 1) p = 1 + p ^ (k - 1) := by
    rw [ArithmeticFunction.sigma_apply, hp.divisors, Finset.sum_insert]
    · simp
    · simpa using hp.ne_one.symm
  have hmul : σ (k - 1) (p * n) = σ (k - 1) p * σ (k - 1) n :=
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  rw [EisensteinSeries.E_qExpansion_coeff hk hk2]
  simp [hpn, hmul, hs, mul_left_comm, mul_comm]

end D5.S1.NumberTheory.ModularForms

#print axioms D5.S1.NumberTheory.ModularForms.eisenstein_qExpansion_coeff_prime
#print axioms D5.S1.NumberTheory.ModularForms.eisenstein_qExpansion_coeff_prime_mul
