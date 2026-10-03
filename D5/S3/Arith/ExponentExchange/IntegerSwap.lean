/- GID: D5/S3/Arith/ExponentExchange/IntegerSwap
   generality: G
   mirror-B: D5/B/S3/Arith/ExponentExchange/IntegerSwap
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: []
   utility: none
   digest: Prime exponent exchange lowers the integer and raises normalized sigma. -/

import D5.S3.Arith.RobinExponentSwap
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.FieldSimp

/- Library-search audit trail (2026-09-07):
   1. D5 searches: reciprocalGeomSum, reciprocal_geom_sum_swap_strict, sigma/swap,
      factorization/swap, and ArithmeticFunction.sigma. RobinExponentSwap has exactly
      two public declarations (grep -nE '^(theorem|lemma|def|noncomputable def) ').
      Its real comparison is imported and applied. GoldenResourceObjectiveFactorization
      concerns logarithmic objectives, not an integer exchange certificate.
   2. Mathlib v4.33.0, db584cd6d46c92f209a44c0f1c829460d327499d: searched
      Data/Nat/Factorization, NumberTheory/ArithmeticFunction and FactorisationProperties.
      Reuse factorization_div, factorization_mul, Prime.factorization_pow,
      Prime.pow_dvd_iff_le_factorization, sigma_one_apply_prime_pow,
      isMultiplicative_sigma.map_mul_of_coprime, sigma_pos, and geometric-sum formulas.
      No complete prime-exponent exchange theorem found in this scope.
   3. Third-party Lean ecosystem: Tavily via NyxID, queries "Lean theorem prime exponent
      swap normalized divisor sum sigma superabundant factorization" and
      "site:github.com Lean superabundant exponent sigma swap". Returned elementary
      factorization documentation and unrelated results; no matching Lean declaration.
      This is not an exhaustive assertion about all external repositories.
-/

namespace D5.S3.Arith.ExponentExchange.IntegerSwap

open D5.S3.Arith.RobinExponentSwap

noncomputable section

theorem normalized_sigma_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (ArithmeticFunction.sigma 1 (p ^ a) : ℝ) / (p ^ a : ℕ) =
      reciprocalGeomSum p a := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  push_cast
  unfold reciprocalGeomSum
  rw [geom_sum_eq hp1, geom_sum_inv hp1 hp0]
  simp only [inv_pow, pow_succ]
  field_simp

theorem normalized_sigma_mul {u v : ℕ} (h : u.Coprime v) :
    (ArithmeticFunction.sigma 1 (u * v) : ℝ) / (u * v : ℕ) =
      ((ArithmeticFunction.sigma 1 u : ℝ) / u) *
        ((ArithmeticFunction.sigma 1 v : ℝ) / v) := by
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h]
  push_cast
  exact mul_div_mul_comm _ _ _ _

/-- The quotient by the two full prime powers is positive and coprime to their product. -/
private theorem two_prime_cofactor {m p q : ℕ} (hm : 1 ≤ m)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    let a := m.factorization p
    let b := m.factorization q
    let t := m / (p ^ a * q ^ b)
    1 ≤ t ∧ t.Coprime (p * q) ∧ m = t * p ^ a * q ^ b := by
  dsimp only
  have hm0 : m ≠ 0 := by omega
  have hc : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq.ne
  have hd : p ^ m.factorization p * q ^ m.factorization q ∣ m :=
    (hc.pow _ _).mul_dvd_of_dvd_of_dvd
      ((hp.pow_dvd_iff_le_factorization hm0).mpr le_rfl)
      ((hq.pow_dvd_iff_le_factorization hm0).mpr le_rfl)
  let t := m / (p ^ m.factorization p * q ^ m.factorization q)
  have ht : 0 < t := Nat.div_pos (Nat.le_of_dvd (by omega) hd)
    (Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _))
  have hfac : t.factorization = m.factorization -
      (p ^ m.factorization p * q ^ m.factorization q).factorization :=
    Nat.factorization_div hd
  have htp : t.factorization p = 0 := by
    rw [hfac, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero)
      (pow_ne_zero _ hq.ne_zero), hp.factorization_pow, hq.factorization_pow]
    simp [hpq.ne]
  have htq : t.factorization q = 0 := by
    rw [hfac, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero)
      (pow_ne_zero _ hq.ne_zero), hp.factorization_pow, hq.factorization_pow]
    simp [hpq.ne.symm]
  have hcp : t.Coprime p := (hp.coprime_iff_not_dvd.mpr (by
    rw [hp.dvd_iff_one_le_factorization ht.ne', htp]
    omega)).symm
  have hcq : t.Coprime q := (hq.coprime_iff_not_dvd.mpr (by
    rw [hq.dvd_iff_one_le_factorization ht.ne', htq]
    omega)).symm
  refine ⟨ht, hcp.mul_right hcq, ?_⟩
  simpa only [t, Nat.mul_assoc] using (Nat.div_mul_cancel hd).symm

/-- Swapping two increasing prime valuations strictly lowers the integer and strictly
raises its normalized divisor sum. The smaller valuation may be zero. -/
theorem prime_exponent_swap {m p q : ℕ} (hm : 1 ≤ m)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hab : m.factorization p < m.factorization q) :
    let a := m.factorization p
    let b := m.factorization q
    let t := m / (p ^ a * q ^ b)
    let m' := t * p ^ b * q ^ a
    1 ≤ t ∧ Nat.gcd t (p * q) = 1 ∧ m = t * p ^ a * q ^ b ∧
      (0 < m' ∧ m' < m) ∧
      (ArithmeticFunction.sigma 1 m : ℝ) / m <
        (ArithmeticFunction.sigma 1 m' : ℝ) / m' := by
  dsimp only
  let a := m.factorization p
  let b := m.factorization q
  let t := m / (p ^ a * q ^ b)
  obtain ⟨ht, htc, hmfac⟩ := two_prime_cofactor hm hp hq hpq
  change 1 ≤ t at ht
  change t.Coprime (p * q) at htc
  change m = t * p ^ a * q ^ b at hmfac
  have htp : t.Coprime p := (Nat.coprime_mul_iff_right.mp htc).1
  have htq : t.Coprime q := (Nat.coprime_mul_iff_right.mp htc).2
  have hpqc : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq.ne
  have ht0 : 0 < t := ht
  have hnew : 0 < t * p ^ b * q ^ a :=
    Nat.mul_pos (Nat.mul_pos ht0 (pow_pos hp.pos _)) (pow_pos hq.pos _)
  have hsize : t * p ^ b * q ^ a < m := by
    have hpow : p ^ (b - a) < q ^ (b - a) :=
      pow_lt_pow_left₀ hpq (Nat.zero_le p) (Nat.sub_ne_zero_of_lt hab)
    have hbase : 0 < t * p ^ a * q ^ a :=
      Nat.mul_pos (Nat.mul_pos ht0 (pow_pos hp.pos _)) (pow_pos hq.pos _)
    have hsplit (r : ℕ) : r ^ b = r ^ a * r ^ (b - a) := by
      rw [← pow_add, Nat.add_sub_of_le hab.le]
    rw [hmfac, hsplit p, hsplit q]
    nlinarith [Nat.mul_lt_mul_of_pos_left hpow hbase]
  have hfactor (i j : ℕ) :
      (ArithmeticFunction.sigma 1 (t * p ^ i * q ^ j) : ℝ) /
          (t * p ^ i * q ^ j : ℕ) =
        ((ArithmeticFunction.sigma 1 t : ℝ) / t) *
          (reciprocalGeomSum p i * reciprocalGeomSum q j) := by
    rw [normalized_sigma_mul ((htq.pow_right j).mul_left (hpqc.pow i j)),
      normalized_sigma_mul (htp.pow_right i), normalized_sigma_prime_pow hp,
      normalized_sigma_prime_pow hq, mul_assoc]
  have hgain :
      (ArithmeticFunction.sigma 1 m : ℝ) / m <
        (ArithmeticFunction.sigma 1 (t * p ^ b * q ^ a) : ℝ) /
          (t * p ^ b * q ^ a : ℕ) := by
    have hpositive : 0 < (ArithmeticFunction.sigma 1 t : ℝ) / t :=
      div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 t ht0.ne')
        (by exact_mod_cast ht0)
    have hswap := reciprocal_geom_sum_swap_strict (p := (p : ℝ)) (q := (q : ℝ))
      (by exact_mod_cast hp.one_lt) (by exact_mod_cast hpq) hab
    rw [hmfac, hfactor a b, hfactor b a]
    exact mul_lt_mul_of_pos_left hswap hpositive
  exact ⟨ht, htc, hmfac, ⟨hnew, hsize⟩, hgain⟩

#print axioms prime_exponent_swap

end

end D5.S3.Arith.ExponentExchange.IntegerSwap
