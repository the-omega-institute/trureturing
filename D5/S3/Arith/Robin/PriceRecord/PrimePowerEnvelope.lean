/- GID: D5/S3/Arith/Robin/PriceRecord/PrimePowerEnvelope
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/PrimePowerEnvelope
   mirror-E: none(waiver:general-arithmetic-theorem-no-numerical-experiment)
   anchors: []
   utility: none
   digest: Uniform prime-power bounds for nonnegative-price full records. -/

import D5.S3.Arith.ExponentExchange.IntegerSwap
import D5.S3.Arith.GoldenResource.ObjectiveCore
import D5.S3.Arith.Robin.OriginalEndpointPrimeTail
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Log

/-! Finite prime-power removal and a fresh Bertrand prime bound all occupied exponents. -/

namespace D5.S3.Arith.Robin.PriceRecord.PrimePowerEnvelope

open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.ExponentExchange.IntegerSwap
open D5.S3.Arith.RobinExponentSwap
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)

noncomputable section

private theorem abundancy_record {m : ℕ} {lambda : ℝ} (hlambda : 0 ≤ lambda)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m)
    {n : ℕ} (hn : 0 < n) (hnm : n < m) :
    (ArithmeticFunction.sigma 1 n : ℝ) / n <
      (ArithmeticFunction.sigma 1 m : ℝ) / m := by
  have hm : 0 < m := hn.trans hnm
  have h := hrecord n hn hnm
  rw [golden_resource_sigma_identity _ hn, golden_resource_sigma_identity _ hm] at h
  have hlog : Real.log (n : ℝ) < Real.log (m : ℝ) :=
    Real.log_lt_log (by exact_mod_cast hn) (by exact_mod_cast hnm)
  have hprice := mul_le_mul_of_nonneg_left hlog.le hlambda
  have hsig : 0 < (ArithmeticFunction.sigma 1 n : ℝ) / n :=
    div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 n hn.ne')
      (by exact_mod_cast hn)
  exact (Real.log_lt_log_iff hsig (div_pos
    (by exact_mod_cast ArithmeticFunction.sigma_pos 1 m hm.ne')
    (by exact_mod_cast hm))).mp (by linarith)

private theorem prime_cofactor {m p : ℕ} (hm : 0 < m) (hp : p.Prime) :
    let t := m / p ^ m.factorization p
    0 < t ∧ t.Coprime p ∧ m = t * p ^ m.factorization p := by
  dsimp only
  have hd := (hp.pow_dvd_iff_le_factorization hm.ne').mpr le_rfl
  let t := m / p ^ m.factorization p
  have ht : 0 < t := Nat.div_pos (Nat.le_of_dvd hm hd) (pow_pos hp.pos _)
  have hfac : t.factorization = m.factorization - (p ^ m.factorization p).factorization :=
    Nat.factorization_div hd
  have htp : t.factorization p = 0 := by
    rw [hfac, hp.factorization_pow]
    simp
  have hcp : t.Coprime p := (hp.coprime_iff_not_dvd.mpr (by
    rw [hp.dvd_iff_one_le_factorization ht.ne', htp]
    omega)).symm
  exact ⟨ht, hcp, (Nat.div_mul_cancel hd).symm⟩

private theorem geom_closed {p : ℕ} (hp : p.Prime) (a : ℕ) :
    reciprocalGeomSum p a =
      ((p : ℝ) ^ (a + 1) - 1) / ((p : ℝ) ^ a * (p - 1)) := by
  rw [← normalized_sigma_prime_pow hp, ArithmeticFunction.sigma_one_apply_prime_pow hp]
  push_cast
  rw [geom_sum_eq (by exact_mod_cast hp.ne_one : (p : ℝ) ≠ 1)]
  rw [div_div]
  congr 1
  ring

private theorem exchange_bound {m p q k : ℕ} (hm : 0 < m)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hqfresh : ¬ q ∣ m)
    (hka : k ≤ m.factorization p) (hqB : q < p ^ k)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      (ArithmeticFunction.sigma 1 n : ℝ) / n <
        (ArithmeticFunction.sigma 1 m : ℝ) / m) :
    p ^ (m.factorization p - k + 1) < q := by
  let a := m.factorization p
  let b := a - k
  let t := m / p ^ a
  obtain ⟨ht, htp, hmt⟩ := prime_cofactor hm hp
  change 0 < t at ht
  change t.Coprime p at htp
  change m = t * p ^ a at hmt
  have hab : a = b + k := by dsimp [a, b]; omega
  have hpa : p ^ a = p ^ b * p ^ k := by rw [hab, pow_add]
  have htq : t.Coprime q := (hq.coprime_iff_not_dvd.mpr (fun h =>
    hqfresh (h.trans (by rw [hmt]; exact Nat.dvd_mul_right t (p ^ a))))).symm
  have hpqc : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq.ne
  let n := t * p ^ b * q
  have hn : 0 < n := Nat.mul_pos (Nat.mul_pos ht (pow_pos hp.pos _)) hq.pos
  have hnm : n < m := by
    rw [hmt, hpa, ← Nat.mul_assoc]
    exact Nat.mul_lt_mul_of_pos_left hqB (Nat.mul_pos ht (pow_pos hp.pos _))
  have hfactor (i : ℕ) :
      (ArithmeticFunction.sigma 1 (t * p ^ i) : ℝ) / (t * p ^ i : ℕ) =
        ((ArithmeticFunction.sigma 1 t : ℝ) / t) * reciprocalGeomSum p i := by
    rw [normalized_sigma_mul (htp.pow_right i), normalized_sigma_prime_pow hp]
  have hnew :
      (ArithmeticFunction.sigma 1 n : ℝ) / n =
        ((ArithmeticFunction.sigma 1 t : ℝ) / t) *
          (reciprocalGeomSum p b * reciprocalGeomSum q 1) := by
    have hqnorm : (ArithmeticFunction.sigma 1 q : ℝ) / q =
        reciprocalGeomSum q 1 := by
      simpa only [pow_one] using normalized_sigma_prime_pow hq 1
    dsimp [n]
    rw [normalized_sigma_mul (htq.mul_left (hpqc.pow_left b)), hfactor,
      hqnorm, mul_assoc]
  have h := hrecord n hn hnm
  rw [hnew, hmt, hfactor] at h
  have htpos : 0 < (ArithmeticFunction.sigma 1 t : ℝ) / t :=
    div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 t ht.ne')
      (by exact_mod_cast ht)
  have hlocal := (mul_lt_mul_iff_right₀ htpos).mp h
  have hqgeom : reciprocalGeomSum q 1 = ((q : ℝ) + 1) / q := by
    norm_num [reciprocalGeomSum, Finset.sum_range_succ]
    field_simp [show (q : ℝ) ≠ 0 by exact_mod_cast hq.ne_zero]
  rw [geom_closed hp b, geom_closed hp a, hqgeom] at hlocal
  have hpR : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq.pos
  have hB : 0 < (p : ℝ) ^ k := by positivity
  have hX : 0 < (p : ℝ) ^ b := by positivity
  have haR : (p : ℝ) ^ a = (p : ℝ) ^ b * (p : ℝ) ^ k := by rw [hab, pow_add]
  rw [pow_succ, pow_succ, haR] at hlocal
  have heq :
      (((p : ℝ) ^ b * p - 1) / ((p : ℝ) ^ b * (p - 1))) * ((q + 1) / q) <
        ((p : ℝ) ^ b * p * p ^ k - 1) / ((p : ℝ) ^ b * (p - 1)) / p ^ k := by
    convert hlocal using 1
    field_simp
  have hden : 0 < (p : ℝ) ^ b * (p - 1) := mul_pos hX (by linarith)
  rw [div_mul_eq_mul_div, div_right_comm _ _ ((p : ℝ) ^ k),
    div_lt_div_iff_of_pos_right hden, ← mul_div_assoc] at heq
  have heq2 := (div_lt_div_iff₀ hqR hB).mp heq
  have hRlt : (p : ℝ) ^ b * p < (q : ℝ) + 1 := by
    by_contra hnR
    have hR := le_of_not_gt hnR
    have hexp := mul_le_mul_of_nonneg_right hR hB.le
    nlinarith
  have hRN : p ^ (b + 1) < q + 1 := by exact_mod_cast hRlt
  have hRle : p ^ (b + 1) ≤ q := by omega
  have hRne : p ^ (b + 1) ≠ q := by
    intro he
    have hpdq : p ∣ q := he ▸ dvd_pow_self p (by omega : b + 1 ≠ 0)
    exact hpq.ne ((Nat.dvd_prime hq).mp hpdq |>.resolve_left hp.ne_one)
  exact lt_of_le_of_ne hRle hRne

/-- Every prime power in an actual full predecessor record at a nonnegative price
is strictly below four times the square of its largest prime factor. -/
theorem price_record_prime_power_envelope {m : ℕ} (hm : 2 ≤ m)
    {lambda : ℝ} (hlambda : 0 ≤ lambda)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective lambda n < goldenResourceObjective lambda m) :
    ∀ p : ℕ, p.Prime → p ∣ m →
      p ^ m.factorization p < 4 * (largestPrime m) ^ 2 := by
  have hm0 : m ≠ 0 := by omega
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have hrP : r ≤ largestPrime m :=
    Finset.le_sup (f := id) (Nat.mem_primeFactors.mpr ⟨hr, hrd, hm0⟩)
  have hP : 2 ≤ largestPrime m := hr.two_le.trans hrP
  obtain ⟨q, hq, hPq, hqP⟩ := Nat.exists_prime_lt_and_le_two_mul
    (largestPrime m) (by omega)
  have hqfresh : ¬ q ∣ m := by
    intro hqd
    have := Finset.le_sup (f := id) (Nat.mem_primeFactors.mpr ⟨hq, hqd, hm0⟩)
    exact (not_le_of_gt hPq) this
  intro p hp hpd
  have hpP : p ≤ largestPrime m :=
    Finset.le_sup (f := id) (Nat.mem_primeFactors.mpr ⟨hp, hpd, hm0⟩)
  have hpq : p < q := hpP.trans_lt hPq
  let k := Nat.log p q + 1
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hqB : q < p ^ k := Nat.lt_pow_succ_log_self hp.one_lt q
  have hBq : p ^ (k - 1) ≤ q := by
    simpa [k] using Nat.pow_log_le_self p hq.ne_zero
  have hbound : p ^ m.factorization p < q ^ 2 := by
    by_cases hka : k ≤ m.factorization p
    · have hR := exchange_bound (by omega) hp hq hpq hqfresh hka hqB
        (fun n hn hnm => abundancy_record hlambda hrecord hn hnm)
      have hsplit : p ^ m.factorization p =
          p ^ (m.factorization p - k + 1) * p ^ (k - 1) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hsplit, pow_two]
      exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hR (pow_pos hp.pos _))
        (Nat.mul_le_mul_left q hBq)
    · have ha : m.factorization p ≤ k - 1 := by omega
      have hpow := (Nat.pow_le_pow_right hp.pos ha).trans hBq
      exact hpow.trans_lt (by have := hq.two_le; nlinarith)
  have hq2 : q ^ 2 ≤ 4 * largestPrime m ^ 2 := by nlinarith
  exact hbound.trans_le hq2

#print axioms price_record_prime_power_envelope

end

end D5.S3.Arith.Robin.PriceRecord.PrimePowerEnvelope
