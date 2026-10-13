/- GID: D5/S0/Certificates/KrizekAntisigmaDecreaseRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/KrizekAntisigmaDecreaseRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc, mathlib/module/Mathlib.Tactic.NormNum.Prime]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/KrizekAntisigmaDecreaseRefutation.claim; result=D5/S0/Certificates/KrizekAntisigmaDecreaseRefutation.result; claim=D5/S0/Certificates/KrizekAntisigmaDecreaseRefutation.claim
   digest: The instance n = 332640 refutes Krizek's A231548 conjecture about antisigma at gap three. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.KrizekAntisigmaDecreaseRefutation

/-!
OEIS A024816 defines `antisigma(n)` as the sum of the positive integers less
than `n` that do not divide `n`. Equivalently, it is the sum of the
non-divisors between one and `n`, since `n` itself always divides `n`.

In OEIS A231548, Jaroslav Krizek conjectured on 2013-11-12:
"Conjecture: there are no numbers n such that antisigma(n) < antisigma(n-3)."
The claim below excludes `n < 3` exactly because the comment compares `n`
with its predecessor `n - 3`.

The instance `n = 332640` refutes the conjecture. Its divisor sum is computed
from `332640 = 2^5 * 3^3 * 5 * 7 * 11` by multiplicativity. The divisor sum
at `332637 = 3 * 110879` uses the kernel-checked primality of `110879`.
-/

/-- The OEIS A024816 antisigma function, stated as the sum of non-divisors
between one and `n`. -/
def antisigma (n : ℕ) : ℕ :=
  ∑ d ∈ (Finset.Icc 1 n).filter (fun d => ¬ d ∣ n), d

/-- Krizek's A231548 conjecture that antisigma never decreases across a gap
of three, restricted to inputs where `n - 3` is the natural predecessor. -/
def claim : Prop :=
  ∀ n : ℕ, 3 ≤ n → antisigma (n - 3) ≤ antisigma n

private theorem antisigma_eq_triangular_sub_sigma (n : ℕ) :
    antisigma n = n * (n + 1) / 2 - ArithmeticFunction.sigma 1 n := by
  by_cases hn : n = 0
  · subst n
    norm_num [antisigma, ArithmeticFunction.sigma_apply]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hdivisors :
        (Finset.Icc 1 n).filter (fun d => d ∣ n) = n.divisors := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · intro h
        exact ⟨h.2, hn⟩
      · intro hd
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd.1 hnpos, Nat.le_of_dvd hnpos hd.1⟩, hd.1⟩
    have htotal : (∑ d ∈ Finset.Icc 1 n, d) = n * (n + 1) / 2 := by
      rw [show Finset.Icc 1 n = Finset.Ico 1 (n + 1) by
        ext d
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega]
      calc
        (∑ d ∈ Finset.Ico 1 (n + 1), d) = ∑ d ∈ Finset.range (n + 1), d := by
          simpa using
            (Finset.sum_range_eq_add_Ico (fun d : ℕ => d) (Nat.succ_pos n)).symm
        _ = n * (n + 1) / 2 := by
          rw [Finset.sum_range_id]
          simp only [Nat.add_sub_cancel]
          rw [Nat.mul_comm]
    unfold antisigma
    rw [← htotal, ArithmeticFunction.sigma_one_apply, ← hdivisors]
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (s := Finset.Icc 1 n) (p := fun d => d ∣ n) (f := fun d => d)
    omega

private theorem prime_110879 : Nat.Prime 110879 := by norm_num

private theorem sigma_332640 :
    ArithmeticFunction.sigma 1 332640 = 1451520 := by
  let σ := ArithmeticFunction.sigma 1
  have h2 : σ (2 ^ 5) = 63 := by
    exact (ArithmeticFunction.sigma_one_apply_prime_pow (i := 5)
      (by norm_num : Nat.Prime 2)).trans (by norm_num [Finset.sum_range_succ])
  have h3 : σ (3 ^ 3) = 40 := by
    exact (ArithmeticFunction.sigma_one_apply_prime_pow (i := 3)
      (by norm_num : Nat.Prime 3)).trans (by norm_num [Finset.sum_range_succ])
  have h5 : σ (5 ^ 1) = 6 := by
    exact (ArithmeticFunction.sigma_one_apply_prime_pow (i := 1)
      (by norm_num : Nat.Prime 5)).trans (by norm_num [Finset.sum_range_succ])
  have h7 : σ (7 ^ 1) = 8 := by
    exact (ArithmeticFunction.sigma_one_apply_prime_pow (i := 1)
      (by norm_num : Nat.Prime 7)).trans (by norm_num [Finset.sum_range_succ])
  have h11 : σ (11 ^ 1) = 12 := by
    exact (ArithmeticFunction.sigma_one_apply_prime_pow (i := 1)
      (by norm_num : Nat.Prime 11)).trans (by norm_num [Finset.sum_range_succ])
  have h23 : σ (2 ^ 5 * 3 ^ 3) = 63 * 40 :=
    ((ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime
      (by norm_num [Nat.Coprime] : Nat.Coprime (2 ^ 5) (3 ^ 3))).trans
      (congrArg₂ (· * ·) h2 h3)
  have h235 : σ (2 ^ 5 * 3 ^ 3 * 5 ^ 1) = 63 * 40 * 6 :=
    ((ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime
      (by norm_num [Nat.Coprime] : Nat.Coprime (2 ^ 5 * 3 ^ 3) (5 ^ 1))).trans
      (congrArg₂ (· * ·) h23 h5)
  have h2357 : σ (2 ^ 5 * 3 ^ 3 * 5 ^ 1 * 7 ^ 1) = 63 * 40 * 6 * 8 :=
    ((ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime
      (by norm_num [Nat.Coprime] : Nat.Coprime (2 ^ 5 * 3 ^ 3 * 5 ^ 1) (7 ^ 1))).trans
      (congrArg₂ (· * ·) h235 h7)
  have h235711 : σ (2 ^ 5 * 3 ^ 3 * 5 ^ 1 * 7 ^ 1 * 11 ^ 1) = 63 * 40 * 6 * 8 * 12 :=
    ((ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime
      (by norm_num [Nat.Coprime] : Nat.Coprime (2 ^ 5 * 3 ^ 3 * 5 ^ 1 * 7 ^ 1) (11 ^ 1))).trans
      (congrArg₂ (· * ·) h2357 h11)
  exact (congrArg σ (show (332640 : ℕ) = 2 ^ 5 * 3 ^ 3 * 5 ^ 1 * 7 ^ 1 * 11 ^ 1
    by norm_num)).trans (h235711.trans (by norm_num))

private theorem sigma_332637 :
    ArithmeticFunction.sigma 1 332637 = 443520 := by
  have h3 : ArithmeticFunction.sigma 1 3 = 4 := by
    simpa only [pow_one, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero, zero_add, Nat.reduceAdd] using
      (ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) Nat.prime_three)
  have hp : ArithmeticFunction.sigma 1 110879 = 110880 := by
    simpa only [pow_one, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero, zero_add, Nat.reduceAdd] using
      (ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) prime_110879)
  have hcop : Nat.Coprime 3 110879 :=
    Nat.prime_three.coprime_iff_not_dvd.mpr (by norm_num)
  have hprod : ArithmeticFunction.sigma 1 (3 * 110879) = 4 * 110880 :=
    ((ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop).trans
      (congrArg₂ (· * ·) h3 hp)
  exact (congrArg (ArithmeticFunction.sigma 1)
    (show (332637 : ℕ) = 3 * 110879 by norm_num)).trans
    (hprod.trans (by norm_num))

/-- At `n = 332640`, antisigma is smaller than at `n - 3 = 332637`,
contradicting the literal A231548 conjecture. -/
theorem result : ¬ claim := by
  have hprevious : antisigma (332640 - 3) = 55323409683 :=
    (antisigma_eq_triangular_sub_sigma 332637).trans
      ((congrArg (fun x : ℕ => 332637 * (332637 + 1) / 2 - x) sigma_332637).trans
        (by norm_num))
  have hcurrent : antisigma 332640 = 55323399600 :=
    (antisigma_eq_triangular_sub_sigma 332640).trans
      ((congrArg (fun x : ℕ => 332640 * (332640 + 1) / 2 - x) sigma_332640).trans
        (by norm_num))
  intro hclaim
  have hle := hclaim 332640 (by norm_num)
  rw [hprevious, hcurrent] at hle
  norm_num at hle

#print axioms antisigma
#print axioms claim
#print axioms result

end D5.S0.Certificates.KrizekAntisigmaDecreaseRefutation
