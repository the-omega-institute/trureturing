/- GID: D5/S0/Certificates/KrizekIntegralityGcdRecordRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/KrizekIntegralityGcdRecordRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/KrizekIntegralityGcdRecordRefutation.claim; result=D5/S0/Certificates/KrizekIntegralityGcdRecordRefutation.result; claim=D5/S0/Certificates/KrizekIntegralityGcdRecordRefutation.claim
   digest: The seventh listed member of OEIS A245786 is not a record point of OEIS A216793. -/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.KrizekIntegralityGcdRecordRefutation

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

def IsMember (n : ℕ) : Prop :=
  ∃ z : ℤ,
    ((n : ℚ) / (σ 0 n : ℚ) + (σ 1 n : ℚ) / (n : ℚ)) = z

def IsRecord (n : ℕ) : Prop :=
  ∀ m : ℕ, 0 < m → m < n →
    Nat.gcd (σ 1 m) m < Nat.gcd (σ 1 n) n

def claim : Prop := ∀ n : ℕ, 0 < n → IsMember n → IsRecord n

private lemma sigma_N :
    ArithmeticFunction.sigma 1 275890944 = 919636480 := by
  have hN : 275890944 =
      (((((2 ^ 8 * 3 ^ 1) * 7 ^ 1) * 19 ^ 1) * 37 ^ 1) * 73 ^ 1) := by
    norm_num
  rw [hN]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (p := 2) (i := 8) (by norm_num),
    ArithmeticFunction.sigma_one_apply_prime_pow (p := 3) (i := 1) (by norm_num),
    ArithmeticFunction.sigma_one_apply_prime_pow (p := 7) (i := 1) (by norm_num),
    ArithmeticFunction.sigma_one_apply_prime_pow (p := 19) (i := 1) (by norm_num),
    ArithmeticFunction.sigma_one_apply_prime_pow (p := 37) (i := 1) (by norm_num),
    ArithmeticFunction.sigma_one_apply_prime_pow (p := 73) (i := 1) (by norm_num)]
  norm_num

private lemma tau_N :
    ArithmeticFunction.sigma 0 275890944 = 288 := by
  have hN : 275890944 =
      (((((2 ^ 8 * 3 ^ 1) * 7 ^ 1) * 19 ^ 1) * 37 ^ 1) * 73 ^ 1) := by
    norm_num
  rw [hN]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.sigma_zero_apply_prime_pow (p := 2) (i := 8) (by norm_num),
    ArithmeticFunction.sigma_zero_apply_prime_pow (p := 3) (i := 1) (by norm_num),
    ArithmeticFunction.sigma_zero_apply_prime_pow (p := 7) (i := 1) (by norm_num),
    ArithmeticFunction.sigma_zero_apply_prime_pow (p := 19) (i := 1) (by norm_num),
    ArithmeticFunction.sigma_zero_apply_prime_pow (p := 37) (i := 1) (by norm_num),
    ArithmeticFunction.sigma_zero_apply_prime_pow (p := 73) (i := 1) (by norm_num)]
  norm_num

private lemma sigma_M :
    ArithmeticFunction.sigma 1 142990848 = 571963392 := by
  have hM : 142990848 =
      (((((2 ^ 9 * 3 ^ 2) * 7 ^ 1) * 11 ^ 1) * 13 ^ 1) * 31 ^ 1) := by
    norm_num
  rw [hM]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (p := 2) (i := 9) (by norm_num),
    ArithmeticFunction.sigma_one_apply_prime_pow (p := 3) (i := 2) (by norm_num),
    ArithmeticFunction.sigma_one_apply_prime_pow (p := 7) (i := 1) (by norm_num),
    ArithmeticFunction.sigma_one_apply_prime_pow (p := 11) (i := 1) (by norm_num),
    ArithmeticFunction.sigma_one_apply_prime_pow (p := 13) (i := 1) (by norm_num),
    ArithmeticFunction.sigma_one_apply_prime_pow (p := 31) (i := 1) (by norm_num)]
  norm_num

theorem result : ¬ claim := by
  intro hclaim
  have hmember : IsMember 275890944 := by
    refine ⟨957958, ?_⟩
    rw [tau_N, sigma_N]
    norm_num
  have hrecord := hclaim 275890944 (by norm_num) hmember
  have hbad := hrecord 142990848 (by norm_num) (by norm_num)
  rw [sigma_M, sigma_N] at hbad
  norm_num at hbad

#print axioms IsMember
#print axioms IsRecord
#print axioms claim
#print axioms result

end D5.S0.Certificates.KrizekIntegralityGcdRecordRefutation
