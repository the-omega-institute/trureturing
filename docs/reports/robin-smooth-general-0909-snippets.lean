import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import D5.S3.Arith.GoldenResource.RobinRationalBasis

-- Temporary restricted-reproof probe; never register, deposit, or freeze.
namespace RobinSmoothProbe0909

theorem prime_factor_gt_one {p : Nat} (hp : p.Prime) :
    (1 : Real) < (p : Real) / ((p : Real) - 1) := by
  have hp1 : (1 : Real) < p := by exact_mod_cast hp.one_lt
  rw [lt_div_iff₀ (sub_pos.mpr hp1), one_mul]
  linarith only

theorem local_ratio_lt {p : Nat} (hp : p.Prime) (a : Nat) :
    ((Finset.range (a + 1)).sum (fun i => (p : Real) ^ i)) / (p : Real) ^ a <
      (p : Real) / ((p : Real) - 1) := by
  have hp1 : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hpm : (0 : Real) < (p : Real) - 1 := sub_pos.mpr hp1
  have hpow : (0 : Real) < (p : Real) ^ a := pow_pos (by exact_mod_cast hp.pos) a
  rw [geom_sum_eq hp1.ne']
  calc
    ((p : Real) ^ (a + 1) - 1) / (p - 1) / p ^ a <
        (p : Real) ^ (a + 1) / (p - 1) / p ^ a :=
      div_lt_div_of_pos_right
        (div_lt_div_of_pos_right (sub_lt_self _ zero_lt_one) hpm) hpow
    _ = (p : Real) / (p - 1) := by
      rw [pow_succ, div_right_comm, mul_div_cancel_left₀ _ hpow.ne']

theorem sigma_ratio_product {n : Nat} (hn : 0 < n) :
    (ArithmeticFunction.sigma 1 n : Real) / n =
      n.primeFactors.prod (fun p =>
        ((Finset.range (n.factorization p + 1)).sum (fun i => (p : Real) ^ i)) /
          (p : Real) ^ n.factorization p) := by
  have hnprod : (n : Real) =
      n.primeFactors.prod (fun p => (p : Real) ^ n.factorization p) := by
    simpa only [Nat.cast_prod, Nat.cast_pow] using
      congrArg (fun k : Nat => (k : Real)) (Nat.prod_primeFactors_pow_factorization hn.ne')
  have hsprod : (ArithmeticFunction.sigma 1 n : Real) =
      n.primeFactors.prod (fun p =>
        (Finset.range (n.factorization p + 1)).sum (fun i => (p : Real) ^ i)) := by
    simpa only [Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, mul_one] using
      congrArg (fun k : Nat => (k : Real))
        (ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
          (k := 1) hn.ne')
  rw [hsprod, hnprod, Finset.prod_div_distrib]

theorem support_product_le (P : Finset Nat) (hP : forall p, p ∈ P -> p.Prime)
    {n : Nat} (hs : forall p, p.Prime -> p ∣ n -> p ∈ P) :
    n.primeFactors.prod (fun p => (p : Real) / ((p : Real) - 1)) <=
      P.prod (fun p => (p : Real) / ((p : Real) - 1)) := by
  exact Finset.prod_le_prod_of_subset_of_one_le
    (fun p hp => hs p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
    (fun p hp => zero_le_one.trans (prime_factor_gt_one (Nat.prime_of_mem_primeFactors hp)).le)
    (fun p hp _ => (prime_factor_gt_one (hP p hp)).le)

theorem sigma_ratio_lt (P : Finset Nat) (hP : forall p, p ∈ P -> p.Prime)
    {n : Nat} (hn : 1 < n) (hs : forall p, p.Prime -> p ∣ n -> p ∈ P) :
    (ArithmeticFunction.sigma 1 n : Real) / n <
      P.prod (fun p => (p : Real) / ((p : Real) - 1)) := by
  rw [sigma_ratio_product (Nat.zero_lt_of_lt hn)]
  apply lt_of_lt_of_le _ (support_product_le P hP hs)
  apply Finset.prod_lt_prod_of_nonempty _
    (fun p hp => local_ratio_lt (Nat.prime_of_mem_primeFactors hp) _)
    (Nat.nonempty_primeFactors.mpr hn)
  intro p hp
  apply div_pos _ (pow_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos) _)
  apply Finset.sum_pos'
  · intro i _
    exact pow_nonneg (Nat.cast_nonneg p) i
  · exact ⟨0, by simp, by simp⟩

theorem threshold_domain (P : Finset Nat) (hP : forall p, p ∈ P -> p.Prime)
    {n : Nat} (hn : 0 < n)
    (ht : P.prod (fun p => (p : Real) / ((p : Real) - 1)) /
      Real.exp Real.eulerMascheroniConstant < Real.log (Real.log (n : Real))) :
    Real.exp 1 < (n : Real) := by
  have hc : (0 : Real) < P.prod (fun p => (p : Real) / ((p : Real) - 1)) :=
    Finset.prod_pos (fun p hp => zero_lt_one.trans (prime_factor_gt_one (hP p hp)))
  have hll : 0 < Real.log (Real.log (n : Real)) :=
    (div_pos hc (Real.exp_pos _)).trans ht
  have hn1 : (1 : Real) <= n := by exact_mod_cast hn
  have hlog : 1 < Real.log (n : Real) :=
    (Real.log_pos_iff (Real.log_nonneg hn1)).mp hll
  exact (Real.lt_log_iff_exp_lt (by exact_mod_cast hn)).mp hlog

theorem robin_smooth (P : Finset Nat) (hP : forall p, p ∈ P -> p.Prime)
    (n : Nat) (hn : 0 < n) (hs : forall p, p.Prime -> p ∣ n -> p ∈ P)
    (ht : P.prod (fun p => (p : Real) / ((p : Real) - 1)) /
      Real.exp Real.eulerMascheroniConstant < Real.log (Real.log (n : Real))) :
    (ArithmeticFunction.sigma 1 n : Real) / n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : Real)) := by
  have hn1R : (1 : Real) < n :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).trans (threshold_domain P hP hn ht)
  have hn1 : 1 < n := by exact_mod_cast hn1R
  exact (sigma_ratio_lt P hP hn1 hs).trans
    (by simpa only [mul_comm] using (div_lt_iff₀ (Real.exp_pos _)).mp ht)

example : (ArithmeticFunction.sigma 1 1 : Real) / 1 =
    (∅ : Finset Nat).prod (fun p => (p : Real) / ((p : Real) - 1)) := by
  norm_num

theorem empty_support_excluded {n : Nat} (hn : 0 < n)
    (hs : forall p, p.Prime -> p ∣ n -> p ∈ (∅ : Finset Nat)) : n = 1 := by
  have he : n.primeFactors = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact Finset.notMem_empty p
      (hs p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
  exact (Nat.primeFactors_eq_empty.mp he).resolve_left hn.ne'

#print axioms prime_factor_gt_one
#print axioms local_ratio_lt
#print axioms sigma_ratio_product
#print axioms support_product_le
#print axioms sigma_ratio_lt
#print axioms threshold_domain
#print axioms robin_smooth
#print axioms empty_support_excluded

-- Report-only verification of the requested seven-smooth tail specialization.
open D5.S3.Arith.GoldenResource.RobinRationalBasis

theorem seven_tail_threshold {n : Nat} (hn : 131072 <= n) :
    (35 / 8 : Real) / Real.exp Real.eulerMascheroniConstant <
      Real.log (Real.log (n : Real)) := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : Real) <= 577 / 1000) 5
  norm_num [Finset.sum_range_succ] at he
  have he' : Real.exp (577 / 1000) <= Real.exp Real.eulerMascheroniConstant :=
    Real.exp_le_exp.mpr (by linarith only [eulerMascheroni_decimal_bounds.1])
  have hgamma : (89 / 50 : Real) < Real.exp Real.eulerMascheroniConstant := by
    linarith only [he, he']
  have hl := (log_pow_two_mul_bounds 1 17 0 (by norm_num) (by norm_num) (by norm_num)).1
  norm_num [atanhPartial] at hl
  have hlog : (589 / 50 : Real) < Real.log 131072 := by linarith only [hl]
  have hll := (log_pow_two_mul_bounds (589 / 400) 3 4
    (by norm_num) (by norm_num) (by norm_num)).1
  norm_num [atanhPartial, Finset.sum_range_succ] at hll
  have hlow : (123 / 50 : Real) < Real.log (589 / 50) := by linarith only [hll]
  have hbase : (123 / 50 : Real) < Real.log (Real.log 131072) :=
    hlow.trans (Real.log_lt_log (by norm_num) hlog)
  have hnR : (131072 : Real) <= n := by exact_mod_cast hn
  have hln : (123 / 50 : Real) < Real.log (Real.log (n : Real)) :=
    hbase.trans_le (Real.log_le_log (by linarith only [hlog])
      (Real.log_le_log (by norm_num) hnR))
  have hmul := mul_lt_mul hgamma hln.le (by norm_num : (0 : Real) < 123 / 50)
    (Real.exp_pos Real.eulerMascheroniConstant).le
  apply (div_lt_iff₀ (Real.exp_pos _)).mpr
  norm_num at hmul
  linarith only [hmul]

theorem robin_seven_smooth_tail (a b c d : Nat)
    (hn : 131072 <= 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) :
    (ArithmeticFunction.sigma 1 (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) : Real) /
        (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d : Nat) <
      Real.exp Real.eulerMascheroniConstant *
        Real.log (Real.log (2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d : Nat)) := by
  apply robin_smooth {2, 3, 5, 7}
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  · exact lt_of_lt_of_le (by norm_num : 0 < (131072 : Nat)) hn
  · intro p hp hd
    simp only [hp.dvd_mul] at hd
    rcases hd with ((h | h) | h) | h
    · simp [Nat.prime_eq_prime_of_dvd_pow hp (by decide : Nat.Prime 2) h]
    · simp [Nat.prime_eq_prime_of_dvd_pow hp (by decide : Nat.Prime 3) h]
    · simp [Nat.prime_eq_prime_of_dvd_pow hp (by decide : Nat.Prime 5) h]
    · simp [Nat.prime_eq_prime_of_dvd_pow hp (by decide : Nat.Prime 7) h]
  · convert seven_tail_threshold hn using 1 <;> norm_num

#print axioms seven_tail_threshold
#print axioms robin_seven_smooth_tail

end RobinSmoothProbe0909
