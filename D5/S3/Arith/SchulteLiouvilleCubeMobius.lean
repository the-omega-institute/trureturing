/- GID: D5/S3/Arith/SchulteLiouvilleCubeMobius
   generality: G
   mirror-B: D5/B/S3/Arith/SchulteLiouvilleCubeMobius
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Schulte's A299406 coefficients equal Liouville times the cube-Mobius convolution. -/

import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Algebra.GCDMonoid.Nat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.SchulteLiouvilleCubeMobius

open ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.Omega

/-- The k-th-power lift: for positive k, the coefficients of f(ks)
when f denotes its Dirichlet series. The guard discards non-powers. -/
def liftPow (k : ℕ) (f : ArithmeticFunction ℤ) : ArithmeticFunction ℤ where
  toFun n := if (Nat.floorRoot k n) ^ k = n then f (Nat.floorRoot k n) else 0
  map_zero' := by simp

/-- A299406: the coefficient sequence of ζ(s)ζ(6s)/(ζ(2s)ζ(3s)),
read through Dirichlet convolution. -/
def A : ArithmeticFunction ℤ :=
  (ζ : ArithmeticFunction ℤ) * liftPow 6 ζ * liftPow 2 μ * liftPow 3 μ

/-- A210826 via its Lambert series: μ convolved with the cube indicator. -/
def B : ArithmeticFunction ℤ := μ * liftPow 3 ζ

set_option maxHeartbeats 1000000 in
/-- Schulte's A299406 product identity at every positive natural index. -/
theorem result (n : ℕ) (hn : 0 < n) :
    A n = liouville n * B n := by
  have liftPow_apply_pow (k : ℕ) (hk : k ≠ 0) (f : ArithmeticFunction ℤ) (m : ℕ) :
      liftPow k f (m ^ k) = f m := by
    simp [liftPow, Nat.floorRoot_pow_self hk]

  have liftPow_apply_nonpow (k : ℕ) (f : ArithmeticFunction ℤ) (n : ℕ)
      (hn : ¬ ∃ m, m ^ k = n) : liftPow k f n = 0 := by
    simp [liftPow, show (Nat.floorRoot k n) ^ k ≠ n from fun h => hn ⟨_, h⟩]

  have liftPow_isMultiplicative (k : ℕ) (hk : k ≠ 0) (f : ArithmeticFunction ℤ)
      (hf : f.IsMultiplicative) : (liftPow k f).IsMultiplicative := by
    refine ⟨?_, ?_⟩
    · simpa using (liftPow_apply_pow k hk f 1).trans hf.1
    intro a b hab
    by_cases ha : ∃ r, r ^ k = a
    · obtain ⟨r, rfl⟩ := ha
      by_cases hb : ∃ s, s ^ k = b
      · obtain ⟨s, rfl⟩ := hb
        rw [← mul_pow, liftPow_apply_pow k hk, liftPow_apply_pow k hk,
          liftPow_apply_pow k hk]
        exact hf.2 ((Nat.coprime_pow_right_iff (Nat.pos_of_ne_zero hk) _ _).mp
          ((Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hk) _ _).mp hab))
      · rw [liftPow_apply_nonpow k f b hb, mul_zero]
        apply liftPow_apply_nonpow
        rintro ⟨s, hs⟩
        obtain ⟨t, ht⟩ := exists_eq_pow_of_mul_eq_pow
          (show IsUnit (gcd b (r ^ k)) from by
            change IsUnit (Nat.gcd b (r ^ k))
            rw [hab.symm.gcd_eq_one]
            exact isUnit_one)
          (show b * r ^ k = s ^ k from (mul_comm ..).trans hs.symm)
        exact hb ⟨t, ht.symm⟩
    · rw [liftPow_apply_nonpow k f a ha, zero_mul]
      apply liftPow_apply_nonpow
      rintro ⟨s, hs⟩
      obtain ⟨t, ht⟩ := exists_eq_pow_of_mul_eq_pow
        (show IsUnit (gcd a b) from by
          change IsUnit (Nat.gcd a b)
          rw [hab.gcd_eq_one]
          exact isUnit_one) hs.symm
      exact ha ⟨t, ht.symm⟩

  have liftPow_prime_pow (k : ℕ) (hk : k ≠ 0) (f : ArithmeticFunction ℤ)
      (p e : ℕ) (hp : p.Prime) :
      liftPow k f (p ^ e) = if k ∣ e then f (p ^ (e / k)) else 0 := by
    by_cases he : k ∣ e
    · rw [if_pos he]
      have hpow : p ^ e = (p ^ (e / k)) ^ k := by
        rw [← pow_mul, Nat.div_mul_cancel he]
      rw [hpow, liftPow_apply_pow k hk]
    · rw [if_neg he]
      apply liftPow_apply_nonpow
      rintro ⟨m, hm⟩
      have hmdvd : m ∣ p ^ e := hm ▸ dvd_pow_self m hk
      obtain ⟨i, hi, hmi⟩ := (Nat.dvd_prime_pow hp).mp hmdvd
      have hie : i * k = e := Nat.pow_right_injective hp.one_lt (by
        change p ^ (i * k) = p ^ e
        rw [pow_mul, ← hmi, hm])
      exact he (hie ▸ dvd_mul_left k i)

  have conv_prime_pow (f g : ArithmeticFunction ℤ) (p e : ℕ) (hp : p.Prime) :
      (f * g) (p ^ e) = ∑ i ∈ Finset.range (e + 1), f (p ^ i) * g (p ^ (e - i)) := by
    rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b),
      Nat.sum_divisors_prime_pow hp]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Nat.pow_div (by simpa using hi) hp.pos]

  have lift_moebius_prime_pow (k : ℕ) (hk : k ≠ 0) (p e : ℕ) (hp : p.Prime) :
      liftPow k μ (p ^ e) = (if e = 0 then (1 : ℤ) else 0) - (if e = k then 1 else 0) := by
    rw [liftPow_prime_pow k hk μ p e hp]
    by_cases he0 : e = 0
    · subst e
      simp [Ne.symm hk]
    by_cases hek : e = k
    · subst e
      simp [hk, Nat.div_self (Nat.pos_of_ne_zero hk), ArithmeticFunction.moebius_apply_prime hp]
    by_cases hke : k ∣ e
    · rw [if_pos hke, ArithmeticFunction.moebius_apply_prime_pow hp]
      · have he1 : e / k ≠ 1 := by
          intro h
          have := Nat.div_mul_cancel hke
          rw [h, one_mul] at this
          exact hek this.symm
        simp [he0, hek, he1]
      · intro h
        have := Nat.div_mul_cancel hke
        rw [h, zero_mul] at this
        exact he0 this.symm
    · simp [hke, he0, hek]

  have conv_lift_moebius (f : ArithmeticFunction ℤ) (k : ℕ) (hk : k ≠ 0)
      (p e : ℕ) (hp : p.Prime) :
      (f * liftPow k μ) (p ^ e) = f (p ^ e) - if k ≤ e then f (p ^ (e - k)) else 0 := by
    rw [mul_comm f, conv_prime_pow _ _ p e hp]
    simp_rw [lift_moebius_prime_pow k hk p _ hp, sub_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_ite_eq']

  have zeta_lift_two_prime_pow (p e : ℕ) (hp : p.Prime) :
      ((ζ : ArithmeticFunction ℤ) * liftPow 2 μ) (p ^ e) =
        (if e = 0 then (1 : ℤ) else 0) + (if e = 1 then 1 else 0) := by
    rw [conv_lift_moebius _ 2 (by decide) p e hp]
    have hz (i : ℕ) : (ζ : ArithmeticFunction ℤ) (p ^ i) = 1 := by
      simp [natCoe_apply, hp.ne_zero]
    simp only [hz]
    split_ifs <;> omega

  have conv_squarefree (f : ArithmeticFunction ℤ) (p e : ℕ) (hp : p.Prime) :
      (f * ((ζ : ArithmeticFunction ℤ) * liftPow 2 μ)) (p ^ e) =
        f (p ^ e) + if 1 ≤ e then f (p ^ (e - 1)) else 0 := by
    rw [mul_comm f, conv_prime_pow _ _ p e hp]
    simp_rw [zeta_lift_two_prime_pow p _ hp, add_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_ite_eq', Nat.succ_le_iff]

  have lift_zeta_prime_pow (k : ℕ) (hk : k ≠ 0) (p e : ℕ) (hp : p.Prime) :
      liftPow k ζ (p ^ e) = if k ∣ e then (1 : ℤ) else 0 := by
    rw [liftPow_prime_pow k hk ζ p e hp]
    simp [natCoe_apply, hp.ne_zero]

  have B_prime_pow (p e : ℕ) (hp : p.Prime) :
      B (p ^ e) = (if 3 ∣ e then (1 : ℤ) else 0) -
        if 1 ≤ e then (if 3 ∣ e - 1 then 1 else 0) else 0 := by
    have hlift : liftPow 1 μ = μ := by
      ext n
      simpa using liftPow_apply_pow 1 (by decide) μ n
    rw [B, mul_comm μ, ← hlift, conv_lift_moebius _ 1 (by decide) p e hp]
    simp only [lift_zeta_prime_pow 3 (by decide) p _ hp]

  have A_prime_pow (p e : ℕ) (hp : p.Prime) :
      A (p ^ e) =
        ((if 6 ∣ e then (1 : ℤ) else 0) +
          if 1 ≤ e then (if 6 ∣ e - 1 then 1 else 0) else 0) -
        if 3 ≤ e then
          ((if 6 ∣ e - 3 then 1 else 0) +
            if 1 ≤ e - 3 then (if 6 ∣ (e - 3) - 1 then 1 else 0) else 0)
        else 0 := by
    have hA : A = (liftPow 6 ζ * ((ζ : ArithmeticFunction ℤ) * liftPow 2 μ)) * liftPow 3 μ := by
      unfold A
      ring
    rw [hA, conv_lift_moebius _ 3 (by decide) p e hp]
    simp only [conv_squarefree _ p _ hp, lift_zeta_prime_pow 6 (by decide) p _ hp]

  have prime_power_identity (p e : ℕ) (hp : p.Prime) :
      A (p ^ e) = ArithmeticFunction.liouville (p ^ e) * B (p ^ e) := by
    rw [A_prime_pow p e hp, B_prime_pow p e hp,
      ArithmeticFunction.liouville_apply (pow_ne_zero _ hp.ne_zero),
      ArithmeticFunction.cardFactors_apply_prime_pow hp, neg_one_pow_eq_ite]
    simp only [Nat.even_iff, Nat.dvd_iff_mod_eq_zero]
    split_ifs <;> omega

  have hA : A.IsMultiplicative :=
    (((isMultiplicative_zeta.natCast.mul
      (liftPow_isMultiplicative 6 (by decide) ζ isMultiplicative_zeta.natCast)).mul
      (liftPow_isMultiplicative 2 (by decide) μ isMultiplicative_moebius)).mul
      (liftPow_isMultiplicative 3 (by decide) μ isMultiplicative_moebius))
  have hB : B.IsMultiplicative :=
    isMultiplicative_moebius.mul
      (liftPow_isMultiplicative 3 (by decide) ζ isMultiplicative_zeta.natCast)
  have hfun : A = ArithmeticFunction.liouville.pmul B :=
    (hA.eq_iff_eq_on_prime_powers A _ (isMultiplicative_liouville.pmul hB)).mpr
      (fun p e hp => prime_power_identity p e hp)
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) hfun
  simpa only [pmul_apply, ArithmeticFunction.liouville_apply (Nat.ne_of_gt hn)] using h

end D5.S3.Arith.SchulteLiouvilleCubeMobius
