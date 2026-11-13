/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/RamanujanSums
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/RamanujanSums
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime power values and multiplicativity of finite Ramanujan sums. -/

import D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient

/-! Prime power values and multiplicativity for the finite coprime exponential sums. -/

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.RamanujanSums

open scoped BigOperators
open D5.S3.Analytic.Certified.FiniteRamanujanDivisorIdentity
open ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

set_option maxHeartbeats 1000000

theorem ramanujan_prime_power (p j k : ℕ) (hp : p.Prime) :
    ramanujanSum (p ^ (k + 1)) j =
      (if p ^ (k + 1) ∣ j then (p ^ (k + 1) : ℂ) else 0) -
      (if p ^ k ∣ j then (p ^ k : ℂ) else 0) := by
  have h1 := sum_ramanujanSum_divisors (p ^ (k + 1)) j (pow_pos hp.pos _)
  have h0 := sum_ramanujanSum_divisors (p ^ k) j (pow_pos hp.pos _)
  rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ] at h1
  rw [Nat.sum_divisors_prime_pow hp] at h0
  push_cast at h1 h0
  rw [h0] at h1
  exact eq_sub_of_add_eq' h1

private noncomputable def ramFn (j : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun d => ramanujanSum d j, by simp [ramanujanSum]⟩
private def divFn (j : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun d => if d ∣ j then (d : ℂ) else 0, by simp⟩
private theorem ramFn_mul_zeta (j : ℕ) : ramFn j * (ζ : ArithmeticFunction ℂ) = divFn j := by
  ext d
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  change (∑ r ∈ d.divisors, ramanujanSum r j) = if d ∣ j then (d : ℂ) else 0
  by_cases hd : d = 0
  · simp [hd]
  · exact sum_ramanujanSum_divisors d j (Nat.pos_of_ne_zero hd)
private theorem ramFn_eq_moebius_convolution (j : ℕ) :
    ramFn j = divFn j * (μ : ArithmeticFunction ℂ) := by
  calc
    ramFn j = ramFn j * 1 := (mul_one _).symm
    _ = ramFn j * ((ζ : ArithmeticFunction ℂ) * (μ : ArithmeticFunction ℂ)) := by
      rw [ArithmeticFunction.coe_zeta_mul_coe_moebius]
    _ = (ramFn j * (ζ : ArithmeticFunction ℂ)) * (μ : ArithmeticFunction ℂ) :=
      (mul_assoc _ _ _).symm
    _ = _ := by rw [ramFn_mul_zeta]
private theorem divFn_multiplicative (j : ℕ) : (divFn j).IsMultiplicative := by
  refine ⟨by simp [divFn], ?_⟩
  intro m n hmn
  change (if m * n ∣ j then ((m * n : ℕ) : ℂ) else 0) =
    (if m ∣ j then (m : ℂ) else 0) * (if n ∣ j then (n : ℂ) else 0)
  have hd : m * n ∣ j ↔ m ∣ j ∧ n ∣ j := by
    constructor
    · intro h
      exact ⟨(dvd_mul_right m n).trans h, (dvd_mul_left n m).trans h⟩
    · rintro ⟨hm, hn⟩
      exact hmn.mul_dvd_of_dvd_of_dvd hm hn
  by_cases hm : m ∣ j <;> by_cases hn : n ∣ j <;> simp [hd, hm, hn]
theorem ramanujan_multiplicative (m n j : ℕ) (hmn : m.Coprime n) :
    ramanujanSum (m * n) j = ramanujanSum m j * ramanujanSum n j := by
  have h : (ramFn j).IsMultiplicative := by
    rw [ramFn_eq_moebius_convolution]
    exact (divFn_multiplicative j).mul ArithmeticFunction.isMultiplicative_moebius.intCast
  exact h.2 hmn

theorem ramanujan_one (j : ℕ) : ramanujanSum 1 j = 1 := by
  simpa using sum_ramanujanSum_divisors 1 j Nat.zero_lt_one

end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.RamanujanSums
