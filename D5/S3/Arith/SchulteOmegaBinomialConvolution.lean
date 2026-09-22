/- GID: D5/S3/Arith/SchulteOmegaBinomialConvolution
   generality: G
   mirror-B: D5/B/S3/Arith/SchulteOmegaBinomialConvolution
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Schulte's binomial convolution for big and small omega at every positive index. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Complex.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.SchulteOmegaBinomialConvolution

open ArithmeticFunction
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega

set_option maxHeartbeats 1000000 in
/-- Schulte's A001222 conjecture: the binomial Dirichlet convolution for all
complex x and y and positive n. Here Ω = A001222 counts prime factors with
multiplicity, ω = A001221 counts distinct prime factors, and Ω − ω = A046660.
Natural exponentiation includes the convention 0 ^ 0 = 1. -/
theorem result (x y : ℂ) (n : ℕ) (hn : 0 < n) :
    (x + y) ^ Ω n = ∑ d ∈ n.divisors,
      x ^ Ω d * ((x + y) ^ (Ω (n / d) - ω (n / d)) * y ^ ω (n / d)) := by
  classical
  let F (z : ℂ) : ArithmeticFunction ℂ :=
    ⟨fun m => if m = 0 then 0 else z ^ Ω m, by simp⟩
  let H : ArithmeticFunction ℂ :=
    ⟨fun m => if m = 0 then 0 else (x + y) ^ (Ω m - ω m) * y ^ ω m, by simp⟩
  have hle (m : ℕ) : ω m ≤ Ω m := by
    change m.primeFactorsList.dedup.length ≤ m.primeFactorsList.length
    exact m.primeFactorsList.dedup_sublist.length_le
  have hF (z : ℂ) : (F z).IsMultiplicative := by
    apply IsMultiplicative.iff_ne_zero.mpr
    refine ⟨by simp [F], ?_⟩
    intro a b ha hb _
    simp [F, ha, hb, cardFactors_mul ha hb, pow_add]
  have hH : H.IsMultiplicative := by
    apply IsMultiplicative.iff_ne_zero.mpr
    refine ⟨by simp [H], ?_⟩
    intro a b ha hb hab
    have hsub : Ω a + Ω b - (ω a + ω b) = (Ω a - ω a) + (Ω b - ω b) := by
      have := hle a
      have := hle b
      omega
    simp only [H, coe_mk, if_neg ha, if_neg hb, if_neg (mul_ne_zero ha hb),
      cardFactors_mul ha hb, cardDistinctFactors_mul hab, hsub, pow_add]
    ring
  have hprime (p e : ℕ) (hp : p.Prime) :
      (F x * H) (p ^ e) = F (x + y) (p ^ e) := by
    have hconv : (F x * H) (p ^ e) =
        ∑ i ∈ Finset.range (e + 1), F x (p ^ i) * H (p ^ (e - i)) := by
      rw [ArithmeticFunction.mul_apply,
        Nat.sum_divisorsAntidiagonal (fun a b => F x a * H b), Nat.sum_divisors_prime_pow hp]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Nat.pow_div (by simpa using hi) hp.pos]
    rw [hconv, Finset.sum_range_succ]
    have hterms : (∑ i ∈ Finset.range e, F x (p ^ i) * H (p ^ (e - i))) =
        (∑ i ∈ Finset.range e, x ^ i * (x + y) ^ (e - 1 - i)) * y := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < e := Finset.mem_range.mp hi
      have he : e - i ≠ 0 := by omega
      have hexp : e - i - 1 = e - 1 - i := by omega
      simp [F, H, hp.ne_zero, cardFactors_apply_prime_pow hp,
        cardDistinctFactors_apply_prime_pow hp he, hexp, mul_assoc]
    rw [hterms]
    simp only [Nat.sub_self, pow_zero, F, H, coe_mk, if_neg (pow_ne_zero _ hp.ne_zero),
      if_neg Nat.one_ne_zero, cardFactors_one, cardDistinctFactors_one,
      cardFactors_apply_prime_pow hp, Nat.sub_self, pow_zero, mul_one]
    have hgeom := geom_sum₂_mul_add y x e
    rw [add_comm y x, geom_sum₂_comm] at hgeom
    exact hgeom
  have heq : F x * H = F (x + y) :=
    ((hF x |>.mul hH).eq_iff_eq_on_prime_powers _ _ (hF (x + y))).mpr hprime
  have heval := congrArg (fun f : ArithmeticFunction ℂ => f n) heq
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => F x a * H b)] at heval
  rw [← show F (x + y) n = (x + y) ^ Ω n by simp [F, Nat.ne_of_gt hn], ← heval]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  have hnd0 : n / d ≠ 0 := Nat.ne_of_gt
    (Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)) (Nat.pos_of_ne_zero hd0))
  simp [F, H, hd0, hnd0]

end D5.S3.Arith.SchulteOmegaBinomialConvolution
