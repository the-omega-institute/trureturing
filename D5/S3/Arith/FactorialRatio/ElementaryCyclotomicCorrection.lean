/- GID: D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection
   generality: G
   mirror-B: D5/B/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Factorization]
   utility: none
   digest: Exact cyclotomic factorial correction and multinomial divisibility. -/

module

import Batteries.Tactic.OpenPrivate
public import D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd
import all D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic.Ring

/-! Exact prime-power deficits and the integer multinomial bound for the residual indicator. -/

set_option autoImplicit false

set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FactorialRatio.ElementaryCyclotomicCorrection

open Finset ElementaryCyclotomicGcd
open scoped BigOperators Nat
open private mem_levels_iff prime_power_cases EStar_factorization EStar_ne_zero
  factorization_prime_product prime_product_ne_zero sum_levels_eq_zero_of_lt
  from D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd

/-- The residual indicator at one conductor. Each conductor occurs at most once. -/
@[expose] public def levelIndicator (N r : ℕ) : ℕ :=
  if r % 4 = 1 ∧ firstDegree r ≤ N % r then 1 else 0

/-- The original deficit at a prime-power level, including the exceptional level two. -/
@[expose] public def levelDeficit (N r : ℕ) : ℕ :=
  exceptionCount N r + if r = 2 then N else 0

private theorem card_exception_progression
    {N r a L : ℕ} (hr : 0 < r)
    (hroot : ∀ j, Exceptional r j ↔ ∃ k : ℕ, j = a + r * k)
    (hbound : ∀ k, a + r * k + firstDegree r ≤ N ↔ k < L) :
    ((range (N + 1 - firstDegree r)).filter (Exceptional r)).card = L := by
  rw [← card_range L]
  symm
  refine card_bij (fun k _ => a + r * k) ?_ ?_ ?_
  · intro k hk
    exact mem_filter.mpr
      ⟨mem_range.mpr (by have := (hbound k).mpr (mem_range.mp hk); omega),
        (hroot _).mpr ⟨k, rfl⟩⟩
  · intro k _ l _ h
    exact Nat.mul_left_cancel hr (Nat.add_left_cancel h)
  · intro j hj
    obtain ⟨k, hk⟩ := (hroot j).mp (mem_filter.mp hj).2
    have h := mem_range.mp (mem_filter.mp hj).1
    exact ⟨k, mem_range.mpr ((hbound k).mp (by omega)), hk.symm⟩

private theorem shifted_multiple_le_iff {N r b : ℕ} (hr : 0 < r) (hb : b < r) (k : ℕ) :
    r * k + b ≤ N ↔ k < N / r + (if b ≤ N % r then 1 else 0) := by
  have hdecomp := Nat.mod_add_div N r
  have hrem := Nat.mod_lt N hr
  by_cases hlt : k < N / r
  · have hmul : r * (k + 1) ≤ r * (N / r) :=
      Nat.mul_le_mul_left r (by omega)
    rw [Nat.mul_add, Nat.mul_one] at hmul
    have hleft : r * k + b ≤ N := by omega
    have hright : k < N / r + (if b ≤ N % r then 1 else 0) := by omega
    simp [hleft, hright]
  · by_cases heq : k = N / r
    · subst k
      by_cases h : b ≤ N % r <;> simp [h] <;> omega
    · have hmul : r * (N / r + 1) ≤ r * k :=
        Nat.mul_le_mul_left r (by omega)
      rw [Nat.mul_add, Nat.mul_one] at hmul
      by_cases h : b ≤ N % r <;> simp [h] <;> omega

private theorem exceptional_three_progression {r : ℕ} (hr : 3 ≤ r) (h3 : r % 4 = 3)
    (j : ℕ) : Exceptional r j ↔ ∃ k : ℕ, j = (r - firstDegree r) + r * k := by
  have he : 4 * firstDegree r = r + 1 := by unfold firstDegree; omega
  have ha : 4 * (r - firstDegree r) + 1 = 3 * r := by omega
  rw [Exceptional, ite_eq_right (by omega : r % 4 ≠ 1)]
  constructor
  · rintro ⟨d, hd⟩
    have hmod := congrArg (fun x : ℕ => x % 4) hd
    rw [Nat.mul_mod r d 4, h3] at hmod
    have hleft : (4 * j + 1) % 4 = 1 := by omega
    rw [hleft] at hmod
    have hd3 : d % 4 = 3 := by have := Nat.mod_lt d (by decide : 0 < 4); omega
    have hdecomp := Nat.mod_add_div d 4
    have hmul : r * d = 4 * (r * (d / 4)) + 3 * r := by
      calc
        r * d = r * (3 + 4 * (d / 4)) := congrArg (r * ·) (by omega)
        _ = _ := by ring
    exact ⟨d / 4, by omega⟩
  · rintro ⟨k, rfl⟩
    refine ⟨3 + 4 * k, ?_⟩
    calc
      _ = (4 * (r - firstDegree r) + 1) + 4 * (r * k) := by ring
      _ = _ := by rw [ha]; ring

/-- Closed count at every odd conductor, including empty ranges. -/
private theorem exceptionCount_odd_closed (N : ℕ) {r : ℕ} (hr : 3 ≤ r) (hodd : r % 2 = 1) :
    exceptionCount N r = N / r + levelIndicator N r := by
  rw [exceptionCount, ite_eq_left hodd]
  by_cases h1 : r % 4 = 1
  · have he : firstDegree r < r := by unfold firstDegree; omega
    unfold levelIndicator
    simp only [h1, true_and]
    refine card_exception_progression (by omega) (a := 0) ?_ ?_
    · intro j
      simp [Exceptional, h1, dvd_def]
    · intro k
      simpa [Nat.add_comm] using shifted_multiple_le_iff (N := N) (by omega : 0 < r) he k
  · have h3 : r % 4 = 3 := by omega
    have he : firstDegree r ≤ r := by unfold firstDegree; omega
    unfold levelIndicator
    simp only [h1, false_and, ite_false, add_zero]
    refine card_exception_progression (by omega) (exceptional_three_progression hr h3) ?_
    intro k
    have h : (r - firstDegree r) + r * k + firstDegree r = (k + 1) * r := by
      rw [Nat.add_mul, Nat.one_mul, mul_comm k r]
      omega
    rw [h, ← Nat.le_div_iff_mul_le (by omega : 0 < r)]
    omega

/-- At (2) the deficit is (N), at higher dyadic powers it is zero, and at each odd
prime power it is its Legendre floor plus the residue indicator. -/
public theorem levelDeficit_prime_pow (N : ℕ) {p t : ℕ} (hp : p.Prime) (ht : 1 ≤ t) :
    levelDeficit N (p ^ t) =
      (if p ^ t = 2 then N else 0) +
        (if p = 2 then 0 else N / p ^ t) + levelIndicator N (p ^ t) := by
  rcases hp.eq_two_or_odd with rfl | hpodd
  · have he (k : ℕ) : (2 : ℕ) ^ (k + 1) % 2 = 0 := by simp [pow_succ]
    have ht' : t - 1 + 1 = t := by omega
    have hmod : (2 : ℕ) ^ t % 2 = 0 := ht' ▸ he (t - 1)
    have hnot : (2 : ℕ) ^ t % 4 ≠ 1 := by omega
    simp [levelDeficit, exceptionCount, levelIndicator, hmod, hnot]
  · have hne : p ≠ 2 := by omega
    have hh := prime_power_cases hp ht
    have ho : p ^ t % 2 = 1 := Nat.odd_iff.mp ((Nat.odd_iff.mpr hpodd).pow)
    have hn : p ^ t ≠ 2 := by omega
    simp [levelDeficit, hne, hn, exceptionCount_odd_closed N (by omega : 3 ≤ p ^ t) ho]

/-- The integer specialization of the squarefree product of selected conductor factors. -/
@[expose] public def RStar (N : ℕ) : ℕ :=
  ∏ p ∈ Nat.primesLE (4 * N + 1), p ^ (∑ t ∈ levels p (4 * N + 1), levelIndicator N (p ^ t))

private theorem RStar_ne_zero (N : ℕ) : RStar N ≠ 0 := prime_product_ne_zero _ _

private theorem RStar_factorization (N : ℕ) {p : ℕ} (hp : p.Prime) :
    (RStar N).factorization p = ∑ t ∈ levels p (4 * N + 1), levelIndicator N (p ^ t) := by
  unfold RStar
  rw [factorization_prime_product]
  by_cases h : p ≤ 4 * N + 1
  · rw [ite_eq_left (Nat.mem_primesLE.mpr ⟨h, hp⟩)]
  · rw [ite_eq_right (fun hm => h (Nat.mem_primesLE.mp hm).1),
        sum_levels_eq_zero_of_lt (lt_of_not_ge h)]

private theorem factorial_factorization_at {p n X : ℕ} (hp : p.Prime) (hn : n ≤ X) :
    n.factorial.factorization p = ∑ t ∈ levels p X, n / p ^ t :=
  Nat.factorization_factorial hp (Nat.lt_succ_of_le (Nat.log_mono_right hn))

/-- The exact correction specializing to integers, with the binary digit sum in the exponent. -/
public theorem EStar_eq_two_pow_digit_sum_mul_factorial_mul_RStar (N : ℕ) :
    EStar N = 2 ^ (Nat.digits 2 N).sum * N.factorial * RStar N := by
  have hpow : (2 : ℕ) ^ (Nat.digits 2 N).sum ≠ 0 := by positivity
  apply Nat.eq_of_factorization_eq (EStar_ne_zero N)
    (mul_ne_zero (mul_ne_zero hpow (Nat.factorial_ne_zero N)) (RStar_ne_zero N))
  intro p
  by_cases hp : p.Prime
  · rw [EStar_factorization N hp,
        Nat.factorization_mul (mul_ne_zero hpow (Nat.factorial_ne_zero N)) (RStar_ne_zero N),
        Nat.factorization_mul hpow (Nat.factorial_ne_zero N), Finsupp.add_apply, Finsupp.add_apply,
        Nat.prime_two.factorization_pow, Finsupp.single_apply, RStar_factorization N hp]
    rcases hp.eq_two_or_odd with rfl | hpodd
    · have hleg := Nat.sub_one_mul_factorization_factorial (n := N) Nat.prime_two
      norm_num at hleg
      have hdigits := Nat.digit_sum_le 2 N
      have hz : (∑ t ∈ levels 2 (4 * N + 1), exceptionCount N (2 ^ t)) = 0 := by
        refine sum_eq_zero fun t ht => ?_
        have hpos := (mem_levels_iff Nat.prime_two).mp ht
        obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
        simp [exceptionCount, pow_succ]
      have hi : (∑ t ∈ levels 2 (4 * N + 1), levelIndicator N (2 ^ t)) = 0 := by
        refine sum_eq_zero fun t ht => ?_
        have hpos := (mem_levels_iff Nat.prime_two).mp ht
        obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
        have he : (2 : ℕ) ^ (k + 1) % 2 = 0 := by simp [pow_succ]
        simp [levelIndicator, show (2 : ℕ) ^ (k + 1) % 4 ≠ 1 by omega]
      simp only [hz, hi, if_true, add_zero]
      omega
    · have hne : p ≠ 2 := by omega
      rw [ite_eq_right hne, ite_eq_right (Ne.symm hne), zero_add, zero_add,
        factorial_factorization_at hp (by omega : N ≤ 4 * N + 1), ← sum_add_distrib]
      refine sum_congr rfl fun t ht => ?_
      have hh := prime_power_cases hp ((mem_levels_iff hp).mp ht).1
      have ho : p ^ t % 2 = 1 := Nat.odd_iff.mp ((Nat.odd_iff.mpr hpodd).pow)
      exact exceptionCount_odd_closed N (by omega) ho
  · simp only [Nat.factorization_eq_zero_of_not_prime _ hp]

private def correctionParts (N : ℕ) : Fin 4 → ℕ := ![N, N, N, N + 1]

private theorem correctionParts_sum (N : ℕ) :
    ∑ i, correctionParts N i = 4 * N + 1 := by
  simp [Fin.sum_univ_four, correctionParts]
  omega

private theorem correctionParts_factorial_prod (N : ℕ) :
    ∏ i, (correctionParts N i).factorial = N.factorial ^ 3 * (N + 1).factorial := by
  simp [Fin.prod_univ_four, correctionParts, pow_succ]

/-- The multinomial for four parts of sizes (N,N,N,N+1). -/
@[expose] public def correctionMultinomial (N : ℕ) : ℕ :=
  (4 * N + 1).factorial / (N.factorial ^ 3 * (N + 1).factorial)

private theorem correctionMultinomial_eq_multinomial (N : ℕ) :
    correctionMultinomial N = Nat.multinomial univ (correctionParts N) := by
  rw [Nat.multinomial, correctionParts_sum, correctionParts_factorial_prod]
  rfl

private theorem correctionMultinomial_pos (N : ℕ) : 0 < correctionMultinomial N := by
  rw [correctionMultinomial_eq_multinomial]
  exact Nat.multinomial_pos _ _

private theorem correctionMultinomial_mul_factorials (N : ℕ) :
    correctionMultinomial N * (N.factorial ^ 3 * (N + 1).factorial) =
      (4 * N + 1).factorial := by
  simpa only [correctionParts_sum, correctionParts_factorial_prod, mul_comm,
    ← correctionMultinomial_eq_multinomial] using Nat.multinomial_spec univ (correctionParts N)

/-- The carry at one level of the multinomial valuation. -/
private def multinomialCarry (N r : ℕ) : ℕ :=
  (4 * N + 1) / r - (3 * (N / r) + (N + 1) / r)

private theorem multinomial_floors (N : ℕ) {r : ℕ} (hr : 2 ≤ r) :
    3 * (N / r) + (N + 1) / r + multinomialCarry N r = (4 * N + 1) / r ∧
    levelIndicator N r ≤ multinomialCarry N r := by
  have hpos : 0 < r := by omega
  let u := N % r
  have hu : u < r := Nat.mod_lt N hpos
  have hN : N = u + r * (N / r) := (Nat.mod_add_div N r).symm
  have h₁ : (N + 1) / r = (u + 1) / r + N / r := by
    rw [show N + 1 = (u + 1) + r * (N / r) by omega, Nat.add_mul_div_left _ _ hpos]
  have h₄ : (4 * N + 1) / r = (4 * u + 1) / r + 4 * (N / r) := by
    have he : 4 * N + 1 = (4 * u + 1) + r * (4 * (N / r)) := calc
      _ = 4 * (u + r * (N / r)) + 1 := congrArg (fun j => 4 * j + 1) hN
      _ = _ := by ring
    rw [he, Nat.add_mul_div_left _ _ hpos]
  have hmono : (u + 1) / r ≤ (4 * u + 1) / r := Nat.div_le_div_right (by omega)
  have hcarry : multinomialCarry N r = (4 * u + 1) / r - (u + 1) / r := by
    unfold multinomialCarry
    omega
  refine ⟨by omega, ?_⟩
  by_cases hi : r % 4 = 1 ∧ firstDegree r ≤ N % r
  · rw [levelIndicator, ite_eq_left hi, hcarry]
    have he : 4 * firstDegree r + 1 = r := by unfold firstDegree; omega
    have hule : firstDegree r ≤ u := hi.2
    have hdiv : 1 ≤ (4 * u + 1) / r :=
      (Nat.le_div_iff_mul_le hpos).mpr (by omega)
    by_cases hb : u + 1 < r
    · rw [Nat.div_eq_of_lt hb, Nat.sub_zero]
      exact hdiv
    · have hb' : u + 1 = r := by omega
      rw [hb', Nat.div_self hpos]
      have hdiv' : 2 ≤ (4 * u + 1) / r :=
        (Nat.le_div_iff_mul_le hpos).mpr (by omega)
      omega
  · simp [levelIndicator, hi]

private theorem levelIndicator_le_multinomialCarry (N : ℕ) {r : ℕ} (hr : 2 ≤ r) :
    levelIndicator N r ≤ multinomialCarry N r := (multinomial_floors N hr).2

/-- Legendre's formula gives the exact sum of carries for the actual integer multinomial. -/
private theorem correctionMultinomial_factorization (N : ℕ) {p : ℕ} (hp : p.Prime) :
    (correctionMultinomial N).factorization p =
      ∑ t ∈ levels p (4 * N + 1), multinomialCarry N (p ^ t) := by
  have he := congrArg (fun n : ℕ => n.factorization p) (correctionMultinomial_mul_factorials N)
  have hN := Nat.factorial_ne_zero N
  have hN1 := Nat.factorial_ne_zero (N + 1)
  have hM := (correctionMultinomial_pos N).ne'
  simp only [pow_succ, pow_zero, one_mul] at he
  rw [Nat.factorization_mul hM (mul_ne_zero (mul_ne_zero (mul_ne_zero hN hN) hN) hN1),
      Nat.factorization_mul (mul_ne_zero (mul_ne_zero hN hN) hN) hN1,
      Nat.factorization_mul (mul_ne_zero hN hN) hN, Nat.factorization_mul hN hN] at he
  simp only [Finsupp.add_apply] at he
  rw [factorial_factorization_at hp (by omega : N ≤ 4 * N + 1),
      factorial_factorization_at hp (by omega : N + 1 ≤ 4 * N + 1),
      factorial_factorization_at hp (le_refl (4 * N + 1))] at he
  have hsum :
      (∑ t ∈ levels p (4 * N + 1), N / p ^ t) +
      (∑ t ∈ levels p (4 * N + 1), N / p ^ t) +
      (∑ t ∈ levels p (4 * N + 1), N / p ^ t) +
      (∑ t ∈ levels p (4 * N + 1), (N + 1) / p ^ t) +
      (∑ t ∈ levels p (4 * N + 1), multinomialCarry N (p ^ t)) =
      ∑ t ∈ levels p (4 * N + 1), (4 * N + 1) / p ^ t := by
    simp only [← sum_add_distrib]
    refine sum_congr rfl fun t ht => ?_
    have h := multinomial_floors N (prime_power_cases hp ((mem_levels_iff hp).mp ht).1).1
    omega
  omega

public theorem RStar_dvd_correctionMultinomial (N : ℕ) : RStar N ∣ correctionMultinomial N := by
  apply (Nat.factorization_prime_le_iff_dvd (RStar_ne_zero N)
    (correctionMultinomial_pos N).ne').mp
  intro p hp
  rw [RStar_factorization N hp, correctionMultinomial_factorization N hp]
  refine sum_le_sum fun t ht => ?_
  exact levelIndicator_le_multinomialCarry N (prime_power_cases hp ((mem_levels_iff hp).mp ht).1).1

public theorem log_RStar_bounds (N : ℕ) :
    0 ≤ Real.log (RStar N) ∧ Real.log (RStar N) ≤ (4 * (N : ℝ) + 1) * Real.log 4 := by
  have hM : correctionMultinomial N ≤ 4 ^ (4 * N + 1) := by
    classical
    have hmem : correctionParts N ∈ piAntidiag univ (4 * N + 1) :=
      mem_piAntidiag.mpr ⟨correctionParts_sum N, fun _ _ => mem_univ _⟩
    calc
      correctionMultinomial N = Nat.multinomial univ (correctionParts N) :=
        correctionMultinomial_eq_multinomial N
      _ ≤ ∑ k ∈ piAntidiag univ (4 * N + 1), Nat.multinomial univ k :=
        single_le_sum (fun _ _ => Nat.zero_le _) hmem
      _ = 4 ^ (4 * N + 1) := by
        simpa using (sum_pow_eq_sum_piAntidiag (univ : Finset (Fin 4))
          (fun _ => (1 : ℕ)) (4 * N + 1)).symm
  refine ⟨Real.log_natCast_nonneg _, ?_⟩
  calc
    _ ≤ Real.log ((4 ^ (4 * N + 1) : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (RStar_ne_zero N))
        (by exact_mod_cast (Nat.le_of_dvd (correctionMultinomial_pos N)
          (RStar_dvd_correctionMultinomial N)).trans hM)
    _ = _ := by rw [Nat.cast_pow, Real.log_pow]; push_cast <;> rfl

end D5.S3.Arith.FactorialRatio.ElementaryCyclotomicCorrection
