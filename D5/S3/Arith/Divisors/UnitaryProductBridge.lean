/- GID: D5/S3/Arith/Divisors/UnitaryProductBridge
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/UnitaryProductBridge
   mirror-E: none(waiver:symbolic-divisor-product-identity)
   anchors: []
   utility: none
   digest: Unitary divisor sums are products of complete prime-power choices. -/

import D5.S3.Arith.EulerFormDivisorSum
import D5.S3.Arith.Divisors.PrimeReciprocalProduct
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

/-! # Prime-power choices for actual unitary divisors -/

namespace D5.S3.Arith.Divisors.UnitaryProductBridge

open Finset
open D5.S3.Arith.EulerFormDivisorSum

private theorem prime_power_product_support (N : ℕ) (hn : N ≠ 0)
    (F : Finset ℕ) (hF : F ⊆ N.primeFactors) :
    (∏ p ∈ F, p ^ N.factorization p).primeFactors = F := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert p F hp ih =>
    have hpN := hF (mem_insert_self p F)
    have hF' : F ⊆ N.primeFactors := fun q hq => hF (mem_insert_of_mem hq)
    have hprime := Nat.prime_of_mem_primeFactors hpN
    have hexp : N.factorization p ≠ 0 :=
      (hprime.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hpN)).ne'
    rw [prod_insert hp, Nat.primeFactors_mul (pow_ne_zero _ hprime.ne_zero)
      (prod_ne_zero_iff.mpr (fun q hq => pow_ne_zero _
        (Nat.prime_of_mem_primeFactors (hF' hq)).ne_zero)),
      Nat.primeFactors_prime_pow hexp hprime, ih hF']
    simp

private theorem prime_power_product_unitary (N : ℕ) (hn : N ≠ 0)
    (F : Finset ℕ) (hF : F ⊆ N.primeFactors) :
    (∏ p ∈ F, p ^ N.factorization p) ∈
      N.divisors.filter (fun d => Nat.Coprime d (N / d)) := by
  classical
  let g : Finset ℕ → ℕ := fun S => ∏ p ∈ S, p ^ N.factorization p
  have hsplit : g (N.primeFactors \ F) * g F = N :=
    (prod_sdiff hF).trans (Nat.prod_primeFactors_pow_factorization hn).symm
  have hg0 : g F ≠ 0 := prod_ne_zero_iff.mpr (fun p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hF hp)).ne_zero)
  have hd : g F ∣ N := ⟨g (N.primeFactors \ F), by simpa [mul_comm] using hsplit.symm⟩
  have hquot : N / g F = g (N.primeFactors \ F) := by
    exact (congrArg (fun k => k / g F) hsplit.symm).trans
      (Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hg0))
  apply mem_filter.mpr
  refine ⟨Nat.mem_divisors.mpr ⟨hd, hn⟩, ?_⟩
  change Nat.Coprime (g F) (N / g F)
  rw [hquot]
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  apply Nat.coprime_prod_right_iff.mpr
  intro q hq
  exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors (hF hp))
    (Nat.prime_of_mem_primeFactors (mem_sdiff.mp hq).1)
    (by intro heq; exact (mem_sdiff.mp hq).2 (heq ▸ hp))

/-- Every unitary divisor chooses either all or none of each prime power. -/
theorem unitarySum_eq_product (N : ℕ) (hn : N ≠ 0) :
    unitarySum N = ∏ p ∈ N.primeFactors, (p ^ N.factorization p + 1) := by
  classical
  apply le_antisymm (unitarySum_le_product N hn)
  let g : Finset ℕ → ℕ := fun F => ∏ p ∈ F, p ^ N.factorization p
  have hinj : Set.InjOn g N.primeFactors.powerset := by
    intro F hF G hG h
    have hh := congrArg Nat.primeFactors h
    simpa only [g, prime_power_product_support N hn F (mem_powerset.mp hF),
      prime_power_product_support N hn G (mem_powerset.mp hG)] using hh
  rw [unitarySum]
  rw [show (∏ p ∈ N.primeFactors, (p ^ N.factorization p + 1)) =
      ∑ F ∈ N.primeFactors.powerset, g F from prod_add_one _]
  exact sum_le_sum_of_injOn g hinj
    (by
      intro d hd
      obtain ⟨F, hF, rfl⟩ := mem_image.mp hd
      exact prime_power_product_unitary N hn F (mem_powerset.mp hF))
    (fun _ _ => le_rfl) (fun _ _ _ => Nat.zero_le _)

private theorem normalized_unitary_product (N : ℕ) (hn : N ≠ 0) :
    (unitarySum N : ℚ) / N =
      ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℚ) ^ N.factorization p) := by
  have hprod : (∏ p ∈ N.primeFactors, (p : ℚ) ^ N.factorization p) = N := by
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  have hu : (unitarySum N : ℚ) =
      ∏ p ∈ N.primeFactors, ((p : ℚ) ^ N.factorization p + 1) := by
    exact_mod_cast unitarySum_eq_product N hn
  rw [hu, ← hprod, ← prod_div_distrib]
  apply prod_congr rfl
  intro p hp
  rw [add_div, div_self (pow_ne_zero _ (by exact_mod_cast
    (Nat.prime_of_mem_primeFactors hp).ne_zero))]

private theorem radical_factorization (N p : ℕ) (hp : p ∈ N.primeFactors) :
    (∏ q ∈ N.primeFactors, q).factorization p = 1 := by
  classical
  rw [Nat.factorization_prod_apply
    (fun q hq => (Nat.prime_of_mem_primeFactors hq).ne_zero)]
  trans ∑ q ∈ N.primeFactors, if q = p then 1 else 0
  · apply sum_congr rfl
    intro q hq
    simp [(Nat.prime_of_mem_primeFactors hq).factorization, Finsupp.single_apply]
  · simp [hp]

/-- Primes absent from the radical quotient occur only to the first power. -/
private theorem factorization_eq_quotient_add_one (N m p : ℕ) (hn : N ≠ 0)
    (hNm : N = m * ∏ q ∈ N.primeFactors, q)
    (hp : p ∈ N.primeFactors) : N.factorization p = m.factorization p + 1 := by
  have hm0 : m ≠ 0 := fun hz => hn (hNm.trans (by simp [hz]))
  have hr0 : (∏ q ∈ N.primeFactors, q) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun q hq => (Nat.prime_of_mem_primeFactors hq).ne_zero)
  have hf := congrArg (fun k : ℕ => k.factorization p) hNm
  rw [Nat.factorization_mul hm0 hr0, Finsupp.add_apply, radical_factorization N p hp] at hf
  exact hf

private theorem factorization_eq_one_of_not_dvd_quotient (N m p : ℕ) (hn : N ≠ 0)
    (hNm : N = m * ∏ q ∈ N.primeFactors, q)
    (hp : p ∈ N.primeFactors) (hpm : ¬ p ∣ m) : N.factorization p = 1 := by
  simpa only [Nat.factorization_eq_zero_of_not_dvd hpm, zero_add] using
    factorization_eq_quotient_add_one N m p hn hNm hp

/-- Primes in a specified support, absent from the radical quotient, give a
lower Euler-product bound for the actual normalized unitary divisor sum. -/
private theorem normalized_unitary_lower (N m : ℕ) (hn : N ≠ 0)
    (hNm : N = m * ∏ p ∈ N.primeFactors, p)
    (F : Finset ℕ) (hF : F ⊆ N.primeFactors) (hmF : ∀ p ∈ F, ¬ p ∣ m) :
    (∏ p ∈ F, (1 + (p : ℚ)⁻¹)) ≤ (unitarySum N : ℚ) / N := by
  rw [normalized_unitary_product N hn]
  have heq : (∏ p ∈ F, (1 + (p : ℚ)⁻¹)) =
      ∏ p ∈ F, (1 + 1 / (p : ℚ) ^ N.factorization p) := by
    apply prod_congr rfl
    intro p hp
    rw [factorization_eq_one_of_not_dvd_quotient N m p hn hNm (hF hp) (hmF p hp)]
    simp
  rw [heq]
  exact prod_le_prod_of_subset_of_one_le₀ hF (fun _ _ => by positivity)
    (fun _ _ _ => le_add_of_nonneg_right (by positivity))

/-- Mandatory small-prime support also bounds the actual normalized squarefree
divisor sum from below. -/
private theorem normalized_squarefree_lower (N m : ℕ) (hn : N ≠ 0)
    (hNm : N = m * ∏ p ∈ N.primeFactors, p)
    (F : Finset ℕ) (hF : F ⊆ N.primeFactors) :
    (∏ p ∈ F, (1 + (p : ℚ)⁻¹)) / m ≤ (squarefreeSum N : ℚ) / N := by
  have hm0 : m ≠ 0 := fun hz => hn (hNm.trans (by simp [hz]))
  have hr : (∏ p ∈ N.primeFactors, (p : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun p hp => by exact_mod_cast
      (Nat.prime_of_mem_primeFactors hp).ne_zero)
  have hs : (squarefreeSum N : ℚ) = ∏ p ∈ N.primeFactors, ((p : ℚ) + 1) := by
    exact_mod_cast squarefreeSum_eq_product N hn
  have hNQ : (N : ℚ) = m * ∏ p ∈ N.primeFactors, (p : ℚ) := by
    simpa only [Nat.cast_mul, Nat.cast_prod] using congrArg (fun k : ℕ => (k : ℚ)) hNm
  have hprod : (∏ p ∈ N.primeFactors, (1 + (p : ℚ)⁻¹)) =
      (squarefreeSum N : ℚ) / (∏ p ∈ N.primeFactors, (p : ℚ)) := by
    rw [hs, ← prod_div_distrib]
    apply prod_congr rfl
    intro p hp
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    field_simp
  calc
    _ ≤ (∏ p ∈ N.primeFactors, (1 + (p : ℚ)⁻¹)) / m :=
      div_le_div_of_nonneg_right
        (prod_le_prod_of_subset_of_one_le₀ hF (fun _ _ => by positivity)
          (fun _ _ _ => le_add_of_nonneg_right (by positivity))) (by positivity)
    _ = _ := by rw [hprod, hNQ]; field_simp

/-- Mandatory primes up to the radical quotient supply a joint lower bound
for the two actual divisor sums. -/
theorem mandatory_support_lower (N : ℕ) (hn : N ≠ 0)
    (hsmall : ∀ p, Nat.Prime p → p ≤ N / (∏ q ∈ N.primeFactors, q) → p ∣ N) :
    let m := N / (∏ q ∈ N.primeFactors, q)
    (∏ p ∈ Nat.primesLE m \ m.primeFactors, (1 + (p : ℚ)⁻¹)) +
      (∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)) / m ≤
      (unitarySum N : ℚ) / N + (squarefreeSum N : ℚ) / N := by
  classical
  dsimp only
  let m := N / (∏ q ∈ N.primeFactors, q)
  have hNm : N = m * ∏ q ∈ N.primeFactors, q :=
    (Nat.div_mul_cancel (Nat.prod_primeFactors_dvd N)).symm
  have hm0 : m ≠ 0 := fun hz => hn (hNm.trans (by simp [hz]))
  have hF : Nat.primesLE m ⊆ N.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primesLE hp,
      hsmall p (Nat.prime_of_mem_primesLE hp) (Nat.le_of_mem_primesLE hp), hn⟩
  have hnot : ∀ p ∈ Nat.primesLE m \ m.primeFactors, ¬ p ∣ m := by
    intro p hp hd
    exact (mem_sdiff.mp hp).2 (Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primesLE (mem_sdiff.mp hp).1, hd, hm0⟩)
  exact add_le_add
    (normalized_unitary_lower N m hn hNm _ (sdiff_subset.trans hF) hnot)
    (normalized_squarefree_lower N m hn hNm _ hF)

/-- Retaining repeated-prime contributions gives the complete mandatory
product bound, including the small radical quotients. -/
theorem mandatory_product_lower (N : ℕ) (hn : N ≠ 0)
    (hsmall : ∀ p, Nat.Prime p → p ≤ N / (∏ q ∈ N.primeFactors, q) → p ∣ N) :
    let m := N / (∏ q ∈ N.primeFactors, q)
    (∏ p ∈ Nat.primesLE m, (1 + 1 / (p : ℚ) ^ (m.factorization p + 1))) +
      (∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)) / m ≤
      (unitarySum N : ℚ) / N + (squarefreeSum N : ℚ) / N := by
  classical
  dsimp only
  let m := N / (∏ q ∈ N.primeFactors, q)
  have hNm : N = m * ∏ q ∈ N.primeFactors, q :=
    (Nat.div_mul_cancel (Nat.prod_primeFactors_dvd N)).symm
  have hF : Nat.primesLE m ⊆ N.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primesLE hp,
      hsmall p (Nat.prime_of_mem_primesLE hp) (Nat.le_of_mem_primesLE hp), hn⟩
  apply add_le_add _ (normalized_squarefree_lower N m hn hNm _ hF)
  rw [normalized_unitary_product N hn]
  calc
    _ = ∏ p ∈ Nat.primesLE m, (1 + 1 / (p : ℚ) ^ N.factorization p) := by
      apply prod_congr rfl
      intro p hp
      rw [factorization_eq_quotient_add_one N m p hn hNm (hF hp)]
    _ ≤ _ := prod_le_prod_of_subset_of_one_le₀ hF (fun _ _ => by positivity)
      (fun _ _ _ => le_add_of_nonneg_right (by positivity))

private theorem finite_mandatory_block_0 :
    ∀ m ∈ Icc 1 100,
      (2 : ℚ) ≤
        (∏ p ∈ Nat.primesLE m, (1 + 1 / (p : ℚ) ^ (m.factorization p + 1))) +
        (∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)) / m := by
  decide +kernel

private theorem finite_mandatory_block_1 :
    ∀ m ∈ Icc 101 200,
      (2 : ℚ) ≤
        (∏ p ∈ Nat.primesLE m, (1 + 1 / (p : ℚ) ^ (m.factorization p + 1))) +
        (∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)) / m := by
  decide +kernel

private theorem finite_mandatory_block_2 :
    ∀ m ∈ Icc 201 300,
      (2 : ℚ) ≤
        (∏ p ∈ Nat.primesLE m, (1 + 1 / (p : ℚ) ^ (m.factorization p + 1))) +
        (∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)) / m := by
  decide +kernel

private theorem finite_mandatory_block_3 :
    ∀ m ∈ Icc 301 400,
      (2 : ℚ) ≤
        (∏ p ∈ Nat.primesLE m, (1 + 1 / (p : ℚ) ^ (m.factorization p + 1))) +
        (∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)) / m := by
  decide +kernel

private theorem finite_mandatory_block_4 :
    ∀ m ∈ Icc 401 500,
      (2 : ℚ) ≤
        (∏ p ∈ Nat.primesLE m, (1 + 1 / (p : ℚ) ^ (m.factorization p + 1))) +
        (∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)) / m := by
  decide +kernel

private theorem finite_mandatory_block_5 :
    ∀ m ∈ Icc 501 600,
      (2 : ℚ) ≤
        (∏ p ∈ Nat.primesLE m, (1 + 1 / (p : ℚ) ^ (m.factorization p + 1))) +
        (∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)) / m := by
  decide +kernel

private theorem finite_mandatory_block_6 :
    ∀ m ∈ Icc 601 700,
      (2 : ℚ) ≤
        (∏ p ∈ Nat.primesLE m, (1 + 1 / (p : ℚ) ^ (m.factorization p + 1))) +
        (∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)) / m := by
  decide +kernel

private theorem finite_mandatory_block_7 :
    ∀ m ∈ Icc 701 800,
      (2 : ℚ) ≤
        (∏ p ∈ Nat.primesLE m, (1 + 1 / (p : ℚ) ^ (m.factorization p + 1))) +
        (∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)) / m := by
  decide +kernel

private theorem finite_mandatory_block_8 :
    ∀ m ∈ Icc 801 900,
      (2 : ℚ) ≤
        (∏ p ∈ Nat.primesLE m, (1 + 1 / (p : ℚ) ^ (m.factorization p + 1))) +
        (∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)) / m := by
  decide +kernel

private theorem finite_mandatory_block_9 :
    ∀ m ∈ Icc 901 999,
      (2 : ℚ) ≤
        (∏ p ∈ Nat.primesLE m, (1 + 1 / (p : ℚ) ^ (m.factorization p + 1))) +
        (∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)) / m := by
  decide +kernel

private theorem finite_mandatory_bound :
    ∀ m ∈ Icc 1 999,
      (2 : ℚ) ≤
        (∏ p ∈ Nat.primesLE m, (1 + 1 / (p : ℚ) ^ (m.factorization p + 1))) +
        (∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)) / m := by
  intro m hm
  have hm' := mem_Icc.mp hm

  by_cases h0 : m ≤ 100
  · exact finite_mandatory_block_0 m (mem_Icc.mpr ⟨by omega, h0⟩)

  by_cases h1 : m ≤ 200
  · exact finite_mandatory_block_1 m (mem_Icc.mpr ⟨by omega, h1⟩)

  by_cases h2 : m ≤ 300
  · exact finite_mandatory_block_2 m (mem_Icc.mpr ⟨by omega, h2⟩)

  by_cases h3 : m ≤ 400
  · exact finite_mandatory_block_3 m (mem_Icc.mpr ⟨by omega, h3⟩)

  by_cases h4 : m ≤ 500
  · exact finite_mandatory_block_4 m (mem_Icc.mpr ⟨by omega, h4⟩)

  by_cases h5 : m ≤ 600
  · exact finite_mandatory_block_5 m (mem_Icc.mpr ⟨by omega, h5⟩)

  by_cases h6 : m ≤ 700
  · exact finite_mandatory_block_6 m (mem_Icc.mpr ⟨by omega, h6⟩)

  by_cases h7 : m ≤ 800
  · exact finite_mandatory_block_7 m (mem_Icc.mpr ⟨by omega, h7⟩)

  by_cases h8 : m ≤ 900
  · exact finite_mandatory_block_8 m (mem_Icc.mpr ⟨by omega, h8⟩)

  exact finite_mandatory_block_9 m (mem_Icc.mpr ⟨by omega, hm'.2⟩)

/-- Mandatory small-prime support forces the actual joint divisor-sum
inequality for every positive integer, without a bound on its size. -/
theorem unitary_squarefree_ge_twice_of_support (N : ℕ) (hn : N ≠ 0)
    (hsmall : ∀ p, Nat.Prime p → p ≤ N / (∏ q ∈ N.primeFactors, q) → p ∣ N) :
    2 * N ≤ unitarySum N + squarefreeSum N := by
  let m := N / (∏ q ∈ N.primeFactors, q)
  have hNm : N = m * ∏ q ∈ N.primeFactors, q :=
    (Nat.div_mul_cancel (Nat.prod_primeFactors_dvd N)).symm
  have hm0 : 0 < m := Nat.pos_of_ne_zero (fun hz => hn (hNm.trans (by simp [hz])))
  have hnorm : (2 : ℚ) ≤ (unitarySum N : ℚ) / N + (squarefreeSum N : ℚ) / N := by
    by_cases hlarge : 1000 ≤ m
    · have hs := mandatory_support_lower N hn hsmall
      change _ ≤ (unitarySum N : ℚ) / N + (squarefreeSum N : ℚ) / N at hs
      have hb := PrimeReciprocalProduct.missing_support_product_ge_two m hlarge
      have hp : (0 : ℚ) ≤ (∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)) / m := by positivity
      linarith
    · exact (finite_mandatory_bound m (mem_Icc.mpr ⟨hm0, by omega⟩)).trans
        (mandatory_product_lower N hn hsmall)
  have hNQ : (0 : ℚ) < N := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hs : (2 : ℚ) * N ≤ (unitarySum N : ℚ) + squarefreeSum N := by
    apply (le_div_iff₀ hNQ).mp
    simpa only [add_div] using hnorm
  exact_mod_cast hs

end D5.S3.Arith.Divisors.UnitaryProductBridge
