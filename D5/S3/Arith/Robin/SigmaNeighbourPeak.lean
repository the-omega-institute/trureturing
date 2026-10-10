/- GID: D5/S3/Arith/Robin/SigmaNeighbourPeak
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/SigmaNeighbourPeak
   mirror-E: none(waiver:qualitative-existence)
   anchors: []
   utility: none
   digest: Primorials have arbitrarily large divisor sums relative to both immediate neighbours. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.Complex.ExponentialBounds
import D5.S3.Arith.GoldenResourceOptimalInteger
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Robin.SigmaNeighbourPeak

open Finset ArithmeticFunction

open ArithmeticFunction in
/-- OEIS A397578 conjecture: for every `n` some `k ≥ 2` has `σ(k) > n·σ(k-1)` and `σ(k) > n·σ(k+1)`. -/
def claim : Prop :=
  ∀ n : ℕ, ∃ k : ℕ, 2 ≤ k ∧ n * sigma 1 (k - 1) < sigma 1 k ∧ n * sigma 1 (k + 1) < sigma 1 k

private lemma prime_power_bound (p a : ℕ) (hp : p.Prime) :
    ((∑ j ∈ range (a + 1), p ^ j : ℕ) : ℝ) / (p : ℝ) ^ a ≤
      (p : ℝ) / (p - 1) := by
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hone : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hgeom := geom_sum_mul (p : ℝ) (a + 1)
  simp only [Nat.cast_sum, Nat.cast_pow]
  apply (div_le_iff₀ (pow_pos hpos a)).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by linarith : (0 : ℝ) < p - 1)).2
  nlinarith [pow_succ (p : ℝ) a]

private lemma sigma_product_bound (m : ℕ) (hm : m ≠ 0) :
    (sigma 1 m : ℝ) / m ≤ ∏ p ∈ m.primeFactors, (p : ℝ) / (p - 1) := by
  have hden : (m : ℝ) = ∏ p ∈ m.primeFactors, (p : ℝ) ^ m.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hm
  rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm, Nat.cast_prod,
    hden, ← prod_div_distrib]
  apply prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    simpa only [mul_one] using prime_power_bound p (m.factorization p)
      (Nat.prime_of_mem_primeFactors hp)

private lemma rough_abundancy (x m : ℕ) (hx : 4 ≤ x) (hm : m ≠ 0)
    (hsize : m ≤ 4 ^ x + 1) (hrough : ∀ p ∈ m.primeFactors, x < p) :
    (sigma 1 m : ℝ) < 3 * m := by
  have hrad : 4 ^ m.primeFactors.card ≤ m := by
    calc
      _ = ∏ p ∈ m.primeFactors, 4 := by simp
      _ ≤ ∏ p ∈ m.primeFactors, p := prod_le_prod' (fun p hp => by
        have := hrough p hp
        omega)
      _ ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m)
  have hcard : m.primeFactors.card ≤ x := by
    by_contra h
    have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 4) (by omega : x + 1 ≤ m.primeFactors.card)
    have hpos : 0 < 4 ^ x := by positivity
    rw [pow_succ] at hpow
    omega
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hprod : (sigma 1 m : ℝ) / m ≤ (1 + (x : ℝ)⁻¹) ^ x := by
    calc
      _ ≤ ∏ p ∈ m.primeFactors, (p : ℝ) / (p - 1) := sigma_product_bound m hm
      _ ≤ ∏ p ∈ m.primeFactors, (1 + (x : ℝ)⁻¹) := by
        apply prod_le_prod
        · intro p hp
          have hpone : (1 : ℝ) < p := by
            exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
          exact div_nonneg (by positivity) (by linarith)
        · intro p hp
          have hpxnat : x + 1 ≤ p := by have := hrough p hp; omega
          have hpx : (x : ℝ) ≤ p - 1 := by
            have hcast : (x : ℝ) + 1 ≤ p := by exact_mod_cast hpxnat
            linarith
          have hpone : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
          rw [inv_eq_one_div]
          apply (div_le_iff₀ (by linarith : (0 : ℝ) < p - 1)).2
          have hi : (1 : ℝ) / (p - 1) ≤ 1 / x :=
            (div_le_div_iff₀ (by linarith : (0 : ℝ) < p - 1) hxpos).2 (by simpa using hpx)
          have hiMul := mul_le_mul_of_nonneg_right hi (by linarith : (0 : ℝ) ≤ p - 1)
          have hid : (1 : ℝ) / (p - 1) * (p - 1) = 1 :=
            div_mul_cancel₀ 1 (by linarith : (p : ℝ) - 1 ≠ 0)
          rw [hid] at hiMul
          nlinarith only [hiMul]
      _ = (1 + (x : ℝ)⁻¹) ^ m.primeFactors.card := by simp
      _ ≤ (1 + (x : ℝ)⁻¹) ^ x := pow_le_pow_right₀ (le_add_of_nonneg_right (inv_nonneg.mpr hxpos.le)) hcard
  have hlt := lt_of_le_of_lt (hprod.trans Real.one_add_inv_pow_le_exp) Real.exp_one_lt_three
  exact (div_lt_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hm : (0 : ℝ) < m)).1 hlt

private lemma large_primorial (n : ℕ) :
    ∃ x : ℕ, 4 ≤ x ∧ 6 * (n : ℝ) * primorial x < sigma 1 (primorial x) := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Finset Nat.Primes, 6 * (n : ℝ) < ∑ p ∈ s, (1 : ℝ) / p := by
    by_contra h
    push Not at h
    exact Nat.Primes.not_summable_one_div (summable_of_sum_le (by intro p; positivity) h)
  let x := max 4 (s.sup fun p => (p : ℕ))
  have hx : 4 ≤ x := le_max_left _ _
  have hP := primorial_pos x
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Subtype.val_injective
  have hsub : s.image (fun p : Nat.Primes => (p : ℕ)) ⊆ (primorial x).divisors := by
    intro p hp
    obtain ⟨q, hq, heq⟩ := mem_image.mp hp
    subst p
    apply Nat.mem_divisors.mpr
    refine ⟨q.property.dvd_primorial_iff.mpr ?_, ne_of_gt hP⟩
    exact (le_sup (f := fun p : Nat.Primes => (p : ℕ)) hq).trans (le_max_right _ _)
  have hsum : ∑ p ∈ s, (1 : ℝ) / p ≤ (sigma 1 (primorial x) : ℝ) / primorial x := by
    rw [← D5.S3.Arith.GoldenResourceOptimalInteger.reciprocal_divisor_sum hP]
    calc
      _ = ∑ p ∈ s.image (fun p : Nat.Primes => (p : ℕ)), (p : ℝ)⁻¹ := by
        rw [sum_image (fun a _ b _ h => hinj h)]
        simp only [one_div]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
  refine ⟨x, hx, ?_⟩
  exact (lt_div_iff₀ (by exact_mod_cast hP : (0 : ℝ) < primorial x)).1 (hs.trans_le hsum)

private lemma neighbour_rough (x : ℕ) (hx : 4 ≤ x) :
    (∀ p ∈ (primorial x - 1).primeFactors, x < p) ∧
    (∀ p ∈ (primorial x + 1).primeFactors, x < p) := by
  have hP : 2 ≤ primorial x := by
    simpa using primorial_mono (by omega : 2 ≤ x)
  constructor
  · intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    by_contra h
    have hdP := hprime.dvd_primorial_iff.mpr (by omega : p ≤ x)
    have hdOne : p ∣ 1 := by
      have h := Nat.dvd_sub hdP hd
      simpa [Nat.sub_sub_self (by omega : 1 ≤ primorial x)] using h
    exact hprime.not_dvd_one hdOne
  · intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    by_contra h
    have hdP := hprime.dvd_primorial_iff.mpr (by omega : p ≤ x)
    have hdOne : p ∣ 1 := by
      have h := Nat.dvd_sub hd hdP
      simpa using h
    exact hprime.not_dvd_one hdOne

/-- Every requested factor is attained simultaneously on both sides of a primorial. -/
theorem result : claim := by
  intro n
  obtain ⟨x, hx, hlarge⟩ := large_primorial n
  have hP : 2 ≤ primorial x := by
    simpa using primorial_mono (by omega : 2 ≤ x)
  obtain ⟨hminus, hplus⟩ := neighbour_rough x hx
  have hbound := primorial_le_four_pow x
  have hm := rough_abundancy x (primorial x - 1) hx (by omega) (by omega) hminus
  have hp := rough_abundancy x (primorial x + 1) hx (by omega) (by omega) hplus
  have hPR : (2 : ℝ) ≤ primorial x := by exact_mod_cast hP
  have hsub : ((primorial x - 1 : ℕ) : ℝ) = primorial x - 1 := by
    exact_mod_cast Nat.cast_sub (by omega : 1 ≤ primorial x)
  have hadd : ((primorial x + 1 : ℕ) : ℝ) = primorial x + 1 := by simp
  have hn : (0 : ℝ) ≤ n := by positivity
  have hspos := sigma_pos 1 (primorial x) (by omega)
  refine ⟨primorial x, hP, ?_, ?_⟩
  · apply (Nat.cast_lt (α := ℝ)).mp
    push_cast
    rw [hsub] at hm
    nlinarith
  · apply (Nat.cast_lt (α := ℝ)).mp
    push_cast
    rw [hadd] at hp
    nlinarith

end D5.S3.Arith.Robin.SigmaNeighbourPeak
