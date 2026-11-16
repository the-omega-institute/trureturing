/- GID: D5/S3/Arith/Divisors/PrimeReciprocalProduct
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/PrimeReciprocalProduct
   mirror-E: none(waiver:symbolic-prime-product-estimate)
   anchors: []
   utility: none
   digest: Squarefree decomposition bounds harmonic sums by finite prime products. -/

import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-! # Harmonic sums and finite reciprocal prime products -/

namespace D5.S3.Arith.Divisors.PrimeReciprocalProduct

open Finset

/-- The reciprocal divisor sum of the primorial, as a finite Euler product. -/
private theorem primorial_reciprocal_sum (m : ℕ) :
    (∑ d ∈ (primorial m).divisors, (d : ℚ)⁻¹) =
      ∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹) := by
  rw [← Nat.divisors_filter_squarefree_of_squarefree (squarefree_primorial m),
    Nat.sum_divisors_filter_squarefree (primorial_ne_zero m), Nat.factors_eq]
  simpa only [List.toFinset_coe, Nat.toFinset_factors, Finset.prod_val,
    Nat.cast_prod, prod_inv_distrib, primeFactors_primorial, id_eq, add_comm] using
    (prod_add_one (f := fun p : ℕ => (p : ℚ)⁻¹) (Nat.primesLE m)).symm

/-- Each positive integer injects into its square factor and squarefree kernel.
The rectangular reciprocal budget therefore controls the whole harmonic sum. -/
private theorem harmonic_le_square_budget (m : ℕ) :
    harmonic m ≤ (∑ a ∈ Icc 1 m, ((a : ℚ)^2)⁻¹) *
      ∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹) := by
  classical
  choose a b hab hsf using (fun k : ℕ => exists_sq_mul_squarefree k)
  let e : ℕ → ℕ × ℕ := fun k => (a k, b k)
  have ha : ∀ k ∈ Icc 1 m, 0 < a k := by
    intro k hk
    have hk0 : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
    by_contra h
    have hz : a k = 0 := by omega
    exact hk0 (by simpa [hz] using (hab k).symm)
  have he : Set.InjOn e (Icc 1 m) := by
    intro k hk l hl h
    have h1 : a k = a l := congrArg Prod.fst h
    have h2 : b k = b l := congrArg Prod.snd h
    calc k = a k ^ 2 * b k := (hab k).symm
         _ = a l ^ 2 * b l := by rw [h1, h2]
         _ = l := hab l
  have hmem : image e (Icc 1 m) ⊆ (Icc 1 m).product (primorial m).divisors := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hz
    have hkm := (mem_Icc.mp hk).2
    have ha0 := ha k hk
    have hk0 : 0 < k := (mem_Icc.mp hk).1
    have hbk : b k ≤ k := Nat.le_of_dvd hk0
      ⟨a k ^ 2, by simpa [Nat.mul_comm] using (hab k).symm⟩
    have hak : a k ≤ k := Nat.le_of_dvd hk0
      ⟨a k * b k, (hab k).symm.trans (by ring)⟩
    refine mem_product.mpr ⟨mem_Icc.mpr ⟨ha0, hak.trans hkm⟩, ?_⟩
    exact Nat.mem_divisors.mpr ⟨(hsf k).dvd_primorial.trans
      (primorial_dvd_primorial (hbk.trans hkm)), primorial_ne_zero m⟩
  rw [harmonic_eq_sum_Icc]
  calc
    _ ≤ ∑ z ∈ (Icc 1 m).product (primorial m).divisors,
        ((z.1 : ℚ)^2)⁻¹ * (z.2 : ℚ)⁻¹ := by
      apply sum_le_sum_of_injOn e he hmem
      · intro k hk
        apply le_of_eq
        dsimp [e]
        rw [← mul_inv]
        congr 1
        exact_mod_cast (hab k).symm
      · intro z hz hz'
        positivity
    _ = _ := by
      rw [← primorial_reciprocal_sum, sum_mul_sum]
      exact sum_product ..

/-- A finite Euler product exceeds half the harmonic sum, with a positive
finite-endpoint correction. -/
theorem harmonic_lt_twice_prime_product (m : ℕ) (hm : 0 < m) :
    harmonic m < 2 * ∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹) := by
  have h := harmonic_le_square_budget m
  have hb := sum_Ioc_inv_sq_le_sub (α := ℚ) (by decide : 1 ≠ 0) hm
  have hs : (∑ a ∈ Icc 1 m, ((a : ℚ)^2)⁻¹) < 2 := by
    rw [← Ioc_insert_left hm, sum_insert (by simp)]
    norm_num at hb ⊢
    have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
    have : (0 : ℚ) < (m : ℚ)⁻¹ := inv_pos.mpr hmQ
    linarith
  have hp : (0 : ℚ) < ∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹) :=
    prod_pos (fun p hp => by positivity)
  exact h.trans_lt (mul_lt_mul_of_pos_right hs hp)

private theorem odd_product_sq_le (F : Finset ℕ)
    (hF : ∀ p ∈ F, 3 ≤ p ∧ p % 2 = 1) :
    (∏ p ∈ F, (1 + (p : ℚ)⁻¹)) ^ 2 ≤ F.card + 1 := by
  classical
  induction F using Finset.induction_on_max with
  | empty => norm_num
  | insert q F hq ih =>
    have hqF : q ∉ F := fun h => (hq q h).false
    have hq3 := (hF q (mem_insert_self _ _)).1
    have hqodd := (hF q (mem_insert_self _ _)).2
    have hF' : ∀ p ∈ F, 3 ≤ p ∧ p % 2 = 1 :=
      fun p hp => hF p (mem_insert_of_mem hp)
    have hi : Set.InjOn (fun p : ℕ => p / 2) F := by
      intro p hp t ht h
      have := (hF' p hp).2
      have := (hF' t ht).2
      change p / 2 = t / 2 at h
      omega
    have hs : F.image (fun p => p / 2) ⊆ Ico 1 (q / 2) := by
      intro p hp
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hp
      have := hF' t ht
      have := hq t ht
      exact mem_Ico.mpr ⟨by omega, by omega⟩
    have hc := card_le_card hs
    rw [card_image_of_injOn hi, Nat.card_Ico] at hc
    have hqcard : 2 * F.card + 3 ≤ q := by omega
    have hqQ : (0 : ℚ) < q := by exact_mod_cast (by omega : 0 < q)
    have hqcardQ : 2 * (F.card : ℚ) + 3 ≤ q := by exact_mod_cast hqcard
    have hstep : (F.card + 1 : ℚ) * (1 + (q : ℚ)⁻¹)^2 ≤ F.card + 2 := by
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hqQ)).mp
      field_simp
      nlinarith [mul_nonneg (sub_nonneg.mpr hqcardQ) (by positivity : (0 : ℚ) ≤ q)]
    rw [prod_insert hqF, mul_pow, card_insert_of_notMem hqF]
    push_cast
    calc
      _ ≤ (1 + (q : ℚ)⁻¹)^2 * (F.card + 1) :=
        mul_le_mul_of_nonneg_left (ih hF') (sq_nonneg _)
      _ ≤ _ := by nlinarith [hstep]

/-- For any nonempty set of distinct primes, the reciprocal product squared
is at most nine fourths times the support size. -/
theorem prime_support_product_sq_le (F : Finset ℕ) (hne : F.Nonempty)
    (hF : ∀ p ∈ F, Nat.Prime p) :
    (∏ p ∈ F, (1 + (p : ℚ)⁻¹)) ^ 2 ≤ (9 / 4 : ℚ) * F.card := by
  have hodd : ∀ p ∈ F.erase 2, 3 ≤ p ∧ p % 2 = 1 := by
    intro p hp
    have hpm := (mem_erase.mp hp).2
    have hp2 := (mem_erase.mp hp).1
    have ho := (hF p hpm).odd_of_ne_two hp2
    exact ⟨by have := (hF p hpm).two_le; omega, Nat.odd_iff.mp ho⟩
  by_cases h2 : 2 ∈ F
  · have h := odd_product_sq_le (F.erase 2) hodd
    rw [← insert_erase h2, prod_insert (notMem_erase _ _), mul_pow,
      card_insert_of_notMem (notMem_erase _ _)]
    norm_num
    nlinarith
  · have he : F.erase 2 = F := erase_eq_of_notMem h2
    rw [he] at hodd
    have h := odd_product_sq_le F hodd
    have hc : (1 : ℚ) ≤ F.card := by exact_mod_cast hne.card_pos
    nlinarith

end D5.S3.Arith.Divisors.PrimeReciprocalProduct
