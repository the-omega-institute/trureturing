/- GID: D5/S3/Arith/Divisors/PrimeReciprocalProduct
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/PrimeReciprocalProduct
   mirror-E: none(waiver:symbolic-prime-product-estimate)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/PrimeReciprocalProduct.missing_support_product_ge_two; premises=D5/S3/Arith/Divisors/PrimeReciprocalProduct.primes_le_23_card,D5/S3/Arith/Divisors/PrimeReciprocalProduct.primes_le_29_card,D5/S3/Arith/Divisors/PrimeReciprocalProduct.prime_product_29_lower,D5/S3/Arith/Divisors/PrimeReciprocalProduct.prime_product_cutoff
   digest: Squarefree decomposition bounds harmonic sums by finite prime products. -/

import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.ExponentialBounds
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

private theorem primes_le_23_card : (Nat.primesLE 23).card = 9 := by decide

private theorem reciprocal_product_small_support (F : Finset ℕ)
    (hF : ∀ p ∈ F, Nat.Prime p) (hc : F.card ≤ 9) :
    (∏ p ∈ F, (1 + (p : ℚ)⁻¹)) ≤
      ∏ p ∈ Nat.primesLE 23, (1 + (p : ℚ)⁻¹) := by
  classical
  let A := Nat.primesLE 23
  let f : ℕ → ℚ := fun p => 1 + (p : ℚ)⁻¹
  let c : ℚ := 1 + (23 : ℚ)⁻¹
  have hAc : A.card = 9 := primes_le_23_card
  have hcard : (F \ A).card ≤ (A \ F).card := by
    have h1 := card_sdiff_add_card_inter F A
    have h2 := card_sdiff_add_card_inter A F
    rw [inter_comm A F] at h2
    omega
  have hlarge : (∏ p ∈ F \ A, f p) ≤ c ^ (F \ A).card := by
    calc
      _ ≤ ∏ _p ∈ F \ A, c := prod_le_prod₀ (fun _ _ => by positivity) (by
        intro p hp
        have hprime := hF p (mem_sdiff.mp hp).1
        have h23 : 23 < p := by
          by_contra! h
          exact (mem_sdiff.mp hp).2 (Nat.mem_primesLE.mpr ⟨h, hprime⟩)
        dsimp [f, c]
        gcongr
        exact_mod_cast h23.le)
      _ = _ := by simp
  have hsmall : c ^ (A \ F).card ≤ ∏ p ∈ A \ F, f p := by
    calc
      _ = ∏ _p ∈ A \ F, c := by simp
      _ ≤ _ := prod_le_prod₀ (fun _ _ => by norm_num [c]) (by
        intro p hp
        have hpA := (mem_sdiff.mp hp).1
        have hp0 : (0 : ℚ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hpA).pos
        have hp23 : (p : ℚ) ≤ 23 := by exact_mod_cast Nat.le_of_mem_primesLE hpA
        dsimp [c, f]
        exact add_le_add_right (inv_anti₀ hp0 hp23) 1)
  have hmid : (∏ p ∈ F \ A, f p) ≤ ∏ p ∈ A \ F, f p :=
    hlarge.trans ((pow_le_pow_right₀ (by norm_num [c] : (1 : ℚ) ≤ c) hcard).trans hsmall)
  have h1 := prod_inter_mul_prod_sdiff F A f
  have h2 := prod_inter_mul_prod_sdiff A F f
  rw [inter_comm A F] at h2
  change (∏ p ∈ F, f p) ≤ ∏ p ∈ A, f p
  rw [← h1, ← h2]
  exact mul_le_mul_of_nonneg_left hmid (prod_nonneg (fun _ _ => by positivity))

private theorem primes_le_29_card : (Nat.primesLE 29).card = 10 := by decide

private theorem prime_product_29_lower :
    3 ^ 20 < ∏ p ∈ Nat.primesLE 29, p := by decide

private theorem prime_product_large_support (F : Finset ℕ)
    (hF : ∀ p ∈ F, Nat.Prime p) (hc : 10 ≤ F.card) :
    3 ^ (3 * F.card - 10) < ∏ p ∈ F, p := by
  classical
  let A := Nat.primesLE 29
  have hAc : A.card = 10 := primes_le_29_card
  have hcard : (F \ A).card = (A \ F).card + (F.card - 10) := by
    have h1 := card_sdiff_add_card_inter F A
    have h2 := card_sdiff_add_card_inter A F
    rw [inter_comm A F] at h2
    omega
  have hlarge : 31 ^ (F \ A).card ≤ ∏ p ∈ F \ A, p := by
    calc
      _ = ∏ _p ∈ F \ A, 31 := by simp
      _ ≤ _ := prod_le_prod (by
        intro p hp
        have hprime := hF p (mem_sdiff.mp hp).1
        have h29 : 29 < p := by
          by_contra! h
          exact (mem_sdiff.mp hp).2 (Nat.mem_primesLE.mpr ⟨h, hprime⟩)
        have hp30 : p ≠ 30 := by intro h; norm_num [h] at hprime
        omega)
  have hsmall : (∏ p ∈ A \ F, p) ≤ 31 ^ (A \ F).card := by
    calc
      _ ≤ ∏ _p ∈ A \ F, 31 := prod_le_prod (by
        intro p hp
        exact (Nat.le_of_mem_primesLE (mem_sdiff.mp hp).1).trans (by decide))
      _ = _ := by simp
  have hmid : (∏ p ∈ A \ F, p) * 31 ^ (F.card - 10) ≤ ∏ p ∈ F \ A, p := by
    calc
      _ ≤ 31 ^ (A \ F).card * 31 ^ (F.card - 10) := Nat.mul_le_mul_right _ hsmall
      _ = 31 ^ (F \ A).card := by rw [← pow_add, hcard]
      _ ≤ _ := hlarge
  have h1 := prod_inter_mul_prod_sdiff F A (fun p : ℕ => p)
  have h2 := prod_inter_mul_prod_sdiff A F (fun p : ℕ => p)
  rw [inter_comm A F] at h2
  have hprod : (∏ p ∈ A, p) * 31 ^ (F.card - 10) ≤ ∏ p ∈ F, p := by
    rw [← h1, ← h2, mul_assoc]
    exact Nat.mul_le_mul_left _ hmid
  have hexp : 3 * F.card - 10 = 20 + 3 * (F.card - 10) := by omega
  calc
    _ = 3 ^ 20 * 27 ^ (F.card - 10) := by rw [hexp, pow_add, pow_mul]; norm_num
    _ ≤ 3 ^ 20 * 31 ^ (F.card - 10) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) _)
    _ < (∏ p ∈ A, p) * 31 ^ (F.card - 10) :=
      Nat.mul_lt_mul_of_pos_right prime_product_29_lower (by positivity)
    _ ≤ _ := hprod

private theorem large_support_prime_quotient (m : ℕ) (hm : 0 < m)
    (hc : 10 ≤ m.primeFactors.card) :
    2 * (∏ p ∈ m.primeFactors, (1 + (p : ℚ)⁻¹)) <
      ∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹) := by
  let r := m.primeFactors.card
  let D : ℚ := ∏ p ∈ m.primeFactors, (1 + (p : ℚ)⁻¹)
  let P : ℚ := ∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)
  have hDpos : 0 < D := prod_pos (fun _ _ => by positivity)
  have hPpos : 0 < P := prod_pos (fun _ _ => by positivity)
  have hD : D ^ 2 ≤ (9 / 4 : ℚ) * r :=
    prime_support_product_sq_le _ (card_pos.mp (by omega))
      (fun _ hp => Nat.prime_of_mem_primeFactors hp)
  have hg : 3 ^ (3 * r - 10) < m :=
    (prime_product_large_support _ (fun _ hp => Nat.prime_of_mem_primeFactors hp) hc).trans_le
      (Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m))
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hgR : (3 : ℝ) ^ (3 * r - 10) < m := by exact_mod_cast hg
  have hl := Real.log_lt_log (by positivity : (0 : ℝ) < 3 ^ (3 * r - 10)) hgR
  rw [Real.log_pow] at hl
  have hlog3 : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
  have hrR : (10 : ℝ) ≤ r := by exact_mod_cast hc
  have hexp : ((3 * r - 10 : ℕ) : ℝ) = 3 * (r : ℝ) - 10 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul]
    norm_num
  rw [hexp] at hl
  have hlog : 3 * (r : ℝ) - 10 < Real.log m := by nlinarith
  have hlog0 : 0 < Real.log m := by linarith
  have hlogSq : 36 * (r : ℝ) < (Real.log m) ^ 2 := by
    have hs := sq_nonneg ((r : ℝ) - 10)
    have hx := mul_pos (sub_pos.mpr hlog) (by linarith : 0 < Real.log m + (3 * (r : ℝ) - 10))
    nlinarith
  have hh : (harmonic m : ℝ) < 2 * (P : ℝ) := by
    exact_mod_cast harmonic_lt_twice_prime_product m hm
  have hlogH : Real.log m ≤ (harmonic m : ℝ) :=
    (Real.log_le_log hmR (by push_cast; linarith : (m : ℝ) ≤ (m + 1 : ℕ))).trans
      (log_add_one_le_harmonic m)
  have hDP : (2 : ℝ) * (D : ℝ) < (P : ℝ) := by
    have hDr : (D : ℝ) ^ 2 ≤ (9 / 4 : ℝ) * r := by
      have hcast : ((D ^ 2 : ℚ) : ℝ) ≤ (((9 / 4 : ℚ) * r : ℚ) : ℝ) :=
        Rat.cast_le.mpr hD
      simpa only [Rat.cast_pow, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
        Rat.cast_natCast] using hcast
    have hPr : (0 : ℝ) < P := by exact_mod_cast hPpos
    have hDr0 : (0 : ℝ) < D := by exact_mod_cast hDpos
    have hs := mul_pos (sub_pos.mpr (hlogH.trans_lt hh)) (by linarith : 0 < 2 * (P : ℝ) + Real.log m)
    nlinarith
  exact_mod_cast hDP

private theorem prime_product_cutoff :
    2 * (∏ p ∈ Nat.primesLE 23, (1 + (p : ℚ)⁻¹)) ≤
      ∏ p ∈ Nat.primesLE 1000, (1 + (p : ℚ)⁻¹) := by
  decide +kernel

/-- Once the radical quotient is at least one thousand, its missing support
alone makes the reciprocal prime product at least two. -/
theorem missing_support_product_ge_two (m : ℕ) (hm : 1000 ≤ m) :
    2 ≤ ∏ p ∈ Nat.primesLE m \ m.primeFactors, (1 + (p : ℚ)⁻¹) := by
  have hm0 : 0 < m := by omega
  have hsub : m.primeFactors ⊆ Nat.primesLE m := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨Nat.le_of_dvd hm0 (Nat.dvd_of_mem_primeFactors hp),
      Nat.prime_of_mem_primeFactors hp⟩
  let D : ℚ := ∏ p ∈ m.primeFactors, (1 + (p : ℚ)⁻¹)
  let B : ℚ := ∏ p ∈ Nat.primesLE m \ m.primeFactors, (1 + (p : ℚ)⁻¹)
  let P : ℚ := ∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)
  have hD : 0 < D := prod_pos (fun _ _ => by positivity)
  have hsplit : B * D = P := prod_sdiff hsub
  have htwo : 2 * D ≤ P := by
    by_cases hc : m.primeFactors.card ≤ 9
    · have hsmall := reciprocal_product_small_support m.primeFactors
        (fun _ hp => Nat.prime_of_mem_primeFactors hp) hc
      have hmono : (∏ p ∈ Nat.primesLE 1000, (1 + (p : ℚ)⁻¹)) ≤ P :=
        prod_le_prod_of_subset_of_one_le₀ (by
          intro p hp
          exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans hm,
            Nat.prime_of_mem_primesLE hp⟩) (fun _ _ => by positivity)
          (fun _ _ _ => le_add_of_nonneg_right (by positivity))
      exact (mul_le_mul_of_nonneg_left hsmall (by norm_num)).trans
        (prime_product_cutoff.trans hmono)
    · exact (large_support_prime_quotient m hm0 (by omega)).le
  change 2 ≤ B
  nlinarith [htwo]

end D5.S3.Arith.Divisors.PrimeReciprocalProduct
