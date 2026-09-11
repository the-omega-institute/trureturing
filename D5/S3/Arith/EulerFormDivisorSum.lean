/- GID: D5/S3/Arith/EulerFormDivisorSum
   generality: G
   mirror-B: D5/B/S3/Arith/EulerFormDivisorSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Euler-form odd numbers satisfy the strict unitary-plus-squarefree divisor-sum bound. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The Euler-form inclusion question of OEIS A388986

The two functions below are the actual filtered divisor sums. All analytic
bounds use rationals and explicitly positive denominators.
-/

namespace D5.S3.Arith.EulerFormDivisorSum

open Finset

noncomputable section

/-- Sum of the unitary divisors, including 1 and the number itself. -/
def unitarySum (N : ℕ) : ℕ :=
  ∑ d ∈ N.divisors.filter (fun d => Nat.Coprime d (N / d)), d

/-- Sum of the squarefree divisors. -/
def squarefreeSum (N : ℕ) : ℕ := ∑ d ∈ N.divisors.filter Squarefree, d

private theorem reciprocal_square_product_le (F : Finset ℕ) (b : ℕ) (hb : 1 < b)
    (hF : ∀ q ∈ F, b ≤ q) :
    (∏ q ∈ F, (1 + 1 / (q : ℚ)^2)) ≤ (b : ℚ) / ((b : ℚ) - 1) := by
  induction F using Finset.induction_on_min generalizing b with
  | empty =>
      simp only [prod_empty]
      have hb' : (1 : ℚ) < b := by exact_mod_cast hb
      apply (le_div_iff₀ (by linarith : (0 : ℚ) < b - 1)).2
      linarith
  | insert q F hq ih =>
      have hbq : b ≤ q := hF q (mem_insert_self _ _)
      have hq1 : 1 < q := lt_of_lt_of_le hb hbq
      have hq' : (1 : ℚ) < q := by exact_mod_cast hq1
      have hq0 : (q : ℚ) ≠ 0 := by positivity
      have hnot : q ∉ F := fun h => (hq q h).false
      rw [prod_insert hnot]
      have ht := ih (q+1) (by omega) (fun x hx => hq x hx)
      push_cast at ht
      have hb' : (1 : ℚ) < b := by exact_mod_cast hb
      have hbq' : (b : ℚ) ≤ q := by exact_mod_cast hbq
      calc
        _ ≤ (1 + 1 / (q : ℚ)^2) * (((q : ℚ)+1)/(q : ℚ)) := by
          apply mul_le_mul_of_nonneg_left
          · simpa using ht
          · positivity
        _ ≤ (q : ℚ) / ((q : ℚ)-1) := by
          apply (le_div_iff₀ (by linarith : (0 : ℚ) < q - 1)).2
          field_simp
          nlinarith
        _ ≤ (b : ℚ) / ((b : ℚ)-1) := by
          apply (div_le_div_iff₀ (by linarith) (by linarith)).2
          nlinarith

private theorem unitary_divisor_product {N d : ℕ} (hn : N ≠ 0) (hd : d ∣ N)
    (hc : d.Coprime (N / d)) :
    d = ∏ q ∈ d.primeFactors, q ^ N.factorization q := by
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn hd
  nth_rw 1 [Nat.prod_primeFactors_pow_factorization hd0]
  apply prod_congr rfl
  intro q hq
  congr 1
  have hf := Nat.factorization_eq_of_coprime_left hc (List.mem_toFinset.mp hq)
  simpa [Nat.mul_div_cancel' hd] using hf.symm

private theorem unitarySum_le_product (N : ℕ) (hn : N ≠ 0) :
    unitarySum N ≤ ∏ q ∈ N.primeFactors, (q ^ N.factorization q + 1) := by
  let D := N.divisors.filter (fun d => Nat.Coprime d (N / d))
  let g := fun F : Finset ℕ => ∏ q ∈ F, q ^ N.factorization q
  have hv : ∀ d ∈ D, d = g d.primeFactors := by
    intro d hd
    exact unitary_divisor_product hn (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)
      (mem_filter.mp hd).2
  have hi : Set.InjOn Nat.primeFactors D := by
    intro d hd e he h
    rw [hv d hd, hv e he, h]
  calc
    unitarySum N = ∑ d ∈ D, g d.primeFactors := sum_congr rfl hv
    _ = ∑ F ∈ D.image Nat.primeFactors, g F := (sum_image hi).symm
    _ ≤ ∑ F ∈ N.primeFactors.powerset, g F := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro F hF
        obtain ⟨d, hd, rfl⟩ := mem_image.mp hF
        exact mem_powerset.mpr
          (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1) hn)
      · intros; exact Nat.zero_le _
    _ = _ := (prod_add_one _).symm

private theorem squarefreeSum_eq_product (N : ℕ) (hn : N ≠ 0) :
    squarefreeSum N = ∏ q ∈ N.primeFactors, (q + 1) := by
  rw [squarefreeSum, Nat.sum_divisors_filter_squarefree hn, Nat.factors_eq]
  simpa only [List.toFinset_coe, Nat.toFinset_factors, Finset.prod_val, id_eq] using
    (prod_add_one (f := fun q : ℕ => q) N.primeFactors).symm

private theorem squarefree_factor_le {b q : ℕ} (hb : 2 ≤ b) (hbq : b ≤ q) :
    ((q : ℚ)+1)/(q : ℚ)^2 ≤ ((b : ℚ)+1)/(b : ℚ)^2 := by
  have hb' : (2 : ℚ) ≤ b := by exact_mod_cast hb
  have hbq' : (b : ℚ) ≤ q := by exact_mod_cast hbq
  have hq' : (2 : ℚ) ≤ q := hb'.trans hbq'
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hbq')
    (by positivity : (0 : ℚ) ≤ (b : ℚ)*(q : ℚ) + b + q)]

private theorem squarefree_product_le (F : Finset ℕ) (b : ℕ) (hb : 2 ≤ b)
    (hne : F.Nonempty) (hF : ∀ q ∈ F, b ≤ q) :
    (∏ q ∈ F, ((q : ℚ)+1)/(q : ℚ)^2) ≤ ((b : ℚ)+1)/(b : ℚ)^2 := by
  obtain ⟨q, hq⟩ := hne
  have hunit : ∀ x ∈ F, ((x : ℚ)+1)/(x : ℚ)^2 ≤ 1 := by
    intro x hx
    have hx' : (2 : ℚ) ≤ x := by exact_mod_cast le_trans hb (hF x hx)
    apply (div_le_one (by positivity : (0 : ℚ) < (x : ℚ)^2)).2
    nlinarith
  calc
    _ ≤ ∏ x ∈ ({q} : Finset ℕ), ((x : ℚ)+1)/(x : ℚ)^2 :=
      prod_le_prod_of_subset_of_le_one (singleton_subset_iff.mpr hq)
        (fun x _ => by positivity) (fun x hx _ => hunit x hx)
    _ = ((q : ℚ)+1)/(q : ℚ)^2 := by simp
    _ ≤ _ := squarefree_factor_le hb (hF q hq)

private theorem joint_products_lt (F : Finset ℕ) (hne : F.Nonempty)
    (hF : ∀ q ∈ F, 3 ≤ q ∧ q ≠ 4) :
    (∏ q ∈ F, (1 + 1/(q : ℚ)^2)) +
      (∏ q ∈ F, ((q : ℚ)+1)/(q : ℚ)^2) < 5/3 := by
  by_cases h3 : 3 ∈ F
  · have hT : ∀ q ∈ F.erase 3, 5 ≤ q := by
      intro q hq
      have := hF q (mem_erase.mp hq).2
      have := (mem_erase.mp hq).1
      omega
    by_cases he : F.erase 3 = ∅
    · have hsingle : F = {3} := by
        rw [← insert_erase h3, he]
        simp
      rw [hsingle]
      norm_num
    · have hA := reciprocal_square_product_le (F.erase 3) 5 (by decide) hT
      have hB := squarefree_product_le (F.erase 3) 5 (by decide)
        (nonempty_iff_ne_empty.mpr he) hT
      rw [← insert_erase h3, prod_insert (notMem_erase _ _),
        prod_insert (notMem_erase _ _)]
      norm_num at hA hB ⊢
      nlinarith
  · have hF5 : ∀ q ∈ F, 5 ≤ q := by
      intro q hq
      have := hF q hq
      have : q ≠ 3 := fun h => h3 (h ▸ hq)
      omega
    have hA := reciprocal_square_product_le F 5 (by decide) hF5
    have hB := squarefree_product_le F 5 (by decide) hne hF5
    norm_num at hA hB ⊢
    linarith

private theorem normalized_sums_le (N : ℕ) (hn : N ≠ 0) :
    (unitarySum N : ℚ) / N + (squarefreeSum N : ℚ) / N ≤
      (∏ q ∈ N.primeFactors, (1 + 1 / (q : ℚ) ^ N.factorization q)) +
      (∏ q ∈ N.primeFactors, ((q : ℚ) + 1) / (q : ℚ) ^ N.factorization q) := by
  have hprod : (∏ q ∈ N.primeFactors, (q : ℚ) ^ N.factorization q) = N := by
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  apply add_le_add
  · have hu : (unitarySum N : ℚ) ≤
        ∏ q ∈ N.primeFactors, ((q : ℚ) ^ N.factorization q + 1) := by
      exact_mod_cast unitarySum_le_product N hn
    calc
      _ ≤ (∏ q ∈ N.primeFactors, ((q : ℚ) ^ N.factorization q + 1)) / N :=
        div_le_div_of_nonneg_right hu (by positivity)
      _ = _ := by
        rw [← hprod, ← prod_div_distrib]
        apply prod_congr rfl
        intro q hq
        have hq0 : (q : ℚ) ^ N.factorization q ≠ 0 := by
          exact pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).ne_zero)
        rw [add_div, div_self hq0]
  · apply le_of_eq
    have hs : (squarefreeSum N : ℚ) = ∏ q ∈ N.primeFactors, ((q : ℚ) + 1) := by
      exact_mod_cast squarefreeSum_eq_product N hn
    rw [hs, ← hprod, prod_div_distrib]

private theorem support_products_lt (F : Finset ℕ) (p : ℕ) (e : ℕ → ℕ)
    (hp : 5 ≤ p) (hpe : 1 ≤ e p) (hpF : p ∉ F) (hne : F.Nonempty)
    (hF : ∀ q ∈ F, 3 ≤ q ∧ q ≠ 4) (he : ∀ q ∈ F, 2 ≤ e q) :
    (∏ q ∈ insert p F, (1 + 1 / (q : ℚ) ^ e q)) +
      (∏ q ∈ insert p F, ((q : ℚ) + 1) / (q : ℚ) ^ e q) < 2 := by
  have hp' : (5 : ℚ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℚ) < p := by linarith
  have hppow : (p : ℚ) ≤ (p : ℚ) ^ e p := by
    simpa using pow_le_pow_right₀ (by linarith : (1 : ℚ) ≤ p) hpe
  have hpbound : 1 + 1 / (p : ℚ) ≤ 6 / 5 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 5) hp'
    linarith
  have hpA : 1 + 1 / (p : ℚ) ^ e p ≤ 6 / 5 :=
    (add_le_add (le_refl 1) (one_div_le_one_div_of_le hp0 hppow)).trans hpbound
  have hpB : ((p : ℚ) + 1) / (p : ℚ) ^ e p ≤ 6 / 5 := by
    calc
      _ ≤ ((p : ℚ) + 1) / p :=
        div_le_div_of_nonneg_left (by positivity) hp0 hppow
      _ = 1 + 1 / (p : ℚ) := by rw [add_div, div_self (ne_of_gt hp0)]
      _ ≤ _ := hpbound
  have hpow : ∀ q ∈ F, (q : ℚ)^2 ≤ (q : ℚ) ^ e q := by
    intro q hq
    have hq' : (3 : ℚ) ≤ q := by exact_mod_cast (hF q hq).1
    exact pow_le_pow_right₀ (by linarith) (he q hq)
  have hA : (∏ q ∈ F, (1 + 1 / (q : ℚ) ^ e q)) ≤
      ∏ q ∈ F, (1 + 1 / (q : ℚ)^2) := by
    apply prod_le_prod (fun _ _ => by positivity)
    intro q hq
    have hq' : (0 : ℚ) < q := by exact_mod_cast (by have := (hF q hq).1; omega : 0 < q)
    exact add_le_add (le_refl 1) (one_div_le_one_div_of_le (by positivity) (hpow q hq))
  have hB : (∏ q ∈ F, ((q : ℚ) + 1) / (q : ℚ) ^ e q) ≤
      ∏ q ∈ F, ((q : ℚ) + 1) / (q : ℚ)^2 := by
    apply prod_le_prod (fun _ _ => by positivity)
    intro q hq
    have hq' : (0 : ℚ) < q := by exact_mod_cast (by have := (hF q hq).1; omega : 0 < q)
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (hpow q hq)
  rw [prod_insert hpF, prod_insert hpF]
  calc
    _ ≤ (6 / 5 : ℚ) * (∏ q ∈ F, (1 + 1 / (q : ℚ)^2)) +
        (6 / 5 : ℚ) * (∏ q ∈ F, ((q : ℚ) + 1) / (q : ℚ)^2) := by
      exact add_le_add (mul_le_mul hpA hA (by positivity) (by norm_num))
        (mul_le_mul hpB hB (by positivity) (by norm_num))
    _ < 2 := by have := joint_products_lt F hne hF; linarith

/-- Every Euler-form number from A228058 satisfies the strict inequality
defining A388986, with the two sums taken over the actual divisors. -/
theorem euler_form_lt (p a r : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hr : Odd r) (hr1 : 1 < r) (hpr : p.Coprime r) :
    unitarySum (p ^ (4 * a + 1) * r^2) + squarefreeSum (p ^ (4 * a + 1) * r^2) <
      2 * (p ^ (4 * a + 1) * r^2) := by
  let N := p ^ (4 * a + 1) * r^2
  have hr0 : r ≠ 0 := by omega
  have hpp0 : p ^ (4 * a + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hrp0 : r^2 ≠ 0 := pow_ne_zero _ hr0
  have hn : N ≠ 0 := mul_ne_zero hpp0 hrp0
  have hp5 : 5 ≤ p := by have := hp.two_le; omega
  have hsupport : N.primeFactors = insert p r.primeFactors := by
    dsimp [N]
    rw [Nat.primeFactors_mul hpp0 hrp0,
      Nat.primeFactors_prime_pow (by omega) hp, Nat.primeFactors_pow r (by decide)]
    simp only [singleton_union]
  have hpF : p ∉ r.primeFactors := fun h =>
    (hp.coprime_iff_not_dvd.mp hpr) (Nat.dvd_of_mem_primeFactors h)
  have hF : ∀ q ∈ r.primeFactors, 3 ≤ q ∧ q ≠ 4 := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact hr.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
    constructor
    · have := hqp.two_le; omega
    · rintro rfl; exact (by decide : ¬Nat.Prime 4) hqp
  have hpe : 1 ≤ N.factorization p := by
    dsimp [N]
    rw [Nat.factorization_mul hpp0 hrp0]
    simp only [Finsupp.add_apply, Nat.factorization_pow_self hp]
    omega
  have he : ∀ q ∈ r.primeFactors, 2 ≤ N.factorization q := by
    intro q hq
    have hpos := (Nat.prime_of_mem_primeFactors hq).factorization_pos_of_dvd
      hr0 (Nat.dvd_of_mem_primeFactors hq)
    dsimp [N]
    rw [Nat.factorization_mul hpp0 hrp0]
    simp only [Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    omega
  have hb := support_products_lt r.primeFactors p N.factorization hp5 hpe hpF
    (Nat.nonempty_primeFactors.mpr hr1) hF he
  rw [← hsupport] at hb
  have hlt := (normalized_sums_le N hn).trans_lt hb
  rw [← add_div] at hlt
  have hn' : (0 : ℚ) < N := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h := (div_lt_iff₀ hn').mp hlt
  exact_mod_cast h

end
end D5.S3.Arith.EulerFormDivisorSum
