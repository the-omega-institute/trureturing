/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/TailFamily
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/MakowskiSchinzel/TailFamily
   mirror-E: none(waiver:unbounded-prime-family-estimate)
   anchors: []
   utility: none
   digest: Finite prime families satisfy the large-support reciprocal tail estimate. -/

import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Basic

/-! # Finite prime-family bounds -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.MakowskiSchinzel

open Finset


open Finset

private theorem finite_geometric_budget (s : Finset ℕ) (x : ℚ)
    (hx : 0 ≤ x) (hx1 : x < 1) :
    ∑ i ∈ s, x ^ i ≤ 1 / (1 - x) := by
  have hsub : s ⊆ Ico 0 (s.sup id + 1) := by
    intro i hi
    simp only [mem_Ico, zero_le, true_and]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  calc
    _ ≤ ∑ i ∈ Ico 0 (s.sup id + 1), x ^ i :=
      sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => pow_nonneg hx i)
    _ ≤ _ := by
      simpa only [pow_zero] using
        (geom_sum_Ico_le_of_lt_one (m := 0) (n := s.sup id + 1) hx hx1)

private theorem finite_geometric_budget_strict (s : Finset ℕ) (x : ℚ)
    (hx : 0 < x) (hx1 : x < 1) :
    ∑ i ∈ s, x ^ i < 1 / (1 - x) := by
  let k := s.sup id + 1
  have hnot : k ∉ s := by
    intro hk
    have hle := Finset.le_sup (f := id) hk
    dsimp [k] at hle
    omega
  have hbound := finite_geometric_budget (insert k s) x hx.le hx1
  rw [sum_insert hnot] at hbound
  have hpos : 0 < x ^ k := pow_pos hx k
  linarith

private theorem finite_geometric_box_budget (s : Finset (ℕ × ℕ)) (x y : ℚ)
    (hx : 0 < x) (hx1 : x < 1) (hy : 0 < y) (hy1 : y < 1) :
    ∑ z ∈ s, x ^ z.1 * y ^ z.2 < 1 / (1 - x) * (1 / (1 - y)) := by
  have hsub : s ⊆ (s.image Prod.fst).product (s.image Prod.snd) := by
    intro z hz
    exact mem_product.mpr ⟨mem_image.mpr ⟨z, hz, rfl⟩, mem_image.mpr ⟨z, hz, rfl⟩⟩
  calc
    _ ≤ ∑ z ∈ (s.image Prod.fst).product (s.image Prod.snd),
        x ^ z.1 * y ^ z.2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => by positivity)
    _ = (∑ i ∈ s.image Prod.fst, x ^ i) *
        (∑ j ∈ s.image Prod.snd, y ^ j) := by
      rw [Finset.product_eq_sprod, Finset.sum_product, sum_mul_sum]
    _ ≤ (∑ i ∈ s.image Prod.fst, x ^ i) * (1 / (1 - y)) :=
      mul_le_mul_of_nonneg_left (finite_geometric_budget _ _ hy.le hy1)
        (sum_nonneg (fun _ _ => pow_nonneg hx.le _))
    _ < _ := mul_lt_mul_of_pos_right (finite_geometric_budget_strict _ _ hx hx1)
      (div_pos (by norm_num) (sub_pos.mpr hy1))

/-- A finite collection of even-even and odd-odd exponent pairs has the exact
uniform geometric upper budget, which no finite family attains. -/
theorem same_parity_geometric_budget (s t : Finset (ℕ × ℕ)) (r : ℚ)
    (hr : 1 < r) :
    (∑ z ∈ s, r / (2 ^ (2 * z.1 + 1) * r ^ (2 * z.2 + 1))) +
      (∑ z ∈ t, r / (2 ^ (2 * z.1 + 2) * r ^ (2 * z.2 + 2))) <
        r * (2 * r + 1) / (3 * (r ^ 2 - 1)) := by
  have hr0 : 0 < r := by linarith
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hy0 : 0 < (1 / r ^ 2 : ℚ) := by positivity
  have hy1 : (1 / r ^ 2 : ℚ) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  have hs := finite_geometric_box_budget s (1 / 4) (1 / r ^ 2)
    (by norm_num) (by norm_num) hy0 hy1
  have ht := finite_geometric_box_budget t (1 / 4) (1 / r ^ 2)
    (by norm_num) (by norm_num) hy0 hy1
  have hodd : ∀ z : ℕ × ℕ,
      r / (2 ^ (2 * z.1 + 1) * r ^ (2 * z.2 + 1)) =
        (1 / 2 : ℚ) * ((1 / 4) ^ z.1 * (1 / r ^ 2) ^ z.2) := by
    intro z
    simp only [pow_add, pow_mul, pow_one, div_pow]
    field_simp
    <;> ring
  have heven : ∀ z : ℕ × ℕ,
      r / (2 ^ (2 * z.1 + 2) * r ^ (2 * z.2 + 2)) =
        (1 / (4 * r)) * ((1 / 4 : ℚ) ^ z.1 * (1 / r ^ 2) ^ z.2) := by
    intro z
    simp only [pow_add, pow_mul, div_pow]
    field_simp
    <;> ring
  simp_rw [hodd, heven]
  rw [← mul_sum, ← mul_sum]
  have h := add_lt_add (mul_lt_mul_of_pos_left hs (by norm_num : (0 : ℚ) < 1 / 2))
    (mul_lt_mul_of_pos_left ht (by positivity : (0 : ℚ) < 1 / (4 * r)))
  convert h using 1 <;> field_simp <;> ring

theorem even_first_geometric_budget (s : Finset (ℕ × ℕ)) (r : ℚ)
    (hr : 1 < r) :
    ∑ z ∈ s, r / (2 ^ (2 * z.1 + 2) * r ^ (z.2 + 1)) <
      r / (3 * (r - 1)) := by
  have hr0 : 0 < r := by linarith
  have hy1 : (1 / r : ℚ) < 1 := (div_lt_one hr0).mpr hr
  have hs := finite_geometric_box_budget s (1 / 4) (1 / r)
    (by norm_num) (by norm_num) (by positivity) hy1
  have heq : ∀ z : ℕ × ℕ,
      r / (2 ^ (2 * z.1 + 2) * r ^ (z.2 + 1)) =
        (1 / 4 : ℚ) * ((1 / 4) ^ z.1 * (1 / r) ^ z.2) := by
    intro z
    simp only [pow_add, pow_mul, pow_one, div_pow]
    field_simp
    ring
  simp_rw [heq]
  rw [← mul_sum]
  have h := mul_lt_mul_of_pos_left hs (by norm_num : (0 : ℚ) < 1 / 4)
  convert h using 1 <;> field_simp <;> ring

theorem even_first_budget_le_same_parity (r : ℚ) (hr : 1 < r) :
    r / (3 * (r - 1)) < r * (2 * r + 1) / (3 * (r ^ 2 - 1)) := by
  have hden : 0 < 3 * (r ^ 2 - 1) := by nlinarith
  have hden' : 0 < 3 * (r - 1) := by linarith
  rw [div_lt_div_iff₀ hden' hden]
  have hr0 : 0 < r := by linarith
  nlinarith [sq_pos_of_pos hr0]

/-- The pure prime-power budget is at most `55/72` from base five onwards. -/
theorem pure_tail_bound (r : ℚ) (hr : 5 ≤ r) :
    r * (2 * r + 1) / (3 * (r ^ 2 - 1)) ≤ 55 / 72 ∧
      (r * (2 * r + 1) / (3 * (r ^ 2 - 1)) = 55 / 72 ↔ r = 5) := by
  have hd : 0 < 3 * (r ^ 2 - 1) := by nlinarith
  constructor
  · rw [div_le_div_iff₀ hd (by norm_num : (0 : ℚ) < 72)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (by linarith : (0 : ℚ) ≤ 7 * r + 11)]
  · constructor
    · intro heq
      have he := (div_eq_div_iff hd.ne' (by norm_num : (72 : ℚ) ≠ 0)).mp heq
      nlinarith
    · rintro rfl
      norm_num

/-- Forty-two denominators with a second odd prime factor fit in the tail budget. -/
theorem mixed_tail_bound (Q : Finset ℕ) (r : ℕ) (hr : 131 ≤ r)
    (hcard : Q.card ≤ 42)
    (hlarge : ∀ q ∈ Q, 2 * r * (r + 2) ≤ q - 1) :
    ∑ q ∈ Q, (r : ℚ) / (q - 1 : ℕ) ≤ (Q.card : ℚ) / (2 * (r + 2)) ∧
      (Q.card : ℚ) / (2 * (r + 2)) ≤ 21 / 133 := by
  have hr0 : (0 : ℚ) < r := by exact_mod_cast (show 0 < r by omega)
  have hden : (0 : ℚ) < 2 * (r + 2 : ℚ) := by positivity
  have hpoint : ∀ q ∈ Q, (r : ℚ) / (q - 1 : ℕ) ≤ 1 / (2 * (r + 2)) := by
    intro q hq
    have hq0 : (0 : ℚ) < (q - 1 : ℕ) := by
      have := hlarge q hq
      exact_mod_cast (show 0 < q - 1 by nlinarith)
    rw [div_le_div_iff₀ hq0 hden]
    have h := hlarge q hq
    have hQ : (2 : ℚ) * r * (r + 2) ≤ (q - 1 : ℕ) := by exact_mod_cast h
    nlinarith
  constructor
  · calc
      _ ≤ ∑ _q ∈ Q, (1 / (2 * (r + 2)) : ℚ) := sum_le_sum hpoint
      _ = (Q.card : ℚ) / (2 * (r + 2)) := by simp [div_eq_mul_inv]
  · calc
      (Q.card : ℚ) / (2 * (r + 2 : ℚ)) ≤ 42 / (2 * (r + 2 : ℚ)) := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hden.le
      _ ≤ 21 / 133 := by
        rw [div_le_div_iff₀ hden (by norm_num : (0 : ℚ) < 133)]
        have : (131 : ℚ) ≤ r := by exact_mod_cast hr
        linarith

#print axioms same_parity_geometric_budget
#print axioms pure_tail_bound
#print axioms mixed_tail_bound




open Finset

private theorem two_pow_mod_three (n : ℕ) :
    2 ^ n % 3 = if n % 2 = 0 then 1 else 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have he : n = 2 * (n / 2) := by omega
    rw [if_pos hn, he, pow_mul, Nat.pow_mod]
    norm_num
  · have he : n = 2 * (n / 2) + 1 := by omega
    rw [if_neg (by omega : ¬n % 2 = 0), he, pow_add, pow_mul, Nat.mul_mod]
    norm_num [Nat.pow_mod]

/-- The exponent parity restrictions characterize avoidance of zero modulo three. -/
theorem pure_prime_exponent_parity (r q a b : ℕ)
    (hr3 : r % 3 ≠ 0) (hrep : q - 1 = 2 ^ a * r ^ b) :
    q % 3 ≠ 0 ↔
      (r % 3 = 1 ∧ a % 2 = 0) ∨ (r % 3 = 2 ∧ a % 2 = b % 2) := by
  have hr0 : 0 < r := by omega
  have hprod : 0 < 2 ^ a * r ^ b := by positivity
  have hqe : q = 2 ^ a * r ^ b + 1 := by omega
  have hmod : q % 3 = (2 ^ a % 3 * (r ^ b % 3) + 1) % 3 := by
    rw [hqe, Nat.add_mod, Nat.mul_mod]
    omega
  constructor
  · intro hq3
    have hrlt := Nat.mod_lt r (by decide : 0 < 3)
    have halt := Nat.mod_lt a (by decide : 0 < 2)
    have hblt := Nat.mod_lt b (by decide : 0 < 2)
    by_cases hr1 : r % 3 = 1
    · left
      refine ⟨hr1, ?_⟩
      have hrpow : r ^ b % 3 = 1 := by simp [Nat.pow_mod, hr1]
      by_contra hane
      rw [hrpow, two_pow_mod_three, if_neg hane] at hmod
      norm_num at hmod
      exact hq3 hmod
    · right
      have hr2 : r % 3 = 2 := by omega
      refine ⟨hr2, ?_⟩
      have hrpow : r ^ b % 3 = if b % 2 = 0 then 1 else 2 := by
        calc
          r ^ b % 3 = (r % 3) ^ b % 3 := Nat.pow_mod r b 3
          _ = 2 ^ b % 3 := by rw [hr2]
          _ = _ := two_pow_mod_three b
      rw [hrpow, two_pow_mod_three] at hmod
      split_ifs at hmod <;> norm_num at hmod <;> omega
  · rintro (⟨hr1, ha⟩ | ⟨hr2, hab⟩)
    · have hpow : r ^ b % 3 = 1 := by simp [Nat.pow_mod, hr1]
      rw [hpow, two_pow_mod_three, if_pos ha] at hmod
      norm_num at hmod
      omega
    · have hpow : r ^ b % 3 = if b % 2 = 0 then 1 else 2 := by
        calc
          r ^ b % 3 = (r % 3) ^ b % 3 := Nat.pow_mod r b 3
          _ = 2 ^ b % 3 := by rw [hr2]
          _ = _ := two_pow_mod_three b
      rw [hpow, two_pow_mod_three, hab] at hmod
      split_ifs at hmod <;> norm_num at hmod <;> omega

#print axioms pure_prime_exponent_parity



private theorem mass_eq_image (Q : Finset ℕ) (r : ℕ) (e : ℕ → ℕ × ℕ)
    (A B : ℕ × ℕ → ℕ)
    (hrep : ∀ q ∈ Q, q - 1 = 2 ^ A (e q) * r ^ B (e q))
    (hq : ∀ q ∈ Q, 1 ≤ q) :
    (∑ q ∈ Q, (r : ℚ) / (q - 1 : ℕ)) =
      ∑ z ∈ Q.image e, (r : ℚ) / (2 ^ A z * (r : ℚ) ^ B z) := by
  have hinj : Set.InjOn e Q := by
    intro q hq' p hp' he
    have hqrep := hrep q hq'
    have hprep := hrep p hp'
    rw [he] at hqrep
    have := hq q hq'
    have := hq p hp'
    omega
  rw [sum_image hinj]
  apply sum_congr rfl
  intro q hq'
  rw [hrep q hq']
  norm_cast

/-- Every finite set of primes of the form `2^a r^b+1`, with `b` positive,
obeys the uniform pure-support estimate. -/
theorem pure_prime_tail_budget (Q : Finset ℕ) (r : ℕ)
    (hro : Odd r) (hr3 : r % 3 ≠ 0) (hr5 : 5 ≤ r)
    (hq : ∀ q ∈ Q, q.Prime)
    (hform : ∀ q ∈ Q, ∃ a b : ℕ, 0 < b ∧ q - 1 = 2 ^ a * r ^ b) :
    ∑ q ∈ Q, (r : ℚ) / (q - 1 : ℕ) <
      (r : ℚ) * (2 * r + 1) / (3 * ((r : ℚ) ^ 2 - 1)) ∧
      (r : ℚ) * (2 * r + 1) / (3 * ((r : ℚ) ^ 2 - 1)) ≤ 55 / 72 ∧
      (r % 3 = 1 → ∑ q ∈ Q, (r : ℚ) / (q - 1 : ℕ) <
        (r : ℚ) / (3 * (r - 1 : ℚ))) := by
  classical
  have htotal : ∀ q : ℕ, ∃ a b : ℕ,
      q ∈ Q → 0 < a ∧ 0 < b ∧ q - 1 = 2 ^ a * r ^ b := by
    intro q
    by_cases hmem : q ∈ Q
    · obtain ⟨a, b, hb, heq⟩ := hform q hmem
      have ha : 0 < a := by
        by_contra h
        have ha0 : a = 0 := by omega
        have heq' : q - 1 = r ^ b := by simpa only [ha0, pow_zero, one_mul] using heq
        have hrpowodd : Odd (r ^ b) := hro.pow
        obtain ⟨j, hj⟩ := hrpowodd
        have hqeven : Even q := ⟨j + 1, by have := (hq q hmem).two_le; omega⟩
        have hq2 := (hq q hmem).even_iff.mp hqeven
        have hrb : r ≤ r ^ b := Nat.le_self_pow (by omega : b ≠ 0) r
        omega
      exact ⟨a, b, fun _ => ⟨ha, hb, heq⟩⟩
    · exact ⟨0, 0, fun h => (hmem h).elim⟩
  choose a b hab using htotal
  have hrQ : (1 : ℚ) < r := by exact_mod_cast (show 1 < r by omega)
  have hq1 : ∀ q ∈ Q, 1 ≤ q := fun q h => (hq q h).one_lt.le
  have hpar : ∀ q ∈ Q,
      (r % 3 = 1 ∧ a q % 2 = 0) ∨ (r % 3 = 2 ∧ a q % 2 = b q % 2) := by
    intro q h
    have hqbig : 3 < q := by
      have hrb : r ≤ r ^ b q := Nat.le_self_pow (by have := (hab q h).2.1; omega) r
      have h2a : 2 ≤ 2 ^ a q := Nat.le_self_pow (by have := (hab q h).1; omega) 2
      have hprod : 2 * r ≤ 2 ^ a q * r ^ b q := Nat.mul_le_mul h2a hrb
      have heq := (hab q h).2.2
      omega
    have hq3 : q % 3 ≠ 0 := by
      intro hz
      have he := (Nat.prime_dvd_prime_iff_eq Nat.prime_three (hq q h)).mp
        (Nat.dvd_of_mod_eq_zero hz)
      omega
    exact (pure_prime_exponent_parity r q (a q) (b q) hr3 (hab q h).2.2).mp hq3
  have hbranch : ∑ q ∈ Q, (r : ℚ) / (q - 1 : ℕ) <
      if r % 3 = 1 then (r : ℚ) / (3 * (r - 1 : ℚ))
      else (r : ℚ) * (2 * r + 1) / (3 * ((r : ℚ) ^ 2 - 1)) := by
    by_cases hr1 : r % 3 = 1
    all_goals simp only [hr1, ite_true, ite_false]
    · let e : ℕ → ℕ × ℕ := fun q => (a q / 2 - 1, b q - 1)
      have hrep : ∀ q ∈ Q, q - 1 = 2 ^ (2 * (e q).1 + 2) * r ^ ((e q).2 + 1) := by
        intro q hq'
        have ha := (hab q hq').1
        have hb := (hab q hq').2.1
        have hp := hpar q hq'
        have heven : a q % 2 = 0 := by omega
        have hae : a q = 2 * (e q).1 + 2 := by dsimp [e]; omega
        have hbe : b q = (e q).2 + 1 := by dsimp [e]; omega
        simpa only [← hae, ← hbe] using (hab q hq').2.2
      rw [mass_eq_image Q r e (fun z => 2 * z.1 + 2) (fun z => z.2 + 1) hrep hq1]
      exact even_first_geometric_budget _ (r : ℚ) hrQ
    · let O := Q.filter (fun q => a q % 2 = 1)
      let E := Q.filter (fun q => ¬a q % 2 = 1)
      let eo : ℕ → ℕ × ℕ := fun q => (a q / 2, b q / 2)
      let ee : ℕ → ℕ × ℕ := fun q => (a q / 2 - 1, b q / 2 - 1)
      have ho : ∀ q ∈ O,
          q - 1 = 2 ^ (2 * (eo q).1 + 1) * r ^ (2 * (eo q).2 + 1) := by
        intro q hq'
        obtain ⟨hmem, hoa⟩ := mem_filter.mp hq'
        have hp := hpar q hmem
        have hae : a q = 2 * (eo q).1 + 1 := by dsimp [eo]; omega
        have hbe : b q = 2 * (eo q).2 + 1 := by dsimp [eo]; omega
        simpa only [← hae, ← hbe] using (hab q hmem).2.2
      have he : ∀ q ∈ E,
          q - 1 = 2 ^ (2 * (ee q).1 + 2) * r ^ (2 * (ee q).2 + 2) := by
        intro q hq'
        obtain ⟨hmem, hea⟩ := mem_filter.mp hq'
        have hp := hpar q hmem
        have ha := (hab q hmem).1
        have hb := (hab q hmem).2.1
        have hae : a q = 2 * (ee q).1 + 2 := by dsimp [ee]; omega
        have hbe : b q = 2 * (ee q).2 + 2 := by dsimp [ee]; omega
        simpa only [← hae, ← hbe] using (hab q hmem).2.2
      rw [← sum_filter_add_sum_filter_not Q (fun q => a q % 2 = 1)]
      change (∑ q ∈ O, (r : ℚ) / (q - 1 : ℕ)) +
        (∑ q ∈ E, (r : ℚ) / (q - 1 : ℕ)) < _
      rw [mass_eq_image O r eo (fun z => 2 * z.1 + 1)
        (fun z => 2 * z.2 + 1) ho (fun q h => hq1 q (mem_filter.mp h).1)]
      rw [mass_eq_image E r ee (fun z => 2 * z.1 + 2)
        (fun z => 2 * z.2 + 2) he (fun q h => hq1 q (mem_filter.mp h).1)]
      exact same_parity_geometric_budget _ _ (r : ℚ) hrQ
  have hbound : ∑ q ∈ Q, (r : ℚ) / (q - 1 : ℕ) <
      (r : ℚ) * (2 * r + 1) / (3 * ((r : ℚ) ^ 2 - 1)) := by
    split_ifs at hbranch with hr1
    · exact hbranch.trans (even_first_budget_le_same_parity (r : ℚ) hrQ)
    · exact hbranch
  refine ⟨hbound, (pure_tail_bound (r : ℚ) (by exact_mod_cast hr5)).1, ?_⟩
  intro hr1
  simpa only [if_pos hr1] using hbranch

/-- A finite prime family with forty-two members has mass strictly below one
when each denominator is pure or contains a second odd factor of size at least `r+2`. -/
theorem large_support_tail_of_dichotomy (Q : Finset ℕ) (r : ℕ)
    (hro : Odd r) (hr3 : r % 3 ≠ 0) (hr131 : 131 ≤ r) (hcard : Q.card ≤ 42)
    (hq : ∀ q ∈ Q, q.Prime)
    (hform : ∀ q ∈ Q,
      (∃ a b : ℕ, 0 < b ∧ q - 1 = 2 ^ a * r ^ b) ∨
        2 * r * (r + 2) ≤ q - 1) :
    (∑ q ∈ Q, (r : ℚ) / (q - 1 : ℕ) <
      (r : ℚ) * (2 * r + 1) / (3 * ((r : ℚ) ^ 2 - 1)) +
        42 / (2 * (r + 2 : ℚ))) ∧
      ∑ q ∈ Q, (r : ℚ) / (q - 1 : ℕ) < 1261 / 1368 ∧
      (let M : Finset ℕ := by
         classical
         exact Q.filter (fun q => ¬∃ a b : ℕ,
           0 < b ∧ q - 1 = 2 ^ a * r ^ b)
       (∑ q ∈ Q, (r : ℚ) / (q - 1 : ℕ) <
          (r : ℚ) * (2 * r + 1) / (3 * ((r : ℚ) ^ 2 - 1)) +
            M.card / (2 * (r + 2 : ℚ))) ∧
         (r % 3 = 1 → ∑ q ∈ Q, (r : ℚ) / (q - 1 : ℕ) <
           (r : ℚ) / (3 * (r - 1 : ℚ)) + M.card / (2 * (r + 2 : ℚ)))) := by
  classical
  let P := Q.filter (fun q => ∃ a b : ℕ,
    0 < b ∧ q - 1 = 2 ^ a * r ^ b)
  let M := Q.filter (fun q => ¬∃ a b : ℕ,
    0 < b ∧ q - 1 = 2 ^ a * r ^ b)
  have hp := pure_prime_tail_budget P r hro hr3 (by omega)
    (fun q h => hq q (mem_filter.mp h).1) (fun q h => (mem_filter.mp h).2)
  have hm := mixed_tail_bound M r hr131
    ((card_filter_le _ _).trans hcard) (by
      intro q h
      obtain ⟨hmem, hnot⟩ := mem_filter.mp h
      exact (hform q hmem).resolve_left hnot)
  have hs := sum_filter_add_sum_filter_not Q (fun q => ∃ a b : ℕ,
    0 < b ∧ q - 1 = 2 ^ a * r ^ b)
    (fun q => (r : ℚ) / (q - 1 : ℕ))
  change (∑ q ∈ P, (r : ℚ) / (q - 1 : ℕ)) +
    (∑ q ∈ M, (r : ℚ) / (q - 1 : ℕ)) = _ at hs
  have hM : (M.card : ℚ) / (2 * (r + 2 : ℚ)) ≤ 42 / (2 * (r + 2 : ℚ)) := by
    gcongr
    exact_mod_cast (card_filter_le _ _).trans hcard
  rw [← hs]
  constructor
  · linarith [hp.1, hm.1]
  · refine ⟨?_, ?_⟩
    · linarith [hp.1, hp.2.1, hm.1, hm.2]
    · change (_ < _ + (M.card : ℚ) / _) ∧ (r % 3 = 1 → _ < _)
      constructor
      · linarith [hp.1, hm.1]
      · intro hr1
        linarith [hp.2.2 hr1, hm.1]

#print axioms pure_prime_tail_budget
#print axioms large_support_tail_of_dichotomy

end D5.S3.Arith.MakowskiSchinzel
