/- GID: D5/S3/Arith/Robin/GoldenResidualFive
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/GoldenResidualFive
   mirror-E: none(waiver:universal-inequality)
   anchors: []
   utility: none
   digest: The 5040 congruence branch satisfies strict Robin with at most thirty-nine distinct primes. -/

import Mathlib.Order.Interval.Finset.Nat
import D5.S3.Arith.Robin.FibonacciPrimeSupport
import D5.S3.Arith.GoldenResource.GoldenCell5040Shape
import D5.S3.Arith.GoldenResource.GoldenCell5040SmallPrimeExclusion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Robin.GoldenResidualFive

open D5.S3.Arith.Robin.FewDistinctPrimes
open D5.S3.Arith.Robin.ElevenSmooth
open D5.S3.Arith.Robin.FibonacciPrimeSupport
open D5.S3.Arith.ExponentExchange.IntegerSwap
open D5.S3.Arith.RobinExponentSwap
open D5.S3.Arith.GoldenResource.RobinRationalBasis
open D5.S3.Arith.GoldenResource.GoldenCell5040Shape
open D5.S3.Arith.GoldenResource.GoldenCell5040SmallPrimeExclusion

noncomputable section

private def roughPrimes : List ℕ := [13, 17, 19, 23, 29]

private def eulerFactor (p : ℕ) : ℝ := (p : ℝ) / ((p : ℝ) - 1)

private theorem rough_nat_step (k : ℕ) (hk : k < 5) :
    (roughPrimes.take (k + 1)).prod =
      (roughPrimes.take k).prod * roughPrimes.getD k 0 := by
  interval_cases k <;> norm_num [roughPrimes]

private theorem rough_real_step (k : ℕ) (hk : k < 5) :
    ((roughPrimes.take (k + 1)).map eulerFactor).prod =
      ((roughPrimes.take k).map eulerFactor).prod * eulerFactor (roughPrimes.getD k 0) := by
  interval_cases k <;> norm_num [roughPrimes, eulerFactor]

private theorem small_rough_prime {k p : ℕ} (hk : k < 5) (hp : p.Prime)
    (h13 : 13 ≤ p) (hlt : p < roughPrimes.getD k 0) : p ∈ roughPrimes.take k := by
  have h29 : p < 29 := by
    have hbound : ∀ j < 5, roughPrimes.getD j 0 ≤ 29 := by decide
    exact hlt.trans_le (hbound k hk)
  interval_cases k <;> interval_cases p <;>
    first | (simp [roughPrimes] at hlt ⊢; done) | norm_num at hp

/-- The same ordered-prime argument bounds the radical below and the Euler product above. -/
private theorem rough_products : ∀ k ≤ 5, ∀ S : Finset ℕ,
    (∀ p ∈ S, p.Prime) → (∀ p ∈ S, 13 ≤ p) → S.card = k →
    (roughPrimes.take k).prod ≤ ∏ p ∈ S, p ∧
      (∏ p ∈ S, eulerFactor p) ≤ ((roughPrimes.take k).map eulerFactor).prod := by
  intro k
  induction k with
  | zero =>
    intro _ S _ _ hcard
    simp [Finset.card_eq_zero.mp hcard, roughPrimes]
  | succ k ih =>
    intro hk S hprime h13 hcard
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    have hqS : S.max' hne ∈ S := S.max'_mem hne
    have hcard' : (S.erase (S.max' hne)).card = k := by
      rw [Finset.card_erase_of_mem hqS, hcard]
      rfl
    have hIH := ih (by omega) (S.erase (S.max' hne))
      (fun p hp => hprime p (Finset.mem_of_mem_erase hp))
      (fun p hp => h13 p (Finset.mem_of_mem_erase hp)) hcard'
    have hq : roughPrimes.getD k 0 ≤ S.max' hne := by
      by_contra hlt
      rw [not_le] at hlt
      have hsub : S ⊆ (roughPrimes.take k).toFinset := by
        intro p hp
        have hpq : p ≤ S.max' hne := S.le_max' p hp
        exact List.mem_toFinset.mpr
          (small_rough_prime (by omega) (hprime p hp) (h13 p hp) (by omega))
      have h1 := Finset.card_le_card hsub
      have h2 : (roughPrimes.take k).toFinset.card ≤ k :=
        (List.toFinset_card_le _).trans (by simp)
      omega
    have hk13 : 13 ≤ roughPrimes.getD k 0 := by
      have h : ∀ j < 5, 13 ≤ roughPrimes.getD j 0 := by decide
      exact h k (by omega)
    have hqR : (roughPrimes.getD k 0 : ℝ) ≤ S.max' hne := by exact_mod_cast hq
    have hkR : (13 : ℝ) ≤ roughPrimes.getD k 0 := by exact_mod_cast hk13
    have hq13R : (13 : ℝ) ≤ S.max' hne := by exact_mod_cast h13 _ hqS
    have hEuler : eulerFactor (S.max' hne) ≤ eulerFactor (roughPrimes.getD k 0) := by
      unfold eulerFactor
      apply (div_le_div_iff₀ (by linarith) (by linarith)).2
      nlinarith
    constructor
    · rw [rough_nat_step k (by omega), ← Finset.mul_prod_erase S _ hqS,
        mul_comm (S.max' hne)]
      exact Nat.mul_le_mul hIH.1 hq
    · have hqnonneg : 0 ≤ eulerFactor (S.max' hne) := by
        unfold eulerFactor
        exact div_nonneg (by positivity) (by linarith)
      have hcapnonneg : 0 ≤ ((roughPrimes.take k).map eulerFactor).prod := by
        have hk' : k < 5 := by omega
        interval_cases k <;> norm_num [roughPrimes, eulerFactor]
      rw [rough_real_step k (by omega), ← Finset.mul_prod_erase S eulerFactor hqS,
        mul_comm (eulerFactor (S.max' hne))]
      exact mul_le_mul hIH.2 hEuler hqnonneg hcapnonneg

private theorem core_coprime (a b r : ℕ) (hc : r.Coprime 210) :
    (2 ^ a * 3 ^ b * 5 * 7).Coprime r := by
  have h2 : r.Coprime 2 := hc.coprime_dvd_right (by decide)
  have h3 : r.Coprime 3 := hc.coprime_dvd_right (by decide)
  have h5 : r.Coprime 5 := hc.coprime_dvd_right (by decide)
  have h7 : r.Coprime 7 := hc.coprime_dvd_right (by decide)
  exact ((((h2.pow_right a).mul_right (h3.pow_right b)).mul_right h5).mul_right h7).symm

private theorem core_primeFactors (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (2 ^ a * 3 ^ b * 5 * 7).primeFactors = {2, 3, 5, 7} := by
  rw [Nat.primeFactors_mul (by positivity) (by decide),
    Nat.primeFactors_mul (by positivity) (by decide),
    Nat.primeFactors_mul (by positivity) (by positivity),
    Nat.primeFactors_prime_pow (by omega) Nat.prime_two,
    Nat.primeFactors_prime_pow (by omega) Nat.prime_three,
    (by decide : Nat.Prime 5).primeFactors, (by decide : Nat.Prime 7).primeFactors]
  decide

private theorem core_support_card (a b r : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hr : r ≠ 0) (hc : r.Coprime 210) :
    (2 ^ a * 3 ^ b * 5 * 7 * r).primeFactors.card = 4 + r.primeFactors.card := by
  rw [Nat.primeFactors_mul (by positivity) hr,
    Finset.card_union_of_disjoint (core_coprime a b r hc).disjoint_primeFactors,
    core_primeFactors a b ha hb]
  norm_num

private theorem core_ge_5040 (a b : ℕ) (ha4 : 4 ≤ a) (hb2 : 2 ≤ b) :
    5040 ≤ 2 ^ a * 3 ^ b * 5 * 7 := by
  have h2 := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) ha4
  have h3 := Nat.pow_le_pow_right (by norm_num : 0 < (3 : ℕ)) hb2
  have h := Nat.mul_le_mul (Nat.mul_le_mul h2 h3) (le_refl 5)
  have h' := Nat.mul_le_mul h (le_refl 7)
  norm_num at h'
  exact h'

private theorem core_ratio_bound (a b : ℕ) (ha4 : 4 ≤ a) (ha6 : a ≤ 6)
    (hb2 : 2 ≤ b) (hb3 : b ≤ 3) :
    (ArithmeticFunction.sigma 1 (2 ^ a * 3 ^ b * 5 * 7) : ℝ) /
      (2 ^ a * 3 ^ b * 5 * 7 : ℕ) ≤ 254 / 63 := by
  have cop (p q i j : ℕ) (h : p.Coprime q) : (p ^ i).Coprime (q ^ j) :=
    (h.pow_left i).pow_right j
  have h7 : (2 ^ a * 3 ^ b * 5).Coprime 7 :=
    (((by decide : Nat.Coprime 2 7).pow_left a).mul_left
      ((by decide : Nat.Coprime 3 7).pow_left b)).mul_left (by decide)
  have h5 : (2 ^ a * 3 ^ b).Coprime 5 :=
    ((by decide : Nat.Coprime 2 5).pow_left a).mul_left
      ((by decide : Nat.Coprime 3 5).pow_left b)
  have h5ratio := normalized_sigma_prime_pow (by decide : Nat.Prime 5) 1
  have h7ratio := normalized_sigma_prime_pow (by decide : Nat.Prime 7) 1
  norm_num [reciprocalGeomSum, Finset.sum_range_succ] at h5ratio h7ratio
  rw [normalized_sigma_mul h7, normalized_sigma_mul h5,
    normalized_sigma_mul (cop 2 3 a b (by decide)),
    normalized_sigma_prime_pow Nat.prime_two, normalized_sigma_prime_pow Nat.prime_three,
    h5ratio, h7ratio]
  interval_cases a <;> interval_cases b <;>
    norm_num [reciprocalGeomSum, Finset.sum_range_succ]

private theorem residual_primes_ge_thirteen {r p : ℕ} (hc : r.Coprime 210)
    (h11 : ¬11 ∣ r) (hp : p ∈ r.primeFactors) : 13 ≤ p := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  by_contra hlt
  have hp13 : p < 13 := by omega
  have hcop : p.Coprime 210 := hc.coprime_dvd_left hd
  interval_cases p <;> (try norm_num at hprime) <;> (try norm_num at hcop)
  exact h11 hd

private theorem loglog_two_pow_thirty_three : (3 : ℝ) < Real.log (Real.log (2 ^ 33)) :=
  loglog_of (2 ^ 33) 22 3 1 (11 / 8) 33 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

/-- A bounded old-prime core and at most five residual primes, excluding 11, satisfy Robin. -/
theorem robin_of_core_residual_le_five (a b r : ℕ)
    (ha4 : 4 ≤ a) (ha6 : a ≤ 6) (hb2 : 2 ≤ b) (hb3 : b ≤ 3)
    (hc : r.Coprime 210) (h11 : ¬11 ∣ r) (hcard : r.primeFactors.card ≤ 5)
    (hn : 5040 < 2 ^ a * 3 ^ b * 5 * 7 * r) :
    (ArithmeticFunction.sigma 1 (2 ^ a * 3 ^ b * 5 * 7 * r) : ℝ) /
        (2 ^ a * 3 ^ b * 5 * 7 * r : ℕ) <
      Real.exp Real.eulerMascheroniConstant *
        Real.log (Real.log (2 ^ a * 3 ^ b * 5 * 7 * r : ℕ)) := by
  have hr : r ≠ 0 := by intro hz; rw [hz, mul_zero] at hn; omega
  by_cases hsmall : r.primeFactors.card ≤ 4
  · apply robin_of_card_primeFactors_le_eight hn
    rw [core_support_card a b r (by omega) (by omega) hr hc]
    omega
  have hfive : r.primeFactors.card = 5 := by omega
  have hprimes := rough_products 5 le_rfl r.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp)
    (fun p hp => residual_primes_ge_thirteen hc h11 hp) hfive
  have hrad : 2800733 ≤ r := by
    have hl := hprimes.1
    norm_num [roughPrimes] at hl
    exact hl.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hr) (Nat.prod_primeFactors_dvd r))
  have hcore := core_ge_5040 a b ha4 hb2
  have hsize : 2 ^ 33 ≤ 2 ^ a * 3 ^ b * 5 * 7 * r := by
    have h := Nat.mul_le_mul hcore hrad
    norm_num at h ⊢
    omega
  have hratio : (ArithmeticFunction.sigma 1 (2 ^ a * 3 ^ b * 5 * 7 * r) : ℝ) /
      (2 ^ a * 3 ^ b * 5 * 7 * r : ℕ) ≤ 355693091 / 67060224 := by
    have hres := (ratio_le_prod r hr).trans hprimes.2
    norm_num [roughPrimes, eulerFactor] at hres
    rw [normalized_sigma_mul (core_coprime a b r hc)]
    calc
      _ ≤ (254 / 63 : ℝ) * (2800733 / 2128896) :=
        mul_le_mul (core_ratio_bound a b ha4 ha6 hb2 hb3) hres
          (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by norm_num)
      _ = 355693091 / 67060224 := by norm_num
  have hsizeR : (2 : ℝ) ^ 33 ≤ (2 ^ a * 3 ^ b * 5 * 7 * r : ℕ) := by
    exact_mod_cast hsize
  have hloglog : (3 : ℝ) < Real.log (Real.log (2 ^ a * 3 ^ b * 5 * 7 * r : ℕ)) := by
    apply loglog_two_pow_thirty_three.trans_le
    exact Real.log_le_log (Real.log_pos (by norm_num))
      (Real.log_le_log (by norm_num) hsizeR)
  have hcapacity : (267 / 50 : ℝ) < Real.exp Real.eulerMascheroniConstant *
      Real.log (Real.log (2 ^ a * 3 ^ b * 5 * 7 * r : ℕ)) := by
    calc
      _ = (89 / 50 : ℝ) * 3 := by norm_num
      _ < Real.exp Real.eulerMascheroniConstant *
          Real.log (Real.log (2 ^ a * 3 ^ b * 5 * 7 * r : ℕ)) := by
        exact mul_lt_mul exp_gamma_lower hloglog.le (by norm_num) (Real.exp_pos _).le
  exact hratio.trans_lt ((by norm_num :
    (355693091 / 67060224 : ℝ) < 267 / 50).trans hcapacity)

/-- In the 5040 power-congruence branch, a ninth distinct prime cannot violate Robin. -/
theorem robin_of_modEq_2241_card_le_nine {n : ℕ} (hn : 5040 < n)
    (h5040 : 5040 ∣ n) (hmod : Nat.ModEq n (3 ^ n) 2241)
    (hcard : n.primeFactors.card ≤ 9) :
    (ArithmeticFunction.sigma 1 n : ℝ) / n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) := by
  obtain ⟨a, b, r, hshape, ha4, ha6, hb2, hb3, hc83⟩ := modEq_2241_shape h5040 hmod
  have hr : r ≠ 0 := by intro hz; rw [hshape, hz, mul_zero] at hn; omega
  have hc : r.Coprime 210 := hc83.coprime_dvd_right (by decide)
  have h11n : ¬11 ∣ n :=
    modEq_2241_small_prime_not_dvd h5040 hmod (by decide) (by decide) (by decide)
  have h11r : ¬11 ∣ r := by
    intro hd
    apply h11n
    rw [hshape]
    exact dvd_mul_of_dvd_right hd _
  have hcardr : r.primeFactors.card ≤ 5 := by
    rw [hshape, core_support_card a b r (by omega) (by omega) hr hc] at hcard
    omega
  rw [hshape] at hn ⊢
  exact robin_of_core_residual_le_five a b r ha4 ha6 hb2 hb3 hc h11r hcardr hn

/-- Distinct integers above a cutoff have a telescoping Euler-product bound. -/
private theorem integer_euler_product_bound (m : ℕ) (hm : 0 < m) :
    ∀ k (S : Finset ℕ), (∀ p ∈ S, m + 1 ≤ p) → S.card = k →
      (∏ p ∈ S, eulerFactor p) ≤ ((m + k : ℕ) : ℝ) / m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  intro k
  induction k with
  | zero =>
    intro S _ hcard
    simp [Finset.card_eq_zero.mp hcard, hmR.ne']
  | succ k ih =>
    intro S hcut hcard
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    have hqS : S.max' hne ∈ S := S.max'_mem hne
    have hcard' : (S.erase (S.max' hne)).card = k := by
      rw [Finset.card_erase_of_mem hqS, hcard]
      rfl
    have hIH := ih (S.erase (S.max' hne))
      (fun p hp => hcut p (Finset.mem_of_mem_erase hp)) hcard'
    have hq : m + k + 1 ≤ S.max' hne := by
      have hsub : S ⊆ Finset.Icc (m + 1) (S.max' hne) := by
        intro p hp
        exact Finset.mem_Icc.mpr ⟨hcut p hp, S.le_max' p hp⟩
      have hcount := Finset.card_le_card hsub
      rw [hcard, Nat.card_Icc] at hcount
      omega
    have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hqR : (m : ℝ) + k + 1 ≤ S.max' hne := by exact_mod_cast hq
    have hmkR : (0 : ℝ) < (m : ℝ) + k := by linarith
    have hqone : (1 : ℝ) < S.max' hne := by linarith
    have hEuler : eulerFactor (S.max' hne) ≤
        ((m : ℝ) + k + 1) / ((m : ℝ) + k) := by
      unfold eulerFactor
      apply (div_le_div_iff₀ (by linarith) hmkR).2
      nlinarith
    have hqnonneg : 0 ≤ eulerFactor (S.max' hne) := by
      unfold eulerFactor
      exact div_nonneg (by positivity) (by linarith)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] at hIH ⊢
    calc
      _ = (∏ p ∈ S.erase (S.max' hne), eulerFactor p) * eulerFactor (S.max' hne) := by
        rw [← Finset.mul_prod_erase S eulerFactor hqS]
        ring
      _ ≤ (((m : ℝ) + k) / m) * (((m : ℝ) + k + 1) / ((m : ℝ) + k)) :=
        mul_le_mul hIH hEuler hqnonneg (div_nonneg (by linarith) hmR.le)
      _ = ((m : ℝ) + k + 1) / m := by
        field_simp [hmR.ne', hmkR.ne'] <;> ring
      _ = ((m : ℝ) + ((k : ℝ) + 1)) / m := by ring

/-- Every residual prime in this branch lies above the excluded small-prime interval. -/
private theorem residual_primes_ge_forty_seven {n r : ℕ}
    (h5040 : 5040 ∣ n) (hmod : Nat.ModEq n (3 ^ n) 2241)
    (hc : r.Coprime 210) (hrdvd : r ∣ n) : ∀ p ∈ r.primeFactors, 47 ≤ p := by
  have h11n : ¬11 ∣ n :=
    modEq_2241_small_prime_not_dvd h5040 hmod (by decide) (by decide) (by decide)
  have h11r : ¬11 ∣ r := fun hd => h11n (hd.trans hrdvd)
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hp13 := residual_primes_ge_thirteen hc h11r hp
  by_contra hlt
  have hnotdvd : ¬p ∣ n :=
    modEq_2241_small_prime_not_dvd h5040 hmod hprime (by omega) (by omega)
  exact hnotdvd ((Nat.dvd_of_mem_primeFactors hp).trans hrdvd)

/-- A cutoff and a support count bound the residual radical and hence the residual itself. -/
private theorem radical_lower_bound (m r k : ℕ) (hm : 0 < m) (hr : r ≠ 0)
    (hcut : ∀ p ∈ r.primeFactors, m ≤ p) (hk : k ≤ r.primeFactors.card) :
    m ^ k ≤ r := by
  calc
    _ ≤ m ^ r.primeFactors.card := Nat.pow_le_pow_right hm hk
    _ = ∏ p ∈ r.primeFactors, m := by simp
    _ ≤ ∏ p ∈ r.primeFactors, p := Finset.prod_le_prod' (fun p hp => hcut p hp)
    _ ≤ r := Nat.le_of_dvd (Nat.pos_of_ne_zero hr) (Nat.prod_primeFactors_dvd r)

private theorem loglog_two_pow_eighty_four : (4 : ℝ) < Real.log (Real.log (2 ^ 84)) :=
  loglog_of (2 ^ 84) 58 4 1 (29 / 16) 84 5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)

/-- Small-prime exclusion and two size certificates close total support through thirty-nine. -/
theorem robin_of_modEq_2241_card_le_thirty_nine {n : ℕ} (hn : 5040 < n)
    (h5040 : 5040 ∣ n) (hmod : Nat.ModEq n (3 ^ n) 2241)
    (hcard : n.primeFactors.card ≤ 39) :
    (ArithmeticFunction.sigma 1 n : ℝ) / n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) := by
  by_cases hsmall : n.primeFactors.card ≤ 9
  · exact robin_of_modEq_2241_card_le_nine hn h5040 hmod hsmall
  obtain ⟨a, b, r, hshape, ha4, ha6, hb2, hb3, hc83⟩ := modEq_2241_shape h5040 hmod
  have hr : r ≠ 0 := by intro hz; rw [hshape, hz, mul_zero] at hn; omega
  have hc : r.Coprime 210 := hc83.coprime_dvd_right (by decide)
  have hcardeq : n.primeFactors.card = 4 + r.primeFactors.card := by
    rw [hshape, core_support_card a b r (by omega) (by omega) hr hc]
  have hrescap : r.primeFactors.card ≤ 35 := by omega
  have hresfive : 5 ≤ r.primeFactors.card := by omega
  have hrdvd : r ∣ n := by
    rw [hshape]
    exact dvd_mul_of_dvd_right (dvd_refl r) _
  have h47 := residual_primes_ge_forty_seven h5040 hmod hc hrdvd
  have hrad : ∀ j ≤ r.primeFactors.card, 47 ^ j ≤ r :=
    fun j hj => radical_lower_bound 47 r j (by decide) hr h47 hj
  have hEuler := integer_euler_product_bound 46 (by decide)
    r.primeFactors.card r.primeFactors (fun p hp => h47 p hp) rfl
  have hres := (ratio_le_prod r hr).trans hEuler
  have hratio : (ArithmeticFunction.sigma 1 n : ℝ) / n ≤
      (254 / 63 : ℝ) * ((46 + (r.primeFactors.card : ℝ)) / 46) := by
    rw [hshape, normalized_sigma_mul (core_coprime a b r hc)]
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      mul_le_mul (core_ratio_bound a b ha4 ha6 hb2 hb3) hres
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by norm_num)
  by_cases hshort : r.primeFactors.card ≤ 14
  · have hcountR : (r.primeFactors.card : ℝ) ≤ 14 := by exact_mod_cast hshort
    have hratioCap : (ArithmeticFunction.sigma 1 n : ℝ) / n ≤ 2540 / 483 := by
      apply hratio.trans
      nlinarith
    have hsize : 2 ^ 33 ≤ n := by
      rw [hshape]
      have h := Nat.mul_le_mul (core_ge_5040 a b ha4 hb2) (hrad 5 hresfive)
      norm_num at h ⊢
      omega
    have hsizeR : (2 : ℝ) ^ 33 ≤ n := by exact_mod_cast hsize
    have hloglog : (3 : ℝ) < Real.log (Real.log (n : ℝ)) := by
      apply loglog_two_pow_thirty_three.trans_le
      exact Real.log_le_log (Real.log_pos (by norm_num))
        (Real.log_le_log (by norm_num) hsizeR)
    have hcapacity : (267 / 50 : ℝ) < Real.exp Real.eulerMascheroniConstant *
        Real.log (Real.log (n : ℝ)) := by
      calc
        _ = (89 / 50 : ℝ) * 3 := by norm_num
        _ < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) :=
          mul_lt_mul exp_gamma_lower hloglog.le (by norm_num) (Real.exp_pos _).le
    exact hratioCap.trans_lt ((by norm_num : (2540 / 483 : ℝ) < 267 / 50).trans hcapacity)
  · have hcountR : (r.primeFactors.card : ℝ) ≤ 35 := by exact_mod_cast hrescap
    have hratioCap : (ArithmeticFunction.sigma 1 n : ℝ) / n ≤ 1143 / 161 := by
      apply hratio.trans
      nlinarith
    have hsize : 2 ^ 84 ≤ n := by
      rw [hshape]
      have h := Nat.mul_le_mul (core_ge_5040 a b ha4 hb2) (hrad 13 (by omega))
      norm_num at h ⊢
      omega
    have hsizeR : (2 : ℝ) ^ 84 ≤ n := by exact_mod_cast hsize
    have hloglog : (4 : ℝ) < Real.log (Real.log (n : ℝ)) := by
      apply loglog_two_pow_eighty_four.trans_le
      exact Real.log_le_log (Real.log_pos (by norm_num))
        (Real.log_le_log (by norm_num) hsizeR)
    have hcapacity : (178 / 25 : ℝ) < Real.exp Real.eulerMascheroniConstant *
        Real.log (Real.log (n : ℝ)) := by
      calc
        _ = (89 / 50 : ℝ) * 4 := by norm_num
        _ < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) :=
          mul_lt_mul exp_gamma_lower hloglog.le (by norm_num) (Real.exp_pos _).le
    exact hratioCap.trans_lt ((by norm_num : (1143 / 161 : ℝ) < 178 / 25).trans hcapacity)

/-- Every strict-Robin counterexample in this congruence branch lies above an explicit threshold. -/
theorem counterexample_size_lower_bound {n : ℕ} (hn : 5040 < n)
    (h5040 : 5040 ∣ n) (hmod : Nat.ModEq n (3 ^ n) 2241)
    (hbad : Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) ≤
      (ArithmeticFunction.sigma 1 n : ℝ) / n) : 5040 * 47 ^ 36 ≤ n := by
  have hsupport : 40 ≤ n.primeFactors.card := by
    by_contra hnot
    have hcard : n.primeFactors.card ≤ 39 := by omega
    exact (not_lt_of_ge hbad) (robin_of_modEq_2241_card_le_thirty_nine hn h5040 hmod hcard)
  obtain ⟨a, b, r, hshape, ha4, ha6, hb2, hb3, hc83⟩ := modEq_2241_shape h5040 hmod
  have hr : r ≠ 0 := by intro hz; rw [hshape, hz, mul_zero] at hn; omega
  have hc : r.Coprime 210 := hc83.coprime_dvd_right (by decide)
  have hres : 36 ≤ r.primeFactors.card := by
    rw [hshape, core_support_card a b r (by omega) (by omega) hr hc] at hsupport
    omega
  have hrdvd : r ∣ n := by
    rw [hshape]
    exact dvd_mul_of_dvd_right (dvd_refl r) _
  have h47 := residual_primes_ge_forty_seven h5040 hmod hc hrdvd
  have hrad := radical_lower_bound 47 r 36 (by decide) hr h47 hres
  rw [hshape]
  exact Nat.mul_le_mul (core_ge_5040 a b ha4 hb2) hrad

#print axioms counterexample_size_lower_bound
#print axioms robin_of_modEq_2241_card_le_thirty_nine
#print axioms robin_of_core_residual_le_five
#print axioms robin_of_modEq_2241_card_le_nine

end

end D5.S3.Arith.Robin.GoldenResidualFive
