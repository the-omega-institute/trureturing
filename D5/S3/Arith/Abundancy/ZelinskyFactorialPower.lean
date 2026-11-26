/- GID: D5/S3/Arith/Abundancy/ZelinskyFactorialPower
   generality: I
   mirror-B: D5/B/S3/Arith/Abundancy/ZelinskyFactorialPower
   mirror-E: none(waiver:symbolic-limit-no-numeric-artifact)
   anchors: []
   utility: none
   digest: The Euler prime-factor product of the factorial power plus one tends to one. -/

import D5.S3.Arith.Divisors.DivisorSubpower
import D5.S3.Weil.GronwallUpperEnvelope
import D5.S3.Arith.Robin.FibonacciRankEulerTail
import D5.S3.Weil.Mertens.Third
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! The prime divisors are separated by size and multiplicative order. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Filter Real
open scoped Topology BigOperators

namespace D5.S3.Arith.Abundancy.ZelinskyFactorialPower

/-- Zelinsky's product over all distinct prime divisors. -/
def H (m : ℕ) : ℝ := ∏ p ∈ m.primeFactors, (p : ℝ) / (p - 1)

private def value (n : ℕ) : ℕ := n.factorial ^ n + 1

private def mass (n : ℕ) : ℝ := ∑ p ∈ (value n).primeFactors, 1 / (p : ℝ)

private def degree (n p : ℕ) : ℕ := orderOf (n.factorial : ZMod p)

private lemma prime_gt {n p : ℕ} (hn : 1 ≤ n)
    (hp : p ∈ (value n).primeFactors) : n < p := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hdvd := Nat.dvd_of_mem_primeFactors hp
  by_contra h
  have hf : p ∣ n.factorial := Nat.dvd_factorial hprime.pos (by omega)
  have hpow : p ∣ n.factorial ^ n := dvd_pow hf (by omega)
  have hone : p ∣ 1 := by
    have := (Nat.dvd_add_iff_right hpow).mpr (show p ∣ n.factorial ^ n + 1 from hdvd)
    exact this
  exact hprime.not_dvd_one hone

private lemma degree_data {n p : ℕ} (hn : 1 ≤ n)
    (hp : p ∈ (value n).primeFactors) :
    0 < degree n p ∧ degree n p ∣ 2 * n ∧ degree n p ∣ p - 1 ∧
      p ∣ n.factorial ^ degree n p - 1 := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  let : Fact p.Prime := ⟨hprime⟩
  have hnp := prime_gt hn hp
  have hfac : (n.factorial : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => (Nat.not_le.mpr hnp) (hprime.dvd_factorial.mp h)
  have hneg : (n.factorial : ZMod p) ^ n = -1 := by
    apply eq_neg_of_add_eq_zero_left
    have := (ZMod.natCast_eq_zero_iff (value n) p).mpr
      (Nat.dvd_of_mem_primeFactors hp)
    simpa [value] using this
  have htwo : (n.factorial : ZMod p) ^ (2 * n) = 1 := by
    rw [mul_comm 2 n, pow_mul, hneg]
    norm_num
  have hd : degree n p ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hfac
  have hpos : 0 < degree n p := Nat.pos_of_dvd_of_pos hd (by omega)
  refine ⟨hpos, orderOf_dvd_of_pow_eq_one htwo, hd, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  have hpow : 1 ≤ n.factorial ^ degree n p := one_le_pow₀ (Nat.factorial_pos n)
  rw [Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_one, degree, pow_orderOf_eq_one]
  simp

private lemma rough_sum (s : Finset ℕ) {m : ℕ} (hm : 0 < m)
    (hs : s ⊆ m.primeFactors) {y : ℝ} (hy : 2 ≤ y)
    (hrough : ∀ p ∈ s, y < (p : ℝ)) :
    (∑ p ∈ s, 1 / (p : ℝ)) ≤ log m / (y * log y) := by
  have hy0 : 0 < y := by linarith
  have hsub : s ⊆ D5.S3.Weil.GronwallUpperEnvelope.largePrimes m y :=
    fun p hp => mem_filter.mpr ⟨hs hp, hrough p hp⟩
  have hcard : (s.card : ℝ) ≤
      (D5.S3.Weil.GronwallUpperEnvelope.largePrimes m y).card := by
    exact_mod_cast card_le_card hsub
  calc
    _ ≤ ∑ _p ∈ s, 1 / y := sum_le_sum fun p hp =>
      one_div_le_one_div_of_le hy0 (hrough p hp).le
    _ = (s.card : ℝ) / y := by simp [div_eq_mul_inv]
    _ ≤ (log m / log y) / y := div_le_div_of_nonneg_right
      (hcard.trans (D5.S3.Weil.GronwallUpperEnvelope.large_prime_count_le hm hy)) hy0.le
    _ = _ := by ring

private lemma progression_sum (s : Finset ℕ) {d z : ℕ} (hd : 0 < d)
    (hs : ∀ p ∈ s, 2 ≤ p ∧ p ≤ z ∧ d ∣ p - 1) :
    (∑ p ∈ s, 1 / (p : ℝ)) ≤ (1 + log z) / d := by
  classical
  let k : ℕ → ℕ := fun p => (p - 1) / d
  have hk (p : ℕ) (hp : p ∈ s) : k p * d + 1 = p := by
    have ht := Nat.div_mul_cancel (hs p hp).2.2
    have hp2 := (hs p hp).1
    dsimp [k]
    omega
  have hmem (p : ℕ) (hp : p ∈ s) : k p ∈ Icc 1 z := by
    have ht := hk p hp
    have hp2 := (hs p hp).1
    have hpz := (hs p hp).2.1
    refine mem_Icc.mpr ⟨?_, ?_⟩
    · nlinarith
    · exact (Nat.div_le_self (p - 1) d).trans (by omega)
  have hinj : Set.InjOn k s := by
    intro p hp q hq heq
    calc
      p = k p * d + 1 := (hk p hp).symm
      _ = k q * d + 1 := by rw [heq]
      _ = q := hk q hq
  have hbound : (∑ p ∈ s, 1 / (p : ℝ)) ≤
      ∑ j ∈ Icc 1 z, (1 / (j : ℝ)) / d := by
    apply sum_le_sum_of_injOn k hinj (by
      intro j hj
      rcases mem_image.mp hj with ⟨p, hp, rfl⟩
      exact hmem p hp)
    · intro p hp
      have hkpos : 0 < k p := (mem_Icc.mp (hmem p hp)).1
      have hkdpos : 0 < (k p : ℝ) * d := mul_pos
        (by exact_mod_cast hkpos) (by exact_mod_cast hd)
      have hle : (k p : ℝ) * d ≤ p := by
        have ht := hk p hp
        exact_mod_cast (show k p * d ≤ p by omega)
      simpa only [div_mul_eq_div_div] using
        (one_div_le_one_div_of_le hkdpos hle)
    · intro j hj _
      positivity
  calc
    _ ≤ (∑ j ∈ Icc 1 z, 1 / (j : ℝ)) / d := by
      simpa only [sum_div] using hbound
    _ = (harmonic z : ℝ) / d := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast, one_div]
    _ ≤ _ := div_le_div_of_nonneg_right (harmonic_le_one_add_log z)
      (Nat.cast_nonneg d)

private lemma small_orders {n : ℕ} (hn : 2 ≤ n) (s : Finset ℕ)
    (hs : s ⊆ (value n).primeFactors) {t y : ℝ} (ht : 0 ≤ t) (hy : 2 ≤ y)
    (hb : ∀ p ∈ s, y < (p : ℝ) ∧ (degree n p : ℝ) ≤ t) :
    (∑ p ∈ s, 1 / (p : ℝ)) ≤ t ^ 2 * log n.factorial / (y * log y) := by
  classical
  have ha : 2 ≤ n.factorial := by
    simpa using Nat.factorial_le hn
  have hloga : 0 ≤ log (n.factorial : ℝ) := log_nonneg (by exact_mod_cast (by omega))
  have hden : 0 ≤ y * log y := mul_nonneg (by linarith) (log_nonneg (by linarith : 1 ≤ y))
  have hmap : ∀ p ∈ s, degree n p ∈ Icc 1 ⌊t⌋₊ := by
    intro p hp
    exact mem_Icc.mpr ⟨(degree_data (by omega) (hs hp)).1,
      (Nat.le_floor_iff ht).mpr (hb p hp).2⟩
  rw [← sum_fiberwise_of_maps_to hmap]
  calc
    _ ≤ ∑ d ∈ Icc 1 ⌊t⌋₊, t * log n.factorial / (y * log y) := by
      apply sum_le_sum
      intro d hd
      have hd0 : 0 < d := (mem_Icc.mp hd).1
      have hpow : 1 < n.factorial ^ d := one_lt_pow₀ (by omega) (by omega)
      have hm : 0 < n.factorial ^ d - 1 := by omega
      have hsub : (s.filter (fun p : ℕ => degree n p = d)) ⊆
          (n.factorial ^ d - 1).primeFactors := by
        intro p hp
        rcases mem_filter.mp hp with ⟨hp, heq⟩
        have hp0 := hs hp
        apply (Nat.prime_of_mem_primeFactors hp0).mem_primeFactors _ (by omega)
        simpa [heq] using (degree_data (by omega) hp0).2.2.2
      have hbnd := rough_sum _ hm hsub hy
        (fun p hp => (hb p (mem_filter.mp hp).1).1)
      have hlog : log (n.factorial ^ d - 1 : ℕ) ≤ (d : ℝ) * log n.factorial := by
        calc
          _ ≤ log ((n.factorial : ℝ) ^ d) := log_le_log (by exact_mod_cast hm)
            (by exact_mod_cast Nat.sub_le (n.factorial ^ d) 1)
          _ = _ := log_pow _ _
      apply hbnd.trans
      apply div_le_div_of_nonneg_right _ hden
      exact hlog.trans (mul_le_mul_of_nonneg_right
        ((Nat.cast_le.mpr (mem_Icc.mp hd).2).trans (Nat.floor_le ht)) hloga)
    _ = (⌊t⌋₊ : ℝ) * (t * log n.factorial / (y * log y)) := by
      simp [Nat.card_Icc, nsmul_eq_mul]
    _ ≤ t ^ 2 * log n.factorial / (y * log y) := by
      calc
        _ ≤ t * (t * log n.factorial / (y * log y)) :=
          mul_le_mul_of_nonneg_right (Nat.floor_le ht) (by positivity)
        _ = _ := by ring

private lemma large_orders {n : ℕ} (hn : 2 ≤ n) (s : Finset ℕ)
    (hs : s ⊆ (value n).primeFactors) {t : ℝ} (ht : 0 < t)
    (hb : ∀ p ∈ s, p ≤ n ^ 3 ∧ t < (degree n p : ℝ)) :
    (∑ p ∈ s, 1 / (p : ℝ)) ≤
      ((2 * n).divisors.card : ℝ) * (1 + 3 * log n) / t := by
  classical
  have hmap : ∀ p ∈ s, degree n p ∈ (2 * n).divisors := by
    intro p hp
    exact Nat.mem_divisors.mpr ⟨(degree_data (by omega) (hs hp)).2.1, by omega⟩
  have hlog : 0 ≤ 1 + log (n ^ 3 : ℕ) := by
    have : 1 ≤ n ^ 3 := one_le_pow₀ (by omega)
    have := log_nonneg (show (1 : ℝ) ≤ (n ^ 3 : ℕ) by exact_mod_cast this)
    linarith
  rw [← sum_fiberwise_of_maps_to hmap]
  calc
    _ ≤ ∑ _d ∈ (2 * n).divisors, (1 + log (n ^ 3 : ℕ)) / t := by
      apply sum_le_sum
      intro d hd
      by_cases hdt : t < (d : ℝ)
      · have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
        apply (progression_sum _ hd0 (fun p hp => ?_)).trans
        · exact div_le_div_of_nonneg_left hlog ht hdt.le
        rcases mem_filter.mp hp with ⟨hp, heq⟩
        exact ⟨(Nat.prime_of_mem_primeFactors (hs hp)).two_le, (hb p hp).1,
          heq ▸ (degree_data (by omega) (hs hp)).2.2.1⟩
      · have hempty : s.filter (fun p : ℕ => degree n p = d) = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro p hp
          rcases mem_filter.mp hp with ⟨hp, heq⟩
          exact hdt (heq ▸ (hb p hp).2)
        rw [hempty, sum_empty]
        positivity
    _ = _ := by
      simp only [sum_const, nsmul_eq_mul, Nat.cast_pow, log_pow]
      ring

private def primes (x : ℝ) : Finset ℕ := (Ioc 0 ⌊x⌋₊).filter Nat.Prime

private def window (n : ℕ) (y : ℝ) : ℝ :=
  (∑ p ∈ primes y, 1 / (p : ℝ)) - ∑ p ∈ primes n, 1 / (p : ℝ)

private lemma window_bound {n : ℕ} {y : ℝ} (hny : (n : ℝ) ≤ y)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ n < p ∧ (p : ℝ) ≤ y) :
    (∑ p ∈ s, 1 / (p : ℝ)) ≤ window n y := by
  have hsub : primes n ⊆ primes y := by
    intro p hp
    rcases mem_filter.mp hp with ⟨hp, hpprime⟩
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hp).1,
      (mem_Ioc.mp hp).2.trans (Nat.floor_mono hny)⟩, hpprime⟩
  rw [window, ← sum_sdiff hsub, add_sub_cancel_right]
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rcases hs p hp with ⟨hpp, hnp, hpy⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpp.pos, Nat.le_floor hpy⟩, hpp⟩
    · simp only [primes, mem_filter, mem_Ioc, Nat.floor_natCast]
      omega
  · intro p hp _
    positivity

private lemma factorial_logs {n : ℕ} (hn : 2 ≤ n) :
    log (n.factorial : ℝ) ≤ (n : ℝ) * log n ∧
      log (value n : ℝ) ≤ (n : ℝ) ^ 2 * log n + log 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hfac0 : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hfac : log (n.factorial : ℝ) ≤ (n : ℝ) * log n := by
    calc
      _ ≤ log ((n : ℝ) ^ n) := log_le_log hfac0 (by exact_mod_cast n.factorial_le_pow)
      _ = _ := log_pow _ _
  refine ⟨hfac, ?_⟩
  have hpow : (1 : ℝ) ≤ (n.factorial : ℝ) ^ n :=
    one_le_pow₀ (by exact_mod_cast Nat.factorial_pos n)
  have hv : (value n : ℝ) ≤ 2 * (n.factorial : ℝ) ^ n := by
    simp only [value, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
    linarith
  calc
    _ ≤ log (2 * (n.factorial : ℝ) ^ n) := log_le_log (by dsimp [value]; positivity) hv
    _ = (n : ℝ) * log n.factorial + log 2 := by
      rw [log_mul (by norm_num) (pow_pos hfac0 _).ne', log_pow]
      ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hfac hn0.le]

private lemma four_ranges {n : ℕ} (hn : 2 ≤ n) {t y : ℝ}
    (ht : 0 < t) (hy : 2 ≤ y) (hny : (n : ℝ) ≤ y) :
    mass n ≤ window n y + t ^ 2 * ((n : ℝ) * log n) / (y * log y) +
      ((2 * n).divisors.card : ℝ) * (1 + 3 * log n) / t +
      ((n : ℝ) ^ 2 * log n + log 2) /
        ((n : ℝ) ^ 3 * log ((n : ℝ) ^ 3)) := by
  classical
  let f : ℕ → ℝ := fun p => 1 / (p : ℝ)
  let s : Finset ℕ := (value n).primeFactors
  let s₁ : Finset ℕ := s.filter (fun p : ℕ => (p : ℝ) ≤ y)
  let s₂ : Finset ℕ := s.filter (fun p : ℕ => y < (p : ℝ) ∧ (degree n p : ℝ) ≤ t)
  let s₃ : Finset ℕ := s.filter (fun p : ℕ => p ≤ n ^ 3 ∧ t < (degree n p : ℝ))
  let s₄ : Finset ℕ := s.filter (fun p : ℕ => n ^ 3 < p)
  have hcover : mass n ≤ (∑ p ∈ s₁, f p) + (∑ p ∈ s₂, f p) +
      (∑ p ∈ s₃, f p) + ∑ p ∈ s₄, f p := by
    simp only [s₁, s₂, s₃, s₄, sum_filter, ← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    dsimp [f]
    have hnonneg : 0 ≤ 1 / (p : ℝ) := by positivity
    split_ifs <;> first | positivity | omega | linarith | grind
  have h₁ : (∑ p ∈ s₁, f p) ≤ window n y :=
    window_bound hny s₁ (fun p hp => ⟨Nat.prime_of_mem_primeFactors
      (mem_filter.mp hp).1, prime_gt (by omega) (mem_filter.mp hp).1,
      (mem_filter.mp hp).2⟩)
  have h₂ := small_orders hn s₂ (filter_subset _ _) ht.le hy
    (fun p hp => (mem_filter.mp hp).2)
  have h₃ := large_orders hn s₃ (filter_subset _ _) ht
    (fun p hp => (mem_filter.mp hp).2)
  have hz : 2 ≤ (n : ℝ) ^ 3 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : ℝ) - 2)]
  have h₄ := rough_sum s₄ (by dsimp [value]; omega) (filter_subset _ _) hz
    (fun p hp => by exact_mod_cast (mem_filter.mp hp).2)
  have hlogs := factorial_logs hn
  have h₂' : (∑ p ∈ s₂, f p) ≤ t ^ 2 * ((n : ℝ) * log n) / (y * log y) := by
    apply h₂.trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlogs.1 (sq_nonneg t))
      (mul_nonneg (by linarith) (log_nonneg (by linarith)))
  have h₄' : (∑ p ∈ s₄, f p) ≤ ((n : ℝ) ^ 2 * log n + log 2) /
      ((n : ℝ) ^ 3 * log ((n : ℝ) ^ 3)) := by
    apply h₄.trans
    exact div_le_div_of_nonneg_right hlogs.2
      (mul_nonneg (by positivity) (log_nonneg (by linarith)))
  linarith

private def error (e k : ℝ) (n : ℕ) : ℝ :=
  2 / (n : ℝ) ^ e + k * ((1 + 3 * log n) / (n : ℝ) ^ (e / 2)) + 2 / (n : ℝ)

private lemma error_tendsto (e k : ℝ) (he : 0 < e) :
    Tendsto (error e k) atTop (𝓝 0) := by
  have he2 : 0 < e / 2 := by positivity
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => 2 / (n : ℝ) ^ e) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop he).comp hn)
  have hi2 : Tendsto (fun n : ℕ => 1 / (n : ℝ) ^ (e / 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop he2).comp hn)
  have hl := (isLittleO_log_rpow_atTop he2).tendsto_div_nhds_zero.comp hn
  have hm : Tendsto (fun n : ℕ => (1 + 3 * log n) / (n : ℝ) ^ (e / 2))
      atTop (𝓝 0) := by
    have hh := hi2.add (hl.const_mul 3)
    simp only [mul_zero, add_zero] at hh
    apply hh.congr
    intro n
    simp only [Function.comp_apply]
    ring
  have ht : Tendsto (fun n : ℕ => 2 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  change Tendsto (fun n : ℕ => 2 / (n : ℝ) ^ e +
    k * ((1 + 3 * log n) / (n : ℝ) ^ (e / 2)) + 2 / (n : ℝ)) atTop (𝓝 0)
  simpa only [mul_zero, add_zero] using (hi.add (hm.const_mul k)).add ht

private lemma window_tendsto (e : ℝ) (he : 0 < e) :
    Tendsto (fun n : ℕ => window n ((n : ℝ) ^ (1 + 3 * e)))
      atTop (𝓝 (log (1 + 3 * e))) := by
  have hc : 0 < 1 + 3 * e := by positivity
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hE : Tendsto Mertens.E₂p atTop (𝓝 0) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₂p.bound'
  have hY := (tendsto_rpow_atTop hc).comp hn
  have h := ((hE.comp hY).sub (hE.comp hn)).add_const (log (1 + 3 * e))
  simp only [sub_self, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn2
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn0 : (0 : ℝ) < n := by linarith
  dsimp [Mertens.E₂p, window, primes]
  rw [log_rpow hn0, log_mul hc.ne' (log_pos hn1).ne']
  ring

private lemma quantitative {n : ℕ} (hn : 2 ≤ n) {e c : ℝ}
    (he : 0 < e) (hc : 0 < c)
    (hdiv : ((2 * n).divisors.card : ℝ) ≤ c * (2 * (n : ℝ)) ^ (e / 2)) :
    mass n ≤ window n ((n : ℝ) ^ (1 + 3 * e)) + error e (c * 2 ^ (e / 2)) n := by
  let x : ℝ := n
  let t : ℝ := x ^ e
  let u : ℝ := x ^ (e / 2)
  have hx : 2 ≤ x := by dsimp [x]; exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have ht : 0 < t := rpow_pos_of_pos hx0 _
  have hu : 0 < u := rpow_pos_of_pos hx0 _
  have ht1 : 1 ≤ t := one_le_rpow hx1 he.le
  have hl : 0 < log x := log_pos (by linarith)
  have hce : 1 ≤ 1 + 3 * e := by linarith
  have hY : x ^ (1 + 3 * e) = x * t ^ 3 := by
    have hpow := rpow_mul_natCast hx0.le e 3
    norm_num only [Nat.cast_ofNat] at hpow
    rw [show 1 + 3 * e = e * 3 + 1 by ring, rpow_add_one hx0.ne', hpow]
    ring
  have hTu : t = u ^ 2 := by
    dsimp [t, u]
    rw [← rpow_mul_natCast hx0.le]
    congr 1
    ring
  have hny : x ≤ x ^ (1 + 3 * e) := by
    rw [hY]
    nlinarith [one_le_pow₀ ht1 (n := 3)]
  have hlow : t ^ 2 * (x * log x) /
      (x ^ (1 + 3 * e) * log (x ^ (1 + 3 * e))) ≤ 2 / t := by
    rw [log_rpow hx0, hY]
    apply (div_le_iff₀ (mul_pos (by positivity) (mul_pos (by positivity) hl))).mpr
    have hid : 2 / t * (x * t ^ 3 * ((1 + 3 * e) * log x)) =
        2 * (1 + 3 * e) * (t ^ 2 * (x * log x)) := by
      field_simp
    rw [hid]
    nlinarith [mul_nonneg (sq_nonneg t) (mul_nonneg hx0.le hl.le)]
  have hhigh : ((2 * n).divisors.card : ℝ) * (1 + 3 * log x) / t ≤
      (c * 2 ^ (e / 2)) * ((1 + 3 * log x) / u) := by
    have hcast : (2 * (n : ℝ)) ^ (e / 2) = 2 ^ (e / 2) * u :=
      mul_rpow (by norm_num) hx0.le
    have h := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hdiv (by positivity : 0 ≤ 1 + 3 * log x)) ht.le
    apply h.trans_eq
    rw [hcast, hTu]
    field_simp
  have htail : (x ^ 2 * log x + log 2) / (x ^ 3 * log (x ^ 3)) ≤ 2 / x := by
    rw [log_pow]
    norm_num only [Nat.cast_ofNat]
    apply (div_le_iff₀ (mul_pos (pow_pos hx0 _) (mul_pos (by norm_num) hl))).mpr
    have hlog2 : log 2 ≤ log x := log_le_log (by norm_num) hx
    have hxx : 1 ≤ x ^ 2 := one_le_pow₀ hx1
    have hid : 2 / x * (x ^ 3 * ((3 : ℝ) * log x)) = 6 * x ^ 2 * log x := by
      field_simp
      ring
    rw [hid]
    nlinarith
  have h := four_ranges hn ht (hx.trans hny) hny
  dsimp [error]
  change mass n ≤ window n (x ^ (1 + 3 * e)) + (2 / t +
    (c * 2 ^ (e / 2)) * ((1 + 3 * log x) / u) + 2 / x)
  linarith

private lemma mass_tendsto : Tendsto mass atTop (𝓝 0) := by
  apply (tendsto_order.2 ⟨?_, ?_⟩)
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (sum_nonneg (by intros; positivity)))
  · intro b hb
    let e : ℝ := min (1 / 4) (b / 24)
    have he : 0 < e := lt_min (by norm_num) (by positivity)
    have heB : e ≤ b / 24 := min_le_right _ _
    obtain ⟨c, hc, hdiv⟩ :=
      D5.S3.Arith.Divisors.DivisorSubpower.card_divisors_subpower (e / 2) (by positivity)
    have hlim := (window_tendsto e he).add (error_tendsto e (c * 2 ^ (e / 2)) he)
    simp only [add_zero] at hlim
    have hlog : log (1 + 3 * e) < b := by
      have := log_le_sub_one_of_pos (show 0 < 1 + 3 * e by positivity)
      linarith
    filter_upwards [eventually_ge_atTop 2, (tendsto_order.mp hlim).2 b hlog]
      with n hn hnb
    apply lt_of_le_of_lt (quantitative hn he hc ?_) hnb
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hdiv (2 * n) (by omega)

/-- Conjecture 36: the complete Euler prime-factor product tends to one. -/
theorem result : Tendsto (fun n : ℕ => H (n.factorial ^ n + 1)) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n => log (H (value n))) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => ?_) (fun n => ?_)
      (by simpa using mass_tendsto.const_mul 2)
    · rw [H, log_prod]
      · exact sum_nonneg (fun p hp =>
          (D5.S3.Arith.Robin.FibonacciRankEulerTail.euler_log_bounds p
            (Nat.prime_of_mem_primeFactors hp).two_le).1)
      · intro p hp
        have hp1 : (1 : ℝ) < p := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
        exact (div_pos (by linarith) (by linarith)).ne'
    · rw [H, log_prod, mass, mul_sum]
      · apply sum_le_sum
        intro p hp
        have hp2 : (2 : ℝ) ≤ p := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        apply (D5.S3.Arith.Robin.FibonacciRankEulerTail.euler_log_bounds p
          (Nat.prime_of_mem_primeFactors hp).two_le).2.trans
        have : 0 < (p : ℝ) - 1 := by linarith
        rw [mul_one_div]
        apply (div_le_div_iff₀ this (by linarith : (0 : ℝ) < p)).mpr
        linarith
      · intro p hp
        have hp1 : (1 : ℝ) < p := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
        exact (div_pos (by linarith) (by linarith)).ne'
  have hpos (n : ℕ) : 0 < H (value n) := by
    apply prod_pos
    intro p hp
    have hp1 : (1 : ℝ) < p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    exact div_pos (by linarith) (by linarith)
  have hh : Tendsto (fun n => exp (log (H (value n)))) atTop (𝓝 1) := by
    simpa only [exp_zero] using hlog.rexp
  exact hh.congr (fun n => exp_log (hpos n))

end D5.S3.Arith.Abundancy.ZelinskyFactorialPower
