/- GID: D5/S3/Weil/Mertens/CoprimeSquarefreeDensity
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/CoprimeSquarefreeDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Count squarefree integers coprime to a fixed squarefree modulus with an explicit square-root error. -/

import D5.S3.Weil.Mertens.CoprimeMobiusCertificateError
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option autoImplicit false

open scoped BigOperators
open Finset
open D5.S3.Weil.Mertens.CoprimeMobiusCertificateError

namespace D5.S3.Weil.Mertens.CoprimeSquarefreeDensity

/-- The number of positive squarefree integers at most X and coprime to Q. -/
noncomputable def S (Q : ℕ) (X : ℝ) : ℝ := by
  classical
  exact ((((Finset.Icc 1 ⌊X⌋₊).filter (fun d => d.Coprime Q ∧ Squarefree d)).card : ℕ) : ℝ)

/-- The reciprocal square series density with one coprimality factor for each prime divisor. -/
noncomputable def rho (Q : ℕ) : ℝ :=
  (∑' n : ℕ, (((n : ℝ) + 1) ^ 2)⁻¹)⁻¹ *
    ∏ p ∈ Q.primeFactors, (p : ℝ) / ((p : ℝ) + 1)

set_option maxHeartbeats 800000 in
/-- The squarefree coprime count differs from its density times X by an explicit square-root bound. -/
theorem squarefree_coprime_count_error (Q : ℕ) (X : ℝ) (hQ : Squarefree Q) (hX : 0 ≤ X) :
    |S Q X - rho Q * X| ≤ ((2 : ℝ) ^ Q.primeFactors.card + 2) * Real.sqrt X := by
  classical
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hindicator (d : ℕ) (hd : 0 < d) :
      (if d.Coprime Q then (1 : ℝ) else 0) =
        ∑ a ∈ Q.divisors, if a ∣ d then (ArithmeticFunction.moebius a : ℝ) else 0 := by
    rw [← sum_filter]
    have hg0 : d.gcd Q ≠ 0 := (Nat.gcd_pos_of_pos_left Q hd).ne'
    have hg : Q.divisors.filter (fun a => a ∣ d) = (d.gcd Q).divisors := by
      ext a
      simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨haR, _⟩, had⟩
        exact ⟨⟨had, haR⟩, hg0⟩
      · rintro ⟨⟨had, haR⟩, _⟩
        exact ⟨⟨haR, hQ0⟩, had⟩
    rw [hg, ← Int.cast_sum, ← ArithmeticFunction.coe_mul_zeta_apply,
      ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
    simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, Nat.Coprime]
  have hC (x : ℝ) : C Q x =
      ∑ a ∈ Q.divisors, (ArithmeticFunction.moebius a : ℝ) * (⌊x / a⌋₊ : ℝ) := by
    rw [C, natCast_card_filter]
    calc
      _ = ∑ d ∈ Icc 1 ⌊x⌋₊, ∑ a ∈ Q.divisors,
          if a ∣ d then (ArithmeticFunction.moebius a : ℝ) else 0 := by
        apply sum_congr rfl
        intro d hd
        exact hindicator d (by have := (mem_Icc.mp hd).1; omega)
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro a ha
        rw [← sum_filter]
        have hi : Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ := by ext k; simp; omega
        rw [hi, sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div,
          Nat.floor_div_natCast]
        ring
  have hCQ : C Q Q = Q.totient := by
    by_cases hQone : Q = 1
    · subst Q
      simp [C]
    have hQne : Q ≠ 1 := hQone
    rw [C, Nat.floor_natCast, Nat.totient_eq_card_coprime]
    apply congrArg (fun s : Finset ℕ => (s.card : ℝ))
    ext d
    simp only [mem_filter, mem_Icc, mem_range]
    constructor
    · rintro ⟨⟨hd1, hdR⟩, hc⟩
      have hne : d ≠ Q := by
        rintro rfl
        exact hQne (by simpa [Nat.Coprime] using hc)
      exact ⟨by omega, hc.symm⟩
    · rintro ⟨hdR, hc⟩
      have hd0 : d ≠ 0 := by
        rintro rfl
        exact hQne (by simpa [Nat.Coprime] using hc)
      exact ⟨⟨by omega, by omega⟩, hc.symm⟩
  have he : e Q = ∑ a ∈ Q.divisors, (ArithmeticFunction.moebius a : ℝ) / a := by
    have hRn : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
    apply (div_eq_iff hRn).mpr
    change (Q.totient : ℝ) = (∑ a ∈ Q.divisors,
      (ArithmeticFunction.moebius a : ℝ) / a) * Q
    rw [← hCQ, hC, sum_mul]
    apply sum_congr rfl
    intro a ha
    rw [Nat.floor_div_eq_div, Nat.cast_div (Nat.dvd_of_mem_divisors ha)
      (Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors ha).ne')]
    ring
  have herror_divisors (x : ℝ) (hx : 0 ≤ x) : |C Q x - e Q * x| ≤ Q.divisors.card := by
    rw [hC, he, sum_mul, ← sum_sub_distrib]
    calc
      _ ≤ ∑ a ∈ Q.divisors,
          |(ArithmeticFunction.moebius a : ℝ) * (⌊x / a⌋₊ : ℝ) -
            (ArithmeticFunction.moebius a : ℝ) / a * x| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ Q.divisors, (1 : ℝ) := by
        apply sum_le_sum
        intro a ha
        have hmu : |(ArithmeticFunction.moebius a : ℝ)| ≤ 1 := by
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := a))
        have hf : |(⌊x / a⌋₊ : ℝ) - x / a| ≤ 1 := by
          rw [abs_sub_comm]
          exact Nat.abs_sub_floor_le (div_nonneg hx (Nat.cast_nonneg a))
        calc
          _ = |(ArithmeticFunction.moebius a : ℝ)| * |(⌊x / a⌋₊ : ℝ) - x / a| := by
            rw [← abs_mul]
            congr 1
            ring
          _ ≤ 1 * 1 := mul_le_mul hmu hf (abs_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      _ = _ := by simp
  have hcard : (Q.divisors.card : ℝ) = (2 : ℝ) ^ Q.primeFactors.card := by
    have hn : Q.divisors.card = 2 ^ Q.primeFactors.card := by
      rw [Nat.card_divisors hQ0]
      calc
        _ = ∏ p ∈ Q.primeFactors, (2 : ℕ) := by
          apply prod_congr rfl
          intro p hp
          have hu := (Nat.squarefree_iff_factorization_le_one hQ0).mp hQ p
          have hl : 0 < Q.factorization p := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hQ0 (Nat.dvd_of_mem_primeFactors hp)
          omega
        _ = _ := by simp
    exact_mod_cast hn
  have he_product : e Q = ∏ p ∈ Q.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have ht : (Q.totient : ℝ) = (Q : ℝ) *
        ∏ p ∈ Q.primeFactors, (1 - (p : ℝ)⁻¹) := by
      have hr := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors Q)
      simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub,
        Rat.cast_one, Rat.cast_inv] using hr
    rw [e, ht]
    have hQr : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
    field_simp
  have herror (Y : ℝ) (hY : 0 ≤ Y) :
      |C Q Y - Y * ∏ p ∈ Q.primeFactors, (1 - (p : ℝ)⁻¹)| ≤
        (2 : ℝ) ^ Q.primeFactors.card := by
    simpa [hcard, he_product, mul_comm] using herror_divisors Y hY
  have hsf_indicator (n : ℕ) (hn : 0 < n) :
      (if Squarefree n then (1 : ℝ) else 0) =
        ∑ a ∈ n.divisors.filter (fun a => a ^ 2 ∣ n),
          (ArithmeticFunction.moebius a : ℝ) := by
    obtain ⟨b, t, hb, ht, heq, hbs⟩ := Nat.sq_mul_squarefree_of_pos hn
    have hdiv (a : ℕ) : a ^ 2 ∣ n ↔ a ∣ t := by
      constructor
      · intro had
        have ha : a ≠ 0 := by
          intro hz
          simp [hz, hn.ne'] at had
        apply (Nat.factorization_le_iff_dvd ha ht.ne').mp
        intro p
        have hle := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 ha) hn.ne').mpr had p
        rw [← heq, Nat.factorization_mul (pow_ne_zero 2 ht.ne') hb.ne',
          Nat.factorization_pow, Nat.factorization_pow] at hle
        simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hle
        have hbound := (Nat.squarefree_iff_factorization_le_one hb.ne').mp hbs p
        omega
      · intro had
        rw [← heq]
        exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd had 2) b
    have hset : n.divisors.filter (fun a => a ^ 2 ∣ n) = t.divisors := by
      ext a
      constructor
      · intro ha
        exact Nat.mem_divisors.mpr ⟨(hdiv a).mp (mem_filter.mp ha).2, ht.ne'⟩
      · intro ha
        have had := Nat.dvd_of_mem_divisors ha
        have htn : t ∣ n := by
          rw [← heq]
          exact dvd_mul_of_dvd_left (dvd_pow_self t (by omega)) b
        exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_trans had htn, hn.ne'⟩,
          (hdiv a).mpr had⟩
    have hiff : Squarefree n ↔ t = 1 := by
      constructor
      · intro hs
        exact Nat.isUnit_iff.mp (hs t (by rw [← heq, ← pow_two]; exact dvd_mul_right _ _))
      · rintro rfl
        rw [← heq]
        simpa using hbs
    rw [hset, ← Int.cast_sum, ← ArithmeticFunction.coe_mul_zeta_apply,
      ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
    simp [hiff]
  let M : ℕ := ⌊Real.sqrt X⌋₊
  let A : Finset ℕ := Icc 1 M
  have hsf_window (n : ℕ) (hn : n ∈ Icc 1 ⌊X⌋₊) :
      (if Squarefree n then (1 : ℝ) else 0) =
        ∑ a ∈ A, if a ^ 2 ∣ n then (ArithmeticFunction.moebius a : ℝ) else 0 := by
    have hn0 : 0 < n := (mem_Icc.mp hn).1
    have hnX : (n : ℝ) ≤ X := (Nat.le_floor_iff hX).mp (mem_Icc.mp hn).2
    rw [hsf_indicator n hn0, ← sum_filter]
    congr 1
    ext a
    simp only [mem_filter]
    constructor
    · rintro ⟨ha, had⟩
      have ha0 := Nat.pos_of_mem_divisors ha
      have hsq : (a : ℝ) ^ 2 ≤ X := by
        exact (by exact_mod_cast Nat.le_of_dvd hn0 had : (a : ℝ) ^ 2 ≤ n).trans hnX
      exact ⟨mem_Icc.mpr ⟨ha0, (Nat.le_floor_iff (Real.sqrt_nonneg X)).mpr
        (Real.le_sqrt_of_sq_le hsq)⟩, had⟩
    · rintro ⟨ha, had⟩
      exact ⟨Nat.mem_divisors.mpr ⟨dvd_trans (dvd_pow_self a (by omega)) had, hn0.ne'⟩, had⟩
  have hcount_mul (k : ℕ) (hk : 0 < k) (hc : k.Coprime Q) :
      (((Icc 1 ⌊X⌋₊).filter (fun n => n.Coprime Q ∧ k ∣ n)).card : ℝ) =
        C Q (X / k) := by
    rw [C]
    apply congrArg (fun n : ℕ => (n : ℝ))
    symm
    apply card_bij (fun m _ => k * m)
    · intro m hm
      obtain ⟨hmI, hmc⟩ := mem_filter.mp hm
      obtain ⟨hm1, hmX⟩ := mem_Icc.mp hmI
      have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
      have hmR := (Nat.le_floor_iff (div_nonneg hX hkR.le)).mp hmX
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hk hm1, ?_⟩,
        (Nat.coprime_mul_iff_left).mpr ⟨hc, hmc⟩, dvd_mul_right k m⟩
      apply (Nat.le_floor_iff hX).mpr
      push_cast
      simpa [mul_comm] using (le_div_iff₀ hkR).mp hmR
    · intro m hm n hn heq
      exact Nat.eq_of_mul_eq_mul_left hk heq
    · intro n hn
      obtain ⟨hnI, hnc, hkn⟩ := mem_filter.mp hn
      obtain ⟨hn1, hnX⟩ := mem_Icc.mp hnI
      refine ⟨n / k, mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
      · exact Nat.div_pos (Nat.le_of_dvd hn1 hkn) hk
      · apply (Nat.le_floor_iff (div_nonneg hX (Nat.cast_nonneg k))).mpr
        rw [Nat.cast_div hkn (Nat.cast_ne_zero.mpr hk.ne')]
        exact div_le_div_of_nonneg_right ((Nat.le_floor_iff hX).mp hnX) (Nat.cast_nonneg k)
      · exact hnc.of_dvd_left (Nat.div_dvd_of_dvd hkn)
      · exact Nat.mul_div_cancel' hkn
  have hexpansion : S Q X =
      ∑ a ∈ A.filter (fun a => a.Coprime Q),
        (ArithmeticFunction.moebius a : ℝ) * C Q (X / (a : ℝ) ^ 2) := by
    rw [S, natCast_card_filter]
    calc
      _ = ∑ n ∈ Icc 1 ⌊X⌋₊, ∑ a ∈ A,
          if n.Coprime Q ∧ a ^ 2 ∣ n then (ArithmeticFunction.moebius a : ℝ) else 0 := by
        apply sum_congr rfl
        intro n hn
        by_cases hc : n.Coprime Q
        · calc
            _ = (if Squarefree n then (1 : ℝ) else 0) := by rw [ite_and, if_pos hc]
            _ = _ := (hsf_window n hn).trans (sum_congr rfl (fun a _ => by rw [ite_and, if_pos hc]))
        · simp [hc]
      _ = ∑ a ∈ A, (ArithmeticFunction.moebius a : ℝ) *
          (((Icc 1 ⌊X⌋₊).filter (fun n => n.Coprime Q ∧ a ^ 2 ∣ n)).card : ℝ) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro a ha
        rw [← sum_filter]
        simp [mul_comm]
      _ = _ := by
        rw [sum_filter]
        apply sum_congr rfl
        intro a ha
        have ha0 : 0 < a := (mem_Icc.mp ha).1
        by_cases hc : a.Coprime Q
        · rw [if_pos hc, hcount_mul (a ^ 2) (pow_pos ha0 2) (hc.pow_left 2)]
          norm_cast
        · rw [if_neg hc]
          have hempty : (Icc 1 ⌊X⌋₊).filter (fun n => n.Coprime Q ∧ a ^ 2 ∣ n) = ∅ := by
            apply filter_eq_empty_iff.mpr
            intro n hn h
            exact hc (h.1.of_dvd_left (dvd_trans (dvd_pow_self a (by omega)) h.2))
          simp [hempty]
  sorry

end D5.S3.Weil.Mertens.CoprimeSquarefreeDensity
