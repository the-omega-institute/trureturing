/- GID: D5/S3/ArithSums/BrowneA164660RootCount
   generality: I
   mirror-B: D5/B/S3/ArithSums/BrowneA164660RootCount
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: The r-th power root count of n in any n consecutive integers is n/D_r(n). -/

import D5.S3.ArithSums.BrowneA164660ChebyshevFloorProduct
import Mathlib.Data.Int.CardIntervalMod

/-! # Arbitrary-power root counts and translated floor products

For positive integers `n, r` let `D_r(n) = ∏_{p ∣ n} p^⌈e_p/r⌉` and `C_r(n) = n / D_r(n)`.
Then `n ∣ k^r` iff `D_r(n) ∣ k` for every integer `k`, so every window of `n` consecutive
integers contains exactly `C_r(n)` solutions, and the floor product over the window is
`(-1)^{C_r(n)}`.
-/

set_option autoImplicit false

namespace D5.S3.ArithSums.BrowneA164660RootCount

open D5.S3.ArithSums.BrowneA164660ChebyshevFloorProduct
open Finset

/-- The ceiling exponents `⌈e_p / r⌉` of `n`, as a finitely supported function. -/
noncomputable def ceilFactorization (r n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.mapRange (fun e => (e + r - 1) / r) (by rw [zero_add, Nat.div_eq_zero_iff]; omega)

/-- `D_r(n) = ∏_{p ∣ n} p^⌈e_p/r⌉`. -/
noncomputable def D (r n : ℕ) : ℕ := (ceilFactorization r n).prod (· ^ ·)

/-- `C_r(n) = n / D_r(n)`. -/
noncomputable def C (r n : ℕ) : ℕ := n / D r n

private lemma D_factorization (r n : ℕ) : (D r n).factorization = ceilFactorization r n := by
  apply Nat.factorization_prod_pow_eq_self
  intro p hp
  have : p ∈ n.factorization.support :=
    Finsupp.support_mapRange hp
  exact Nat.prime_of_mem_primeFactors (by simpa using this)

private lemma D_ne_zero (r n : ℕ) : D r n ≠ 0 := by
  unfold D Finsupp.prod
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  have : p ∈ n.factorization.support := Finsupp.support_mapRange hp
  exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors (by simpa using this)).ne_zero

/-- For `m ≠ 0`, `n ∣ m^r` iff `D_r(n) ∣ m`. -/
private lemma dvd_pow_iff_nat {n r m : ℕ} (hn : n ≠ 0) (hr : 0 < r) (hm : m ≠ 0) :
    n ∣ m ^ r ↔ D r n ∣ m := by
  rw [← Nat.factorization_le_iff_dvd hn (pow_ne_zero _ hm),
    ← Nat.factorization_le_iff_dvd (D_ne_zero r n) hm, D_factorization, Nat.factorization_pow]
  simp only [Finsupp.le_def, ceilFactorization, Finsupp.mapRange_apply, Finsupp.smul_apply,
    smul_eq_mul]
  refine forall_congr' fun p => ?_
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos (n.factorization p) with h0 | hpos
    · rw [h0]; simp [Nat.div_eq_of_lt (show r - 1 < r by omega)]
    · rw [Nat.div_le_iff_le_mul_add_pred hr]
      omega
  · intro h
    have := (Nat.div_le_iff_le_mul_add_pred hr).mp h
    omega

/-- For every integer `k`, `n ∣ k^r` iff `D_r(n) ∣ k`. -/
theorem dvd_pow_iff {n r : ℕ} (hn : 0 < n) (hr : 0 < r) (k : ℤ) :
    (n : ℤ) ∣ k ^ r ↔ (D r n : ℤ) ∣ k := by
  rw [Int.natCast_dvd, Int.natCast_dvd, Int.natAbs_pow]
  rcases Nat.eq_zero_or_pos k.natAbs with h0 | hpos
  · rw [h0, zero_pow hr.ne']
    simp
  · exact dvd_pow_iff_nat hn.ne' hr hpos.ne'

private lemma D_dvd {n r : ℕ} (hn : 0 < n) (hr : 0 < r) : D r n ∣ n :=
  (dvd_pow_iff_nat hn.ne' hr hn.ne').mp (dvd_pow_self n hr.ne')

private lemma D_pos (r n : ℕ) : 0 < D r n := Nat.pos_of_ne_zero (D_ne_zero r n)

/-- The integer floor detector: `⌊t/n⌋ - ⌊(t-1)/n⌋` is `1` if `n ∣ t` and `0` otherwise. -/
private lemma floor_indicator_int {n : ℕ} (hn : 0 < n) (t : ℤ) :
    ⌊(t : ℚ) / (n : ℚ)⌋ - ⌊((t : ℚ) - 1) / (n : ℚ)⌋ = if (n : ℤ) ∣ t then 1 else 0 := by
  have hd : (0 : ℤ) < n := Int.natCast_pos.mpr hn
  have hB : ⌊((t : ℚ) - 1) / (n : ℚ)⌋ = (t - 1) / (n : ℤ) := by
    rw [← Rat.floor_intCast_div_natCast]
    push_cast
    rfl
  rw [Rat.floor_intCast_div_natCast, hB]
  have hrem := Int.emod_nonneg t (ne_of_gt hd)
  have hlt := Int.emod_lt_of_pos t hd
  have heq := Int.mul_ediv_add_emod t (n : ℤ)
  by_cases h : (n : ℤ) ∣ t
  · simp only [h, ↓reduceIte]
    have hz : t % (n : ℤ) = 0 := Int.emod_eq_zero_of_dvd h
    have hf : (t - 1) / (n : ℤ) = t / (n : ℤ) - 1 := by
      apply (Int.ediv_eq_iff_of_pos hd).mpr
      constructor <;> nlinarith
    rw [hf]
    ring
  · simp only [h, ↓reduceIte]
    have hz : t % (n : ℤ) ≠ 0 := fun hz => h (Int.dvd_of_emod_eq_zero hz)
    have hf : (t - 1) / (n : ℤ) = t / (n : ℤ) := by
      apply (Int.ediv_eq_iff_of_pos hd).mpr
      constructor <;> nlinarith [show 1 ≤ t % (n : ℤ) by omega]
    rw [hf, sub_self]

/-- The number of multiples of `D_r(n)` in `(s, s+n]` is `C_r(n)`. -/
private lemma window_card {n r : ℕ} (hn : 0 < n) (hr : 0 < r) (s : ℤ) :
    #{k ∈ Ioc s (s + n) | (D r n : ℤ) ∣ k} = C r n := by
  have hD : (0 : ℤ) < D r n := by exact_mod_cast D_pos r n
  have hmul : (n : ℤ) = D r n * C r n := by
    unfold C
    exact_mod_cast (Nat.mul_div_cancel' (D_dvd hn hr)).symm
  have h := Int.Ioc_filter_dvd_card s (s + n) hD
  have hfl : ⌊((s + n : ℤ) : ℚ) / ((D r n : ℤ) : ℚ)⌋ =
      ⌊((s : ℤ) : ℚ) / ((D r n : ℤ) : ℚ)⌋ + C r n := by
    rw [← Int.floor_add_intCast]
    congr 1
    have hD' : ((D r n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast D_ne_zero r n
    rw [hmul]
    push_cast
    rw [add_div, mul_div_cancel_left₀ _ hD']
  rw [hfl, add_sub_cancel_left, max_eq_left (by positivity)] at h
  exact_mod_cast h

/-- For positive `n, r` and every integer `s`, over the `n` consecutive integers
`s+1, …, s+n` the floor differences `⌊k^r/n⌋ - ⌊(k^r-1)/n⌋` sum to `C_r(n)`, and the product
of `1 - 2` times them is `(-1)^{C_r(n)}`. -/
theorem window (n r : ℕ) (hn : 0 < n) (hr : 0 < r) (s : ℤ) :
    ∑ k ∈ Icc (s + 1) (s + n),
        (⌊(k : ℚ) ^ r / (n : ℚ)⌋ - ⌊((k : ℚ) ^ r - 1) / (n : ℚ)⌋) = (C r n : ℤ) ∧
    ∏ k ∈ Icc (s + 1) (s + n),
        (1 - 2 * (⌊(k : ℚ) ^ r / (n : ℚ)⌋ - ⌊((k : ℚ) ^ r - 1) / (n : ℚ)⌋)) =
      (-1 : ℤ) ^ C r n := by
  classical
  have hI : Icc (s + 1) (s + n) = Ioc s (s + n) := by
    ext k
    simp only [mem_Icc, mem_Ioc]
    omega
  have hterm : ∀ k : ℤ, ⌊(k : ℚ) ^ r / (n : ℚ)⌋ - ⌊((k : ℚ) ^ r - 1) / (n : ℚ)⌋ =
      if (D r n : ℤ) ∣ k then 1 else 0 := by
    intro k
    have := floor_indicator_int hn (k ^ r)
    push_cast at this
    rw [this]
    exact if_congr (dvd_pow_iff hn hr k) rfl rfl
  rw [hI]
  constructor
  · simp only [hterm]
    rw [sum_boole, window_card hn hr]
  · have h1 : ∀ k : ℤ, (1 - 2 * (⌊(k : ℚ) ^ r / (n : ℚ)⌋ - ⌊((k : ℚ) ^ r - 1) / (n : ℚ)⌋)) =
        if (D r n : ℤ) ∣ k then -1 else 1 := by
      intro k
      rw [hterm]
      split_ifs <;> norm_num
    simp only [h1]
    rw [prod_ite, prod_const, prod_const_one, mul_one, window_card hn hr]

private lemma radical_factorization (n q : ℕ) :
    (UniqueFactorizationMonoid.radical n).factorization q =
      if q ∈ n.primeFactors then 1 else 0 := by
  classical
  rw [Nat.radical_eq_prod_primeFactors,
    Nat.factorization_prod (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero),
    Finsupp.finsetSum_apply]
  have : ∀ p ∈ n.primeFactors, p.factorization q = if p = q then 1 else 0 := by
    intro p hp
    rw [(Nat.prime_of_mem_primeFactors hp).factorization, Finsupp.single_apply]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']

private lemma D_factorization_apply (r n q : ℕ) :
    (D r n).factorization q = (n.factorization q + r - 1) / r := by
  rw [D_factorization, ceilFactorization, Finsupp.mapRange_apply]

/-- For `n > 1`, `C_r(n) = n / rad(n)` exactly when `r` is at least every exponent of `n`;
for `n = 1` both sides are `1`. -/
theorem threshold (n r : ℕ) (hr : 0 < r) :
    (1 < n → (C r n = n / UniqueFactorizationMonoid.radical n ↔
      ∀ p ∈ n.primeFactors, n.factorization p ≤ r)) ∧
    C r 1 = 1 / UniqueFactorizationMonoid.radical 1 := by
  refine ⟨fun hn => ?_, ?_⟩
  · have hn0 : n ≠ 0 := by omega
    have hrad0 : UniqueFactorizationMonoid.radical n ≠ 0 :=
      UniqueFactorizationMonoid.radical_ne_zero
    have hDrad : D r n = UniqueFactorizationMonoid.radical n ↔
        ∀ p ∈ n.primeFactors, n.factorization p ≤ r := by
      constructor
      · intro h p hp
        have e := congrArg (fun m => m.factorization p) h
        simp only [D_factorization_apply, radical_factorization, hp, ↓reduceIte] at e
        have := (Nat.div_lt_iff_lt_mul hr).mp (show (n.factorization p + r - 1) / r < 2 by omega)
        omega
      · intro h
        apply Nat.eq_of_factorization_eq (D_ne_zero r n) hrad0
        intro q
        rw [D_factorization_apply, radical_factorization]
        split_ifs with hq
        · have h1 := h q hq
          have h0 : 1 ≤ n.factorization q :=
            (Nat.prime_of_mem_primeFactors hq).factorization_pos_of_dvd hn0
              (Nat.dvd_of_mem_primeFactors hq)
          exact Nat.div_eq_of_lt_le (by omega) (by omega)
        · have h0 : n.factorization q = 0 :=
            Finsupp.notMem_support_iff.mp (by simpa [Nat.support_factorization] using hq)
          rw [h0, zero_add]
          exact Nat.div_eq_of_lt (by omega)
    rw [← hDrad]
    unfold C
    constructor
    · intro h
      rw [← Nat.div_div_self (D_dvd (by omega) hr) hn0, h,
        Nat.div_div_self UniqueFactorizationMonoid.radical_dvd_self hn0]
    · intro h
      rw [h]
  · have h1 : D r 1 = 1 := by simp [D, ceilFactorization]
    simp [C, h1]

private lemma sum_lt_mul {e r : ℕ} (he : 2 ≤ e) (hr : 2 ≤ r) : e + r - 1 < e * r := by
  obtain ⟨a, rfl⟩ : ∃ a, e = a + 2 := ⟨e - 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, r = b + 2 := ⟨r - 2, by omega⟩
  ring_nf
  omega

/-- For `r ≥ 2`, `C_r(n)` is even exactly when `4 ∣ n`. -/
private lemma C_even_iff {n r : ℕ} (hn : 0 < n) (hr : 2 ≤ r) : Even (C r n) ↔ 4 ∣ n := by
  have hC0 : C r n ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd hn (D_dvd hn (by omega))) (D_pos r n)).ne'
  have hfac : (C r n).factorization 2 =
      n.factorization 2 - (n.factorization 2 + r - 1) / r := by
    unfold C
    rw [Nat.factorization_div (D_dvd hn (by omega)), Finsupp.tsub_apply, D_factorization_apply]
  have h2 : 2 ∣ C r n ↔ 1 ≤ (C r n).factorization 2 := by
    simpa using Nat.prime_two.pow_dvd_iff_le_factorization (k := 1) hC0
  have h4 : 4 ∣ n ↔ 2 ≤ n.factorization 2 := by
    simpa using Nat.prime_two.pow_dvd_iff_le_factorization (k := 2) hn.ne'
  rw [even_iff_two_dvd, h2, h4, hfac]
  set e := n.factorization 2
  constructor
  · intro h
    by_contra hc
    interval_cases e
    · simp at h
    · rw [show 1 + r - 1 = r by omega, Nat.div_self (by omega)] at h
      omega
  · intro h
    have := (Nat.div_lt_iff_lt_mul (show 0 < r by omega)).mpr
      (sum_lt_mul h hr)
    omega

/-- For `r ≥ 2` and every integer `s`, the translated floor product equals `a(n+1)`. -/
theorem window_eq_numerator (n r : ℕ) (hn : 0 < n) (hr : 2 ≤ r) (s : ℤ) :
    ∏ k ∈ Icc (s + 1) (s + n),
        (1 - 2 * (⌊(k : ℚ) ^ r / (n : ℚ)⌋ - ⌊((k : ℚ) ^ r - 1) / (n : ℚ)⌋)) = a (n + 1) := by
  rw [(window n r hn (by omega) s).2, numerator_eq n hn]
  by_cases h4 : 4 ∣ n
  · simp only [h4, ↓reduceIte]
    exact ((C_even_iff hn hr).mpr h4).neg_one_pow
  · simp only [h4, ↓reduceIte]
    have hodd : Odd (C r n) := Nat.not_even_iff_odd.mp (fun h => h4 ((C_even_iff hn hr).mp h))
    exact hodd.neg_one_pow

end D5.S3.ArithSums.BrowneA164660RootCount
