/- GID: D5/S3/PrimeGaps/CloitreSquareRootPrimeGapRefutation
   generality: G
   mirror-B: D5/B/S3/PrimeGaps/CloitreSquareRootPrimeGapRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.NumberTheory.Chebyshev]
   utility: none
   digest: The OEIS A079063 eventual square-root lower bound contradicts prime counting. -/

import Mathlib.NumberTheory.Chebyshev

namespace D5.S3.PrimeGaps.CloitreSquareRootPrimeGapRefutation

open Real

noncomputable section

/-- OEIS A079063 (Cloitre, 2003), with the first prime indexed by `1`.
The `sInf` convention assigns zero to an empty set; the witness set is nonempty
for every positive index. -/
def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧
    1 < sqrt (Nat.nth Nat.Prime (n + k - 1)) - sqrt (Nat.nth Nat.Prime (n - 1))}

/-- The weakest quantified reading of OEIS A079063's asserted eventual lower
bound. Its refutation also rules out the proposed `c = 0.4` and a positive
liminf; it does not assert the existence of either proposed limit. -/
def claim : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c * sqrt n < a n

private theorem sqrt_prime_quadratic_step
    (c : ℝ) (N r m : ℕ) (hc : 0 < c)
    (hclaim : ∀ n : ℕ, N ≤ n → c * sqrt n < (a n : ℝ))
    (hr : 1 < c * r) (hm : 1 ≤ m) (hN : N ≤ (r * m) ^ 2) :
    sqrt (Nat.nth Nat.Prime ((r * (m + 1)) ^ 2)) ≤
      sqrt (Nat.nth Nat.Prime ((r * m) ^ 2)) + (3 * r * r : ℕ) := by
  let t0 := (r * m) ^ 2
  let L := 3 * r * r
  have hlocal (t : ℕ) (ht : t0 ≤ t) :
      sqrt (Nat.nth Nat.Prime (t + m)) ≤ sqrt (Nat.nth Nat.Prime t) + 1 := by
    have hroot : (↑(r * m) : ℝ) ≤ sqrt (↑(t + 1) : ℝ) := by
      apply Real.le_sqrt_of_sq_le
      exact_mod_cast (ht.trans (Nat.le_succ t))
    have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
    have hmc : (m : ℝ) < c * (↑(r * m) : ℝ) := by
      have hmul := mul_lt_mul_of_pos_right hr hmreal
      simpa only [one_mul, Nat.cast_mul, mul_assoc] using hmul
    have hca : (m : ℝ) < (a (t + 1) : ℝ) :=
      (hmc.trans_le (mul_le_mul_of_nonneg_left hroot hc.le)).trans
        (hclaim (t + 1) (by omega))
    by_contra h
    have hdiff : 1 < sqrt (Nat.nth Nat.Prime (t + m)) -
        sqrt (Nat.nth Nat.Prime t) := by
      push Not at h
      linarith
    have hmem : m ∈ {j : ℕ | 0 < j ∧
        1 < sqrt (Nat.nth Nat.Prime (t + 1 + j - 1)) -
          sqrt (Nat.nth Nat.Prime (t + 1 - 1))} := by
      simp only [Set.mem_ofPred_eq]
      constructor
      · omega
      · simpa only [show t + 1 + m - 1 = t + m by omega,
          show t + 1 - 1 = t by omega] using hdiff
    have hma : m < a (t + 1) := by exact_mod_cast hca
    exact (not_lt_of_ge (Nat.sInf_le hmem)) hma
  have hchain (i : ℕ) :
      sqrt (Nat.nth Nat.Prime (t0 + i * m)) ≤
        sqrt (Nat.nth Nat.Prime t0) + i := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hstep := hlocal (t0 + i * m) (Nat.le_add_right _ _)
      calc
        sqrt (Nat.nth Nat.Prime (t0 + (i + 1) * m)) =
            sqrt (Nat.nth Nat.Prime ((t0 + i * m) + m)) := by
              exact congrArg (fun j : ℕ => sqrt (Nat.nth Nat.Prime j))
                (by simp only [Nat.add_mul, one_mul]; omega :
                  t0 + (i + 1) * m = (t0 + i * m) + m)
        _ ≤ sqrt (Nat.nth Nat.Prime (t0 + i * m)) + 1 := hstep
        _ ≤ sqrt (Nat.nth Nat.Prime t0) + (↑(i + 1) : ℝ) := by
          push_cast
          linarith [ih]
  have hR : r * r ≤ (r * r) * m := by
    calc
      r * r = (r * r) * 1 := by omega
      _ ≤ (r * r) * m := Nat.mul_le_mul_left _ hm
  have hindex : (r * (m + 1)) ^ 2 ≤ t0 + L * m := by
    dsimp [t0, L]
    nlinarith [hR]
  have hp := (Nat.nth_monotone Nat.infinite_setOfPred_prime) hindex
  have hs : sqrt (Nat.nth Nat.Prime ((r * (m + 1)) ^ 2)) ≤
      sqrt (Nat.nth Nat.Prime (t0 + L * m)) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hp)
  exact hs.trans (by simpa only [t0, L] using hchain L)

private theorem sqrt_prime_quadratic_linear
    (c : ℝ) (N r : ℕ) (hc : 0 < c)
    (hclaim : ∀ n : ℕ, N ≤ n → c * sqrt n < (a n : ℝ))
    (hr : 1 < c * r) :
    ∃ B : ℝ, 0 < B ∧ ∀ m : ℕ, N + 1 ≤ m →
      sqrt (Nat.nth Nat.Prime ((r * m) ^ 2)) ≤ B * m := by
  have hr1 : 1 ≤ r := by
    by_contra h
    have hzero : r = 0 := by omega
    simp [hzero] at hr
    linarith
  let m0 := N + 1
  let L := 3 * r * r
  let B : ℝ := sqrt (Nat.nth Nat.Prime ((r * m0) ^ 2)) + L
  have hL : (0 : ℝ) < L := by
    dsimp [L]
    have hrpos : 0 < r := by omega
    positivity
  have hB : 0 < B := by
    dsimp [B]
    exact add_pos_of_nonneg_of_pos (sqrt_nonneg _) hL
  refine ⟨B, hB, ?_⟩
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    have hm0 : (1 : ℝ) ≤ m0 := by
      change (1 : ℝ) ≤ (N + 1 : ℕ)
      exact_mod_cast (by omega : 1 ≤ N + 1)
    have hB0 : 0 ≤ B := hB.le
    dsimp [B]
    nlinarith [mul_nonneg hB0 (sub_nonneg.mpr hm0)]
  | succ m hm ih =>
    have hN : N ≤ (r * m) ^ 2 := by
      have hNm : N ≤ m := by omega
      have hrm : m ≤ r * m := by
        calc
          m = 1 * m := by omega
          _ ≤ r * m := Nat.mul_le_mul_right m hr1
      have hx : 1 ≤ r * m := by omega
      have hpow : r * m ≤ (r * m) ^ 2 := by
        nlinarith [Nat.mul_le_mul_left (r * m) hx]
      exact hNm.trans (hrm.trans hpow)
    have hstep := sqrt_prime_quadratic_step c N r m hc hclaim hr (by omega) hN
    have hLB : (L : ℝ) ≤ B := by
      dsimp [B]
      exact le_add_of_nonneg_left (sqrt_nonneg _)
    calc
      sqrt (Nat.nth Nat.Prime ((r * (m + 1)) ^ 2)) ≤
          sqrt (Nat.nth Nat.Prime ((r * m) ^ 2)) + (L : ℝ) := by
            simpa only [L] using hstep
      _ ≤ B * (↑(m + 1) : ℝ) := by push_cast; nlinarith [ih, hLB]

/-- Refutation of the eventual positive square-root lower bound proposed in
OEIS A079063. The contradiction holds on arbitrarily large quadratic blocks,
not at a finite exceptional index. -/
theorem result : ¬ claim := by
  have a_witness_nonempty (n : ℕ) (hn : 0 < n) :
      {k : ℕ | 0 < k ∧
        1 < sqrt (Nat.nth Nat.Prime (n + k - 1)) -
          sqrt (Nat.nth Nat.Prime (n - 1))}.Nonempty := by
    obtain ⟨k, hk⟩ := exists_nat_gt
      ((sqrt (Nat.nth Nat.Prime (n - 1) : ℝ) + 1) ^ 2)
    have hq : (k : ℝ) ≤ Nat.nth Nat.Prime (n + k) := by
      exact_mod_cast (show k ≤ Nat.nth Nat.Prime (n + k) by
        have := Nat.add_two_le_nth_prime (n + k)
        omega)
    have hs : (sqrt (Nat.nth Nat.Prime (n - 1) : ℝ) + 1) ^ 2 <
        (Nat.nth Nat.Prime (n + k) : ℝ) := hk.trans_le hq
    have hroot : sqrt (Nat.nth Nat.Prime (n - 1) : ℝ) + 1 <
        sqrt (Nat.nth Nat.Prime (n + k) : ℝ) := Real.lt_sqrt_of_sq_lt hs
    refine ⟨k + 1, ?_⟩
    simp only [Set.mem_ofPred_eq]
    constructor
    · omega
    · have hidx : n + (k + 1) - 1 = n + k := by omega
      rw [hidx]
      linarith
  rintro ⟨c, hc, N, hclaim⟩
  obtain ⟨r, hr0⟩ := exists_nat_gt (1 / c)
  have hr : 1 < c * (r : ℝ) := by
    have := (div_lt_iff₀ hc).mp hr0
    nlinarith
  obtain ⟨B, hB, hlinear⟩ := sqrt_prime_quadratic_linear c N r hc hclaim hr
  let ε : ℝ := 1 / (2 * B ^ 2)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ ε * x := by
    filter_upwards [Chebyshev.eventually_primeCounting_le (show (0 : ℝ) < 1 by norm_num),
      Real.tendsto_log_atTop.eventually_ge_atTop ((log 4 + 1) / ε),
      Filter.eventually_gt_atTop (1 : ℝ)] with x hpi hlog hx
    have hx0 : 0 ≤ x := le_trans (by norm_num : (0 : ℝ) ≤ 1) hx.le
    have hlogpos : 0 < log x := Real.log_pos hx
    have hb : log 4 + 1 ≤ ε * log x := by
      have := (div_le_iff₀ hε).mp hlog
      nlinarith
    have hbound : (log 4 + 1) * x / log x ≤ ε * x := by
      apply (div_le_iff₀ hlogpos).2
      nlinarith [mul_le_mul_of_nonneg_right hb hx0]
    exact hpi.trans hbound
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨K, hK⟩ := exists_nat_gt T
  let m := N + K + 2
  have hm : N + 1 ≤ m := by dsimp [m]; omega
  have hmpos : 1 ≤ m := by omega
  have hr1 : 1 ≤ r := by
    by_contra h
    have hzero : r = 0 := by omega
    simp [hzero] at hr
    linarith
  have hindex : m ≤ (r * m) ^ 2 := by
    have hrm : m ≤ r * m := by
      calc
        m = 1 * m := by omega
        _ ≤ r * m := Nat.mul_le_mul_right m hr1
    have hx : 1 ≤ r * m := by omega
    have hpow : r * m ≤ (r * m) ^ 2 := by
      nlinarith [Nat.mul_le_mul_left (r * m) hx]
    exact hrm.trans hpow
  let q := Nat.nth Nat.Prime ((r * m) ^ 2)
  have hmq : m ≤ q :=
    hindex.trans ((Nat.le_add_right _ _).trans (Nat.add_two_le_nth_prime _))
  have hTq : T ≤ (q : ℝ) := by
    have hKm : K ≤ m := by dsimp [m]; omega
    have hKq : (K : ℝ) ≤ q := by exact_mod_cast hKm.trans hmq
    exact hK.le.trans hKq
  have hsmall : (Nat.primeCounting q : ℝ) ≤ ε * q := by
    simpa only [Nat.floor_natCast] using hT (q : ℝ) hTq
  have hcount : ((r * m) ^ 2 : ℕ) ≤ Nat.primeCounting q := by
    have hmono := Nat.monotone_primeCounting' (Nat.le_succ q)
    simpa only [q, Nat.primeCounting, Nat.primeCounting'_nth_eq] using hmono
  have hlin : sqrt (q : ℝ) ≤ B * m := hlinear m hm
  have hq : (q : ℝ) ≤ B ^ 2 * (m : ℝ) ^ 2 := by
    have hsq : (sqrt (q : ℝ)) ^ 2 = q := Real.sq_sqrt (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr hlin)
      (add_nonneg (sqrt_nonneg (q : ℝ)) (by positivity : 0 ≤ B * (m : ℝ)))]
  have hcountRCast : (((r * m) ^ 2 : ℕ) : ℝ) ≤ (Nat.primeCounting q : ℝ) := by
    exact_mod_cast hcount
  have hcountR : (((r * m) ^ 2 : ℕ) : ℝ) ≤ ε * q :=
    hcountRCast.trans hsmall
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hεB : ε * B ^ 2 = 1 / 2 := by
    dsimp [ε]
    field_simp
  have hsmallR : (((r * m) ^ 2 : ℕ) : ℝ) ≤ (m : ℝ) ^ 2 / 2 := by
    calc
      (((r * m) ^ 2 : ℕ) : ℝ) ≤ ε * (q : ℝ) := hcountR
      _ ≤ ε * (B ^ 2 * (m : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hq hε.le
      _ = (m : ℝ) ^ 2 / 2 := by rw [← mul_assoc, hεB]; ring
  have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith [sq_nonneg ((r : ℝ) - 1)]
  have hm2 : 0 < (m : ℝ) ^ 2 := sq_pos_of_pos hmR
  have hbound : (m : ℝ) ^ 2 ≤ ((r : ℝ) * m) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr2) hm2.le]
  push_cast at hsmallR
  nlinarith [hbound, hm2]

end

end D5.S3.PrimeGaps.CloitreSquareRootPrimeGapRefutation
