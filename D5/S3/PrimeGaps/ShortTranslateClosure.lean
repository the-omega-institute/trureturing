/- GID: D5/S3/PrimeGaps/ShortTranslateClosure
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Port the simultaneous-root argument closing Proposition 1.2 on short translates. -/

/- Ported from openai/LongGapsBetweenPrimes commit 8f5fa88c88b4750028c05b66b081d56a92418054.
   Modified by trureturing on 2026-09-04: repository routing and module split. -/
/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import D5.S3.PrimeGaps.ResidueRemainders

namespace LongGapsBetweenPrimes

noncomputable section

/-- The finite weighted sieve, with every numerical loss displayed explicitly. -/
theorem finite_simultaneous_roots {P M k T : ℕ} {β C D : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hD : 1 ≤ D)
    (hM : 1 < M) (hT : 0 < T) (hmin : ∀ p ∈ P.primeFactors, M < p)
    (root : (p : PrimeIndex P) → Fin (k + 1) → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (htail : D ^ (-β) * Real.exp (((k + 1 : ℕ) : ℝ) * C * β) +
      16 * (((k + 1 : ℕ) : ℝ)) ^ 2 / M ≤ 1 / 2)
    (hgram : gramBound (k + 1) M D ≤ 5 / 4)
    (herr : 16 * D ^ 6 / T ≤ 1 / 8)
    (hbad : (((k + 1 : ℕ) : ℝ)) * (uncoveredBound k β C M D + 16 * D ^ 6 / T) < 1 / 4) :
    ∃ n < T, ∀ i : Fin (k + 1), ∃ p : PrimeIndex P, residueVector P n p = root p i := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hM' : (1 : ℝ) < M := by exact_mod_cast hM
  have hmin' : ∀ p ∈ P.primeFactors, (M : ℝ) ≤ p := by
    intro p hp
    exact_mod_cast (hmin p hp).le
  let A := coefficientMoment P 0 ^ (k + 1)
  have hbase := coefficientMoment_ge_one h.squarefree.ne_zero 0
  have hA : 1 ≤ A := one_le_pow₀ hbase
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hdiag : A / 2 ≤ diagonalMass P (k + 1) D := by
    have hlower := diagonalMass_normalized_lower (k := k + 1) h hβ hD0 (by omega) hmin
    change (1 - _) * A ≤ _ at hlower
    nlinarith only [hlower, mul_le_mul_of_nonneg_right htail hA0.le]
  apply exists_simultaneous_root_of_moments (D := D) root
    (L := A / 4) (U := (uncoveredBound k β C M D + 16 * D ^ 6 / T) * A)
  · have hmoment := (abs_le.mp (residueWeight_second_moment_bound (D := D) h.squarefree
      (Nat.succ_pos k) hM' hmin' root hroot)).1
    have herror := (abs_le.mp
      (residueWeight_interval_error h.squarefree hT hD root hroot h.abs_le_one)).1
    have hgram' := mul_le_mul_of_nonneg_right hgram (diagonalMass_nonneg P (k + 1) D)
    unfold gramBound at hgram'
    nlinarith only [hmoment, herror, hgram', hdiag, herr, hA]
  · intro i
    have hscale : coefficientMoment P 0 ^ k ≤ A := by
      simpa only [A, pow_succ] using
        le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans hbase) k) hbase
    have hmoment := (replacedResidueWeight_normalized_bound h hβ hD0 hM' hmin' root hroot i).trans
      (mul_le_mul_of_nonneg_left hscale (uncoveredBound_nonneg k β C M hD0.le))
    have herror := (abs_le.mp
      (replacedResidueWeight_interval_error h.squarefree hT hD root hroot h.abs_le_one i)).2
    have he0 : 0 ≤ 16 * D ^ 6 / (T : ℝ) := by positivity
    nlinarith only [hmoment, herror, mul_le_mul_of_nonneg_left hA he0]
  · nlinarith only [mul_lt_mul_of_pos_right hbad hA0]

/-- The divisor-product cutoff `exp (x / 8)`. -/
def sieveD (x : ℝ) : ℝ := Real.exp (x / 8)

/-- The averaging interval length, given by the integer part of `exp x`. -/
def sieveT (x : ℝ) : ℕ := ⌊Real.exp x⌋₊

/-- Rewrite `exp (-n * log x)` as `1 / x ^ n`. -/
lemma exp_neg_nat_mul_log {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.exp (-(n : ℝ) * Real.log x) = 1 / x ^ n := by
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hx, one_div]

/-- The truncation tail is at most `1 / x ^ 3` under the sieve size bounds. -/
lemma truncated_exponential_le {n : ℕ} {x β C : ℝ} (hx : 0 < x) (hβ : 0 ≤ β)
    (hsize : (n : ℝ) * C ≤ x / 16) (hlog : 48 * Real.log x ≤ x * β) :
    sieveD x ^ (-β) * Real.exp ((n : ℝ) * C * β) ≤ 1 / x ^ 3 := by
  rw [sieveD, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add,
    ← exp_neg_nat_mul_log hx 3]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hsize hβ]

/-- The truncation tail with doubled exponent is at most `1 / x ^ 6`. -/
lemma truncated_double_exponential_le {n : ℕ} {x β C : ℝ} (hx : 0 < x) (hβ : 0 ≤ β)
    (hsize : (n : ℝ) * C ≤ x / 16) (hlog : 48 * Real.log x ≤ x * β) :
    sieveD x ^ (-(2 * β)) * Real.exp ((n : ℝ) * C * (2 * β)) ≤ 1 / x ^ 6 := by
  rw [sieveD, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add,
    ← exp_neg_nat_mul_log hx 6]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hsize hβ]

/-- Bound the Gram factor by `exp (1 / x ^ 2)`. -/
lemma gramBound_le_simple {n : ℕ} {M x : ℝ} (hx : 1 ≤ x) (hn : (n : ℝ) ≤ x)
    (hM : x ^ 4 ≤ M - 1) (hlog : 1 ≤ Real.log M) :
    gramBound n M (sieveD x) ≤ Real.exp (1 / x ^ 2) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM0 : 0 < M - 1 := (pow_pos hx0 4).trans_le hM
  unfold gramBound sieveD
  rw [Real.log_exp]
  apply Real.exp_le_exp.mpr
  calc
    (n : ℝ) * (x / 8) / ((M - 1) * Real.log M) ≤ x * x / (x ^ 4 * 1) := by
      gcongr
      linarith
    _ = 1 / x ^ 2 := by field_simp

/-- The collision contribution is at most `16 / x ^ 2`. -/
lemma collisionBound_le_simple {n : ℕ} {M x : ℝ} (hx : 0 < x)
    (hn : (n : ℝ) ≤ x) (hM : x ^ 4 ≤ M) :
    16 * (n : ℝ) ^ 2 / M ≤ 16 / x ^ 2 := by
  calc
    16 * (n : ℝ) ^ 2 / M ≤ 16 * x ^ 2 / x ^ 4 := by gcongr
    _ = 16 / x ^ 2 := by field_simp

/-- The overlap contribution is at most `1 / (log 2 * x ^ 3)`. -/
lemma overlapBound_le_simple {M x : ℝ} (hx : 0 < x) (hM : x ^ 4 ≤ M) :
    4 * Real.log (sieveD x) / (M * Real.log 2) ≤ 1 / (Real.log 2 * x ^ 3) := by
  rw [sieveD, Real.log_exp]
  calc
    4 * (x / 8) / (M * Real.log 2) ≤ x / (x ^ 4 * Real.log 2) := by
      gcongr
      linarith
    _ = 1 / (Real.log 2 * x ^ 3) := by field_simp

/-- Bound the normalized uncovered contribution by an explicit multiple of `1 / x ^ 6`. -/
lemma uncoveredBound_le_simple {n : ℕ} {M x β C : ℝ} (hx : 1 ≤ x)
    (hβ : 0 ≤ β) (hn : (n : ℝ) ≤ x) (hsize : (n : ℝ) * C ≤ x / 16)
    (hlog : 48 * Real.log x ≤ x * β) (hM : x ^ 4 ≤ M - 1) (hlogM : 1 ≤ Real.log M)
    (hgram : Real.exp (1 / x ^ 2) ≤ 5 / 4) :
    uncoveredBound n β C M (sieveD x) ≤ (5 / 4) * (2 * C ^ 2 + 2 / (Real.log 2) ^ 2) / x ^ 6 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM' : x ^ 4 ≤ M := hM.trans (sub_le_self _ zero_le_one)
  have hM0 : 0 < M := (pow_pos hx0 4).trans_le hM'
  have hgram' := (gramBound_le_simple hx hn hM hlogM).trans hgram
  have hexp := truncated_double_exponential_le hx0 hβ hsize hlog
  have hover := overlapBound_le_simple hx0 hM'
  have hover0 : 0 ≤ 4 * Real.log (sieveD x) / (M * Real.log 2) := by
    rw [sieveD, Real.log_exp]
    positivity
  calc
    uncoveredBound n β C M (sieveD x) ≤
        (5 / 4) * (2 * C ^ 2 * (1 / x ^ 6) +
          2 * (1 / (Real.log 2 * x ^ 3)) ^ 2) := by
      unfold uncoveredBound
      rw [mul_assoc (2 * C ^ 2)]
      gcongr
      unfold sieveD
      positivity
    _ = _ := by ring

/-- For `x ≥ 2`, the lower sieve cutoff exceeds `x ^ 4` by at least one. -/
lemma sieveZ_lower {x : ℝ} (hx : 2 ≤ x) : x ^ 4 ≤ (sieveZ x : ℝ) - 1 := by
  have hx2 : 4 ≤ x ^ 2 := by nlinarith
  have hx4 : 16 ≤ x ^ 4 := by nlinarith [sq_nonneg (x ^ 2 - 4)]
  have hx6 : 4 * x ^ 4 ≤ x ^ 6 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx2) (sq_nonneg (x ^ 2))]
  unfold sieveZ
  nlinarith [Nat.lt_floor_add_one (x ^ 6)]

/-- The integer averaging length is at least half of `exp x`. -/
lemma sieveT_lower {x : ℝ} (hx : 2 ≤ x) : Real.exp x / 2 ≤ (sieveT x : ℝ) := by
  unfold sieveT
  linarith [Real.add_one_le_exp x, Nat.lt_floor_add_one (Real.exp x)]

/-- The interval averaging error is at most `32 / x ^ 3`. -/
lemma intervalError_le_simple {x : ℝ} (hx : 2 ≤ x) (hlog : 12 * Real.log x ≤ x) :
    16 * sieveD x ^ 6 / sieveT x ≤ 32 / x ^ 3 := by
  have hx0 : 0 < x := by linarith
  calc
    16 * sieveD x ^ 6 / sieveT x ≤ 16 * sieveD x ^ 6 / (Real.exp x / 2) := by
      gcongr
      exact sieveT_lower hx
    _ = 32 * Real.exp (-x / 4) := by
      rw [sieveD, ← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      calc
        _ = 32 * (Real.exp (6 * (x / 8)) / Real.exp x) := by ring
        _ = _ := by rw [← Real.exp_sub]; congr 1; congr 1; ring
    _ ≤ 32 * Real.exp (-(3 : ℝ) * Real.log x) := by
      gcongr
      linarith
    _ = 32 / x ^ 3 := by
      have he : Real.exp (-(3 : ℝ) * Real.log x) = 1 / x ^ 3 := by
        simpa only [Nat.cast_ofNat] using exp_neg_nat_mul_log hx0 3
      rw [he]
      ring

/-- The sieve tilt eventually satisfies `48 * log x ≤ x * sieveBeta x`. -/
lemma eventually_sieve_beta_scale : ∀ᶠ x : ℝ in Filter.atTop,
    48 * Real.log x ≤ x * sieveBeta x := by
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 3] with x hx hlog
  have hpow : (48 : ℝ) ≤ (Real.log x) ^ 4 := by
    calc
      (48 : ℝ) ≤ 3 ^ 4 := by norm_num
      _ ≤ (Real.log x) ^ 4 := pow_le_pow_left₀ (by norm_num) hlog 4
  calc
    48 * Real.log x ≤ (Real.log x) ^ 4 * Real.log x :=
      mul_le_mul_of_nonneg_right hpow (by linarith)
    _ = x * sieveBeta x := by
      unfold sieveBeta sieveUpperLog
      field_simp

/-- The numerical sieve error bounds hold for all sufficiently large `x`. -/
lemma eventually_simple_sieve_bounds (C : ℝ) : ∀ᶠ x : ℝ in Filter.atTop,
    Real.exp (1 / x ^ 2) ≤ 5 / 4 ∧
    1 / x ^ 3 + 16 / x ^ 2 ≤ 1 / 2 ∧
    32 / x ^ 3 ≤ 1 / 8 ∧
    ((5 / 4) * (2 * C ^ 2 + 2 / (Real.log 2) ^ 2)) / x ^ 5 + 32 / x ^ 2 < 1 / 4 := by
  have h (n : ℕ) (hn : n ≠ 0) :
      Filter.Tendsto (fun x : ℝ => 1 / x ^ n) Filter.atTop (nhds 0) := by
    simpa [one_div, hn] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).pow n
  have h₂ := h 2 (by decide)
  have h₃ := h 3 (by decide)
  have h₅ := h 5 (by decide)
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp h₂
  have htail := h₃.add (h₂.const_mul 16)
  have herr := h₃.const_mul 32
  have hbad := (h₅.const_mul ((5 / 4) * (2 * C ^ 2 + 2 / (Real.log 2) ^ 2))).add
    (h₂.const_mul 32)
  filter_upwards [hexp.eventually (gt_mem_nhds (by norm_num : Real.exp 0 < 5 / 4)),
    htail.eventually (gt_mem_nhds (by norm_num : 0 + 16 * 0 < (1 : ℝ) / 2)),
    herr.eventually (gt_mem_nhds (by norm_num : 32 * 0 < (1 : ℝ) / 8)),
    hbad.eventually (gt_mem_nhds (by simp :
      ((5 / 4) * (2 * C ^ 2 + 2 / (Real.log 2) ^ 2)) * 0 + 32 * 0 < (1 : ℝ) / 4))]
    with x hexp htail herr hbad
  exact ⟨hexp.le, by simpa only [mul_one_div] using htail.le,
    by simpa only [mul_one_div] using herr.le,
    by simpa only [mul_one_div] using hbad⟩

/-- The density threshold for simultaneously hitting all root families. -/
def sieveDelta : ℝ := 1 / (64 * weightConstant)

/-- The simultaneous-root density threshold is positive. -/
lemma sieveDelta_pos : 0 < sieveDelta := by
  exact one_div_pos.mpr (mul_pos (by norm_num) (zero_lt_one.trans weightConstant_gt_one))

/-- The simultaneous-root density threshold is less than one half. -/
lemma sieveDelta_lt_half : sieveDelta < 1 / 2 := by
  unfold sieveDelta
  apply one_div_lt_one_div_of_lt (by norm_num)
  linarith [weightConstant_gt_one]

/-- For large `x`, sufficiently small families of distinct roots can be hit simultaneously. -/
lemma eventually_simultaneous_roots : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ k : ℕ, (((k + 1 : ℕ) : ℝ)) ≤ sieveDelta * x →
    ∀ root : (p : PrimeIndex (sieveP x)) → Fin (k + 1) → Fin p.val,
    (∀ p, Function.Injective (root p)) →
    ∃ n < sieveT x, ∀ i : Fin (k + 1), ∃ p : PrimeIndex (sieveP x),
      residueVector (sieveP x) n p = root p i := by
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log x / x)
      Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  filter_upwards [eventually_sieve_coefficient_estimates, eventually_sieve_beta_scale,
    eventually_simple_sieve_bounds weightConstant, Filter.eventually_ge_atTop (2 : ℝ),
    tendsto_sieveZ.eventually_ge_atTop 2, tendsto_log_sieveZ.eventually_ge_atTop 1,
    hlog.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 12)]
    with x hcoeff hbeta ⟨hgram, htail, herr, hbad⟩ hx hZ hlogZ hlog
  intro k hk root hroot
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hC : 0 < weightConstant := zero_lt_one.trans weightConstant_gt_one
  have hn : ((k + 1 : ℕ) : ℝ) ≤ x := by
    have := mul_le_mul_of_nonneg_right sieveDelta_lt_half.le hx0.le
    linarith
  have hsize : ((k + 1 : ℕ) : ℝ) * weightConstant ≤ x / 16 := by
    calc
      _ ≤ (sieveDelta * x) * weightConstant := mul_le_mul_of_nonneg_right hk hC.le
      _ = x / 64 := by unfold sieveDelta; field_simp
      _ ≤ x / 16 := by linarith
  have hkn : (k : ℝ) ≤ x := by
    norm_num only [Nat.cast_add, Nat.cast_one] at hn
    linarith
  have hksize : (k : ℝ) * weightConstant ≤ x / 16 := by
    have : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
    exact (mul_le_mul_of_nonneg_right this hC.le).trans hsize
  have hM := sieveZ_lower hx
  have hM' : x ^ 4 ≤ (sieveZ x : ℝ) := hM.trans (sub_le_self _ zero_le_one)
  have hmin : ∀ p ∈ (sieveP x).primeFactors, sieveZ x < p := by
    intro p hp
    obtain ⟨hp, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact (mem_auxiliaryPrimes.mp (prime_dvd_auxiliaryProduct hp hdvd)).2.1
  have hT : 0 < sieveT x := by
    exact_mod_cast (half_pos (Real.exp_pos x)).trans_le (sieveT_lower hx)
  have herror := intervalError_le_simple hx (by
    have := (div_le_iff₀ hx0).mp hlog
    linarith)
  apply finite_simultaneous_roots hcoeff.2 hcoeff.1.le
    (show 1 ≤ sieveD x by unfold sieveD; exact Real.one_le_exp (by linarith))
    (by omega : 1 < sieveZ x) hT hmin root hroot
  · exact (add_le_add (truncated_exponential_le hx0 hcoeff.1.le hsize hbeta)
      (collisionBound_le_simple hx0 hn hM')).trans htail
  · exact (gramBound_le_simple hx1 hn hM hlogZ).trans hgram
  · exact herror.trans herr
  · have huncovered := uncoveredBound_le_simple hx1 hcoeff.1.le hkn hksize hbeta
      hM hlogZ hgram
    calc
      _ ≤ x * (((5 / 4) * (2 * weightConstant ^ 2 + 2 / (Real.log 2) ^ 2)) / x ^ 6 +
          32 / x ^ 3) := by
        gcongr
        exact add_nonneg
          (uncoveredBound_nonneg k (sieveBeta x) weightConstant (sieveZ x) (Real.exp_nonneg _))
          (by positivity)
      _ = ((5 / 4) * (2 * weightConstant ^ 2 + 2 / (Real.log 2) ^ 2)) / x ^ 5 +
          32 / x ^ 2 := by field_simp
      _ < 1 / 4 := hbad

/-- The upper sieve cutoff is eventually below the primorial up to `x`. -/
lemma eventually_sieveY_lt_primorial : ∀ᶠ x : ℝ in Filter.atTop,
    sieveY x < primorial ⌊x⌋₊ := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hpower : Filter.Tendsto (fun x : ℝ => 1 / (Real.log x) ^ 5)
      Filter.atTop (nhds 0) := by
    simpa [one_div] using
      ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp Real.tendsto_log_atTop).pow 5
  have hconstant : Filter.Tendsto (fun x : ℝ => Real.log 2 / x)
      Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop Filter.tendsto_id
  have hlog : Filter.Tendsto (fun x : ℝ => Real.log (x + 2) / x)
      Filter.atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp
        (Filter.tendsto_atTop_add_const_right Filter.atTop 2 Filter.tendsto_id)
  have hsqrt : Filter.Tendsto (fun x : ℝ => C / Real.sqrt x)
      Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hsmall := ((hpower.add hconstant).add hlog).add hsqrt
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
    hsmall.eventually_lt_const (by simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    with x hx hsmall
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hpower_eq : 1 / (Real.log x) ^ 5 = sieveUpperLog x / x := by
    rw [sieveUpperLog, div_right_comm, div_self hx0.ne']
  have hsqrt_eq : C / Real.sqrt x = C * Real.sqrt x / x := by
    apply (div_eq_div_iff (Real.sqrt_pos.mpr hx0).ne' hx0.ne').mpr
    rw [mul_assoc, Real.mul_self_sqrt hx0.le]
  rw [hpower_eq, hsqrt_eq, ← add_div, ← add_div, ← add_div] at hsmall
  have htheta : sieveUpperLog x < Chebyshev.theta x := by
    have hbound := (div_lt_iff₀ hx0).mp hsmall
    linarith [Chebyshev.psi_ge' hx0.le, hC x]
  unfold sieveY
  apply (Nat.floor_lt (Real.exp_pos _).le).mpr
  calc
    Real.exp (sieveUpperLog x) < Real.exp (Chebyshev.theta x) :=
      Real.exp_lt_exp.mpr htheta
    _ = (primorial ⌊x⌋₊ : ℝ) := by
      rw [Chebyshev.theta_eq_log_primorial, Real.exp_log (by
        exact_mod_cast primorial_pos ⌊x⌋₊)]

/-- Construct distinct modular roots forcing divisibility of the translated linear forms. -/
lemma exists_linear_roots {p k Q b : ℕ} (hp : p.Prime) (hQ : Q.Coprime p)
    (s : Fin k → ℕ) (hs : Function.Injective s) (hsmall : ∀ i, s i < p) :
    ∃ root : Fin k → Fin p, Function.Injective root ∧
      ∀ n i, n % p = (root i).val → p ∣ b + Q * (n + 1) + s i := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hQ' : (Q : ZMod p) ≠ 0 := ((ZMod.isUnit_iff_coprime Q p).mpr hQ).ne_zero
  let root (i : Fin k) : Fin p :=
    ⟨(-(b + Q + s i : ZMod p) / Q).val, ZMod.val_lt _⟩
  refine ⟨root, ?_, ?_⟩
  · intro i j hij
    have h := congrArg (fun a : Fin p => (a.val : ZMod p) * Q) hij
    simp only [root, ZMod.natCast_zmod_val, div_mul_cancel₀ _ hQ', neg_inj,
      add_right_inj] at h
    apply hs
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hsmall i), Nat.mod_eq_of_lt (hsmall j)]
      using (ZMod.natCast_eq_natCast_iff (s i) (s j) p).mp h
  · intro n i hn
    have hn' : (n : ZMod p) = -(b + Q + s i : ZMod p) / Q := by
      have h := congrArg (fun a : ℕ => (a : ZMod p)) hn
      simpa only [root, ZMod.natCast_mod, ZMod.natCast_zmod_val] using h
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    push_cast
    rw [hn']
    field_simp
    ring

/-- Proposition 1.2, proved with the explicit coefficient construction above. -/
theorem short_translates_with_sieveDelta : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ H : ℕ, x < H → (H : ℝ) ≤ x * (Real.log x) ^ 2 →
    ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 H → (S.card : ℝ) ≤ sieveDelta * x →
    ∀ b : ℕ, b < primorial ⌊x⌋₊ →
    ∃ t : ℕ, 1 ≤ t ∧ (t : ℝ) ≤ Real.exp x ∧
      ∀ s ∈ S, ¬Nat.Prime (b + primorial ⌊x⌋₊ * t + s) := by
  classical
  filter_upwards [eventually_simultaneous_roots, eventually_sieveY_lt_primorial,
    Filter.eventually_ge_atTop (2 : ℝ)] with x hroots hY hx
  intro H hxH hH S hS hcard b hb
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hHZ : H < sieveZ x := by
    have hlog : Real.log x ≤ x := by
      linarith [Real.log_le_sub_one_of_pos hx0]
    have hH' : (H : ℝ) ≤ x ^ 4 := calc
      (H : ℝ) ≤ x * (Real.log x) ^ 2 := hH
      _ ≤ x * x ^ 2 := by gcongr; exact Real.log_nonneg hx1
      _ = x ^ 3 := by ring
      _ ≤ x ^ 4 := pow_le_pow_right₀ hx1 (by decide)
    exact_mod_cast hH'.trans_lt (by linarith [sieveZ_lower hx] : x ^ 4 < (sieveZ x : ℝ))
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, le_rfl, by simpa using Real.one_le_exp hx0.le, by simp⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne.card_pos.ne'
  let e : Fin (k + 1) ≃ S :=
    (Fintype.equivFinOfCardEq (by simpa using hk : Fintype.card S = k + 1)).symm
  let s : Fin (k + 1) → ℕ := fun i => (e i).val
  have hp_bounds (p : PrimeIndex (sieveP x)) :
      p.val.Prime ∧ H < p.val ∧ p.val < primorial ⌊x⌋₊ := by
    obtain ⟨hp, hdvd, _⟩ := Nat.mem_primeFactors.mp p.property
    obtain ⟨_, hpZ, hpY⟩ := mem_auxiliaryPrimes.mp (prime_dvd_auxiliaryProduct hp hdvd)
    exact ⟨hp, hHZ.trans hpZ, hpY.trans_lt hY⟩
  have hlinear (p : PrimeIndex (sieveP x)) :
      ∃ root : Fin (k + 1) → Fin p.val, Function.Injective root ∧
        ∀ n i, n % p.val = (root i).val →
          p.val ∣ b + primorial ⌊x⌋₊ * (n + 1) + s i := by
    obtain ⟨hp, hHp, _⟩ := hp_bounds p
    have hpx : ⌊x⌋₊ < p.val :=
      (Nat.floor_lt hx0.le).mpr (hxH.trans (by exact_mod_cast hHp))
    have hcop : (primorial ⌊x⌋₊).Coprime p.val :=
      (hp.coprime_iff_not_dvd.mpr (hp.dvd_primorial_iff.not.mpr hpx.not_ge)).symm
    exact exists_linear_roots hp hcop s (Subtype.val_injective.comp e.injective)
      (fun i => (Finset.mem_Icc.mp (hS (e i).property)).2.trans_lt hHp)
  choose root hinj hdiv using hlinear
  obtain ⟨n, hn, hhit⟩ := hroots k (by simpa [hk] using hcard) root hinj
  refine ⟨n + 1, by omega, ?_, ?_⟩
  · exact (by exact_mod_cast hn : ((n + 1 : ℕ) : ℝ) ≤ sieveT x).trans
      (Nat.floor_le (Real.exp_pos x).le)
  · intro a ha hprime
    obtain ⟨i, hi⟩ := e.surjective ⟨a, ha⟩
    obtain ⟨p, hp⟩ := hhit i
    have hdvd := hdiv p n i (congrArg Fin.val hp)
    have hsi : s i = a := congrArg Subtype.val hi
    rw [hsi] at hdvd
    obtain ⟨hpprime, _, hpQ⟩ := hp_bounds p
    have hQ : primorial ⌊x⌋₊ ≤ primorial ⌊x⌋₊ * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have hlt : p.val < b + primorial ⌊x⌋₊ * (n + 1) + a := by omega
    exact (hprime.eq_one_or_self_of_dvd _ hdvd).elim hpprime.ne_one (ne_of_lt hlt)

/-- The sparse-set translation bound of Proposition 1.2. -/
lemma short_translates : ShortTranslates :=
  ⟨sieveDelta, sieveDelta_pos, sieveDelta_lt_half, short_translates_with_sieveDelta⟩

end

end LongGapsBetweenPrimes
