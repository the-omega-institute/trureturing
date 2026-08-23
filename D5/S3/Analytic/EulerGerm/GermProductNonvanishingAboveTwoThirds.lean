/- GID: D5/S3/Analytic/EulerGerm/GermProductNonvanishingAboveTwoThirds
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Odd-prime local factors are nonzero on the whole open convergence half-plane; the prime-2 local factor and the full Euler product are nonzero for Re s at least 2/3; only prime 2 stays undecided below 2/3. -/

import Mathlib
import D5.S3.Analytic.EulerGerm.GermProductNonvanishing

/- Provenance: Native proof over pinned mathlib. -/
/- OPEN NOTE: The residual undecided strip is exactly

     1 / Real.goldenRatio ^ 2 < Re s < 2 / 3.

   Its only unresolved prime is 2.  The odd-prime theorem below proves that
   every prime p >= 3 has a nonzero local factor throughout the full open
   convergence half-plane.  At p = 2, the geometric tail argument proved here
   closes from Re s >= 2 / 3, but does not show that its tail norm is below one
   in the displayed residual strip.  This is a limitation of that single-prime
   majorant, not evidence for or against a local zero there. -/
/- SEARCH RECEIPT (2026-08-23):
   * Repository `D5/**/*.lean`, searched with `germ.*(prime|odd|two|nonvanish|
     ne_zero)`, `local_factor.*(prime|odd|two|ne_zero)`,
     `re_ge.*golden`, `germLocalFactor`, `excited_tail`, and
     `GermProductNonvanishing`.  The only germ nonvanishing declarations hit
     were the conditional and `Re s >= 1` theorems in
     `GermProductNonvanishing.lean`; no prime-separated or sub-one-threshold
     theorem was found.  `PrimeExponentLaw.lean` mentions that file only in an
     analytic comparison, and the displacement/zero-window hits concern other
     statements.
   * Pinned mathlib, searched with `nonvanishing`, `ne_zero` together with
     `tprod`/`Multipliable`, `Euler product`, and `one_add_ne_zero`.  Exact hit:
     `tprod_one_add_ne_zero_of_summable` in
     `Analysis/SpecialFunctions/Log/Summable.lean:216`; it is not reapplied
     here because the public repository theorem
     `germ_product_ne_zero_of_local_factors_ne_zero` already encapsulates that
     product step and is invoked below.
   * Pinned mathlib prime search hit `Nat.Prime.two_le`,
     `Nat.Prime.eq_two_or_odd'`, `Nat.Prime.odd_of_ne_two`, and
     `Nat.Prime.odd_iff` in `Data/Nat/Prime/{Defs,Basic}.lean`.  The last two
     are used below to derive `3 <= p` from primality and `p != 2`.
   * Pinned mathlib golden-ratio search hit `Real.goldenRatio_sq` in
     `NumberTheory/Real/GoldenRatio.lean:83`; it is used below.  The real-power
     search hit `Real.rpow_add`, `Real.rpow_mul`,
     `Real.rpow_lt_rpow_of_exponent_lt`, `Real.rpow_le_rpow_of_exponent_le`,
     `Real.rpow_le_rpow_of_nonpos`, and the geometric-series theorems used
     below.
   * Reused public repository declarations:
     `o5_beta_power_law`, `o5_beta_growth`,
     `germ_excited_norm_summable`, `germLocalFactor_eq_one_add`, and
     `germ_product_ne_zero_of_local_factors_ne_zero`.  The needed tail
     definition and beta/tail estimates in `GermProductNonvanishing.lean` are
     private and cannot be imported.  This file therefore rebuilds only the
     thinnest local tail layer needed for the prime split; it does not reprove
     convergence, the local-factor decomposition, or the infinite-product
     nonvanishing theorem. -/

namespace D5.S3.Analytic.EulerGerm.GermProductNonvanishingAboveTwoThirds

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GermProductConvergence
open D5.S3.Analytic.EulerGerm.GermProductNonvanishing

noncomputable section

private def excitedTail (s : ℂ) (p : ℕ) : ℂ :=
  ∑' v : ℕ, (p : ℂ) ^ (-s * (o5Beta (v + 1) : ℂ))

private theorem three_eighths_lt_golden_convergence :
    (3 / 8 : ℝ) < 1 / Real.goldenRatio ^ 2 := by
  rw [lt_div_iff₀ (sq_pos_of_pos Real.goldenRatio_pos)]
  rw [Real.goldenRatio_sq, Real.goldenRatio]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5),
    Real.sqrt_nonneg 5]

private theorem golden_sq_gt_five_halves :
    (5 / 2 : ℝ) < Real.goldenRatio ^ 2 := by
  rw [Real.goldenRatio_sq, Real.goldenRatio]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5),
    Real.sqrt_nonneg 5]

private theorem o5_beta_succ_ge_golden_sq_add (v : ℕ) :
    Real.goldenRatio ^ 2 + (v : ℝ) ≤ o5Beta (v + 1) := by
  cases v with
  | zero => simpa using o5_beta_power_law.1.symm.le
  | succ v =>
      have hsqrt : (2 : ℝ) ≤ Real.sqrt 5 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5),
          Real.sqrt_nonneg 5]
      have hmul :
          2 * ((v + 2 : ℕ) : ℝ) ≤
            Real.sqrt 5 * ((v + 2 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hsqrt (by positivity)
      have hgrowth := o5_beta_growth (v + 2)
      have hinv : 1 / Real.goldenRatio = Real.goldenRatio - 1 := by
        rw [one_div, Real.inv_goldenRatio]
        linarith [Real.goldenRatio_add_goldenConj]
      rw [hinv] at hgrowth
      rw [Real.goldenRatio_sq]
      push_cast at hmul hgrowth ⊢
      nlinarith

private theorem three_rpow_neg_three_eighths_lt_two_thirds :
    (3 : ℝ) ^ (-(3 / 8 : ℝ)) < 2 / 3 := by
  rw [← Real.rpow_lt_rpow_iff (Real.rpow_nonneg (by norm_num) _)
    (by positivity : (0 : ℝ) ≤ 2 / 3) (by norm_num : (0 : ℝ) < 8)]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num [Real.rpow_neg_natCast, Real.rpow_natCast]

private theorem two_rpow_neg_two_thirds_lt_two_thirds :
    (2 : ℝ) ^ (-(2 / 3 : ℝ)) < 2 / 3 := by
  rw [← Real.rpow_lt_rpow_iff (Real.rpow_nonneg (by norm_num) _)
    (by positivity : (0 : ℝ) ≤ 2 / 3) (by norm_num : (0 : ℝ) < 3)]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [Real.rpow_neg_natCast, Real.rpow_natCast]

private theorem two_rpow_neg_five_thirds_lt_one_third :
    (2 : ℝ) ^ (-(5 / 3 : ℝ)) < 1 / 3 := by
  rw [← Real.rpow_lt_rpow_iff (Real.rpow_nonneg (by norm_num) _)
    (by positivity : (0 : ℝ) ≤ 1 / 3) (by norm_num : (0 : ℝ) < 3)]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [Real.rpow_neg_natCast, Real.rpow_natCast]

private theorem excited_term_norm_le_geometric (s : ℂ)
    (hs : 1 / Real.goldenRatio ^ 2 < s.re) (p : Nat.Primes) (v : ℕ) :
    ‖(p : ℂ) ^ (-s * (o5Beta (v + 1) : ℂ))‖ ≤
      (p : ℝ) ^ (-s.re * Real.goldenRatio ^ 2) *
        ((p : ℝ) ^ (-s.re)) ^ v := by
  have hphi : 0 < Real.goldenRatio ^ 2 :=
    sq_pos_of_pos Real.goldenRatio_pos
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  have hbeta := o5_beta_succ_ge_golden_sq_add v
  have hproduct :
      s.re * (Real.goldenRatio ^ 2 + (v : ℝ)) ≤
        s.re * o5Beta (v + 1) :=
    mul_le_mul_of_nonneg_left hbeta hspos.le
  have hexponent :
      -s.re * o5Beta (v + 1) ≤
        -s.re * Real.goldenRatio ^ 2 + (-s.re) * (v : ℝ) := by
    nlinarith
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  calc
    (p : ℝ) ^ (-s.re * o5Beta (v + 1)) ≤
        (p : ℝ) ^
          (-s.re * Real.goldenRatio ^ 2 + (-s.re) * (v : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast p.prop.one_le) hexponent
    _ = (p : ℝ) ^ (-s.re * Real.goldenRatio ^ 2) *
        ((p : ℝ) ^ (-s.re)) ^ v := by
      rw [Real.rpow_add (by exact_mod_cast p.prop.pos)]
      congr 1
      rw [← Real.rpow_natCast,
        ← Real.rpow_mul (by exact_mod_cast p.prop.pos.le)]

private theorem excited_tail_norm_lt_one_of_rpow_add_lt_one (s : ℂ)
    (hs : 1 / Real.goldenRatio ^ 2 < s.re) (p : Nat.Primes)
    (hsmall :
      (p : ℝ) ^ (-s.re * Real.goldenRatio ^ 2) +
        (p : ℝ) ^ (-s.re) < 1) :
    ‖excitedTail s p‖ < 1 := by
  let A : ℝ := (p : ℝ) ^ (-s.re * Real.goldenRatio ^ 2)
  let q : ℝ := (p : ℝ) ^ (-s.re)
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  have hqnonneg : 0 ≤ q := Real.rpow_nonneg (by exact_mod_cast p.prop.pos.le) _
  have hq : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.prop.one_lt) (neg_neg_of_pos hspos)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hqnonneg]
    exact hq
  have hgeom : Summable (fun v : ℕ => A * q ^ v) :=
    (summable_geometric_of_norm_lt_one hqnorm).mul_left A
  have hnorm : Summable (fun v : ℕ =>
      ‖(p : ℂ) ^ (-s * (o5Beta (v + 1) : ℂ))‖) :=
    (germ_excited_norm_summable s hs).prod_factor p
  calc
    ‖excitedTail s p‖ ≤
        ∑' v : ℕ, ‖(p : ℂ) ^ (-s * (o5Beta (v + 1) : ℂ))‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' v : ℕ, A * q ^ v :=
      hnorm.tsum_le_tsum (fun v => by
        simpa [A, q] using excited_term_norm_le_geometric s hs p v) hgeom
    _ = A * (1 - q)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hqnonneg hq]
    _ < 1 := by
      rw [← div_eq_mul_inv, div_lt_one (sub_pos.mpr hq)]
      dsimp [A, q]
      linarith

private theorem local_factor_ne_zero_of_tail_norm_lt_one (s : ℂ)
    (hs : 1 / Real.goldenRatio ^ 2 < s.re) (p : Nat.Primes)
    (htail : ‖excitedTail s p‖ < 1) : germLocalFactor s p ≠ 0 := by
  rw [germLocalFactor_eq_one_add s p p.prop hs]
  change 1 + excitedTail s p ≠ 0
  intro hzero
  have htail_eq : excitedTail s p = -1 := by
    linear_combination hzero
  rw [htail_eq, norm_neg, norm_one] at htail
  exact lt_irrefl 1 htail

/-- Every prime other than 2 has a nonzero golden local factor on the full
open convergence half-plane. -/
theorem germ_local_factor_ne_zero_of_prime_ne_two
    (s : ℂ) (hs : 1 / Real.goldenRatio ^ 2 < s.re) (p : Nat.Primes)
    (hp : (p : ℕ) ≠ 2) : germLocalFactor s p ≠ 0 := by
  have hp3 : 3 ≤ (p : ℕ) :=
    p.prop.odd_iff.mp (p.prop.odd_of_ne_two hp)
  have hp3r : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hA :
      (p : ℝ) ^ (-s.re * Real.goldenRatio ^ 2) < 1 / 3 := by
    have hexponent : -s.re * Real.goldenRatio ^ 2 < (-1 : ℝ) := by
      have := (div_lt_iff₀ (sq_pos_of_pos Real.goldenRatio_pos)).mp hs
      nlinarith
    calc
      (p : ℝ) ^ (-s.re * Real.goldenRatio ^ 2) <
          (p : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt
          (by exact_mod_cast p.prop.one_lt) hexponent
      _ = ((p : ℝ)⁻¹) := Real.rpow_neg_one _
      _ ≤ (3 : ℝ)⁻¹ :=
        (inv_le_inv₀ (by exact_mod_cast p.prop.pos) (by norm_num)).2 hp3r
      _ = 1 / 3 := by norm_num
  have hq : (p : ℝ) ^ (-s.re) < 2 / 3 := by
    have hs38 : (3 / 8 : ℝ) < s.re :=
      three_eighths_lt_golden_convergence.trans hs
    calc
      (p : ℝ) ^ (-s.re) < (p : ℝ) ^ (-(3 / 8 : ℝ)) :=
        Real.rpow_lt_rpow_of_exponent_lt
          (by exact_mod_cast p.prop.one_lt) (by linarith)
      _ ≤ (3 : ℝ) ^ (-(3 / 8 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hp3r (by norm_num)
      _ < 2 / 3 := three_rpow_neg_three_eighths_lt_two_thirds
  apply local_factor_ne_zero_of_tail_norm_lt_one s hs p
  apply excited_tail_norm_lt_one_of_rpow_add_lt_one s hs p
  linarith

private theorem golden_convergence_lt_two_thirds :
    1 / Real.goldenRatio ^ 2 < (2 / 3 : ℝ) := by
  rw [div_lt_iff₀ (sq_pos_of_pos Real.goldenRatio_pos)]
  nlinarith [golden_sq_gt_five_halves]

/-- The prime-2 golden local factor is nonzero on `Re s >= 2/3`. -/
theorem germ_local_factor_two_ne_zero_of_re_ge_two_thirds
    (s : ℂ) (hs : (2 / 3 : ℝ) ≤ s.re) :
    germLocalFactor s (⟨2, Nat.prime_two⟩ : Nat.Primes) ≠ 0 := by
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hconv : 1 / Real.goldenRatio ^ 2 < s.re :=
    golden_convergence_lt_two_thirds.trans_le hs
  have hA :
      (2 : ℝ) ^ (-s.re * Real.goldenRatio ^ 2) < 1 / 3 := by
    have hproduct : (5 / 3 : ℝ) < s.re * Real.goldenRatio ^ 2 := by
      nlinarith [golden_sq_gt_five_halves,
        sq_pos_of_pos Real.goldenRatio_pos]
    calc
      (2 : ℝ) ^ (-s.re * Real.goldenRatio ^ 2) <
          (2 : ℝ) ^ (-(5 / 3 : ℝ)) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      _ < 1 / 3 := two_rpow_neg_five_thirds_lt_one_third
  have hq : (2 : ℝ) ^ (-s.re) < 2 / 3 := by
    calc
      (2 : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-(2 / 3 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ < 2 / 3 := two_rpow_neg_two_thirds_lt_two_thirds
  apply local_factor_ne_zero_of_tail_norm_lt_one s hconv p
  apply excited_tail_norm_lt_one_of_rpow_add_lt_one s hconv p
  change (2 : ℝ) ^ (-s.re * Real.goldenRatio ^ 2) +
    (2 : ℝ) ^ (-s.re) < 1
  linarith

/-- The golden Euler product is nonzero on the half-plane `Re s >= 2/3`. -/
theorem germ_product_ne_zero_of_re_ge_two_thirds
    (s : ℂ) (hs : (2 / 3 : ℝ) ≤ s.re) :
    (∏' p : Nat.Primes, germLocalFactor s p) ≠ 0 := by
  have hconv : 1 / Real.goldenRatio ^ 2 < s.re :=
    golden_convergence_lt_two_thirds.trans_le hs
  apply germ_product_ne_zero_of_local_factors_ne_zero s hconv
  intro p
  by_cases hp : (p : ℕ) = 2
  · have hp_eq : p = (⟨2, Nat.prime_two⟩ : Nat.Primes) :=
      Nat.Primes.coe_nat_injective hp
    rw [hp_eq]
    exact germ_local_factor_two_ne_zero_of_re_ge_two_thirds s hs
  · exact germ_local_factor_ne_zero_of_prime_ne_two s hconv p hp

end

end D5.S3.Analytic.EulerGerm.GermProductNonvanishingAboveTwoThirds
