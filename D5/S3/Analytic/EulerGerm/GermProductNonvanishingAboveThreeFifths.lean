/- GID: D5/S3/Analytic/EulerGerm/GermProductNonvanishingAboveThreeFifths
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime 2 and the golden germ product are nonzero when Re s is at least 3/5. -/

import Mathlib
import D5.S3.Analytic.EulerGerm.GermProductNonvanishingAboveTwoThirds

/- Provenance: Native proof over pinned mathlib and frozen repository inputs. -/
/- SEARCH RECEIPT (2026-09-02):
   * Repository `D5/**/*.lean`, searched for `three_fifths`, `3 / 5`,
     `germLocalFactor`, and germ nonvanishing declarations. No theorem already
     moves the prime-2 or full-product boundary from `2 / 3` to `3 / 5`.
   * Reused frozen declarations from
     `GermProductNonvanishingAboveTwoThirds`: the odd-prime theorem on the full
     convergence half-plane and the prime-2 theorem above `2 / 3`.
   * Reused frozen convergence and product declarations:
     `germ_excited_norm_summable`, `germLocalFactor_eq_one_add`, and
     `germ_product_ne_zero_of_local_factors_ne_zero`.
   * Pinned mathlib supplies the exact real-power transport identities and
     geometric-series estimates used below. The strict endpoint inequalities
     are proved by raising to powers 5 and 25 and normalizing rational powers.

   This theorem advances only the explicit nonvanishing boundary furnished by
   the geometric tail majorant. It does not assert that the local factor has a
   zero below `3 / 5`, and it gives no O-5 or RH conclusion. -/

namespace D5.S3.Analytic.EulerGerm.GermProductNonvanishingAboveThreeFifths

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GermProductConvergence
open D5.S3.Analytic.EulerGerm.GermProductNonvanishing
open D5.S3.Analytic.EulerGerm.GermProductNonvanishingAboveTwoThirds

noncomputable section

private def excitedTail (s : ℂ) (p : ℕ) : ℂ :=
  ∑' v : ℕ, (p : ℂ) ^ (-s * (o5Beta (v + 1) : ℂ))

private theorem golden_sq_gt_thirteen_fifths :
    (13 / 5 : ℝ) < Real.goldenRatio ^ 2 := by
  rw [Real.goldenRatio_sq, Real.goldenRatio]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5),
    Real.sqrt_nonneg 5]

private theorem golden_convergence_lt_three_fifths :
    1 / Real.goldenRatio ^ 2 < (3 / 5 : ℝ) := by
  rw [div_lt_iff₀ (sq_pos_of_pos Real.goldenRatio_pos)]
  nlinarith [golden_sq_gt_thirteen_fifths]

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

private theorem two_rpow_neg_three_fifths_lt_thirty_three_fiftieths :
    (2 : ℝ) ^ (-(3 / 5 : ℝ)) < 33 / 50 := by
  rw [← Real.rpow_lt_rpow_iff (Real.rpow_nonneg (by norm_num) _)
    (by positivity : (0 : ℝ) ≤ 33 / 50) (by norm_num : (0 : ℝ) < 5)]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [Real.rpow_neg_natCast, Real.rpow_natCast]

private theorem two_rpow_neg_thirty_nine_twenty_fifths_lt_seventeen_fiftieths :
    (2 : ℝ) ^ (-(39 / 25 : ℝ)) < 17 / 50 := by
  rw [← Real.rpow_lt_rpow_iff (Real.rpow_nonneg (by norm_num) _)
    (by positivity : (0 : ℝ) ≤ 17 / 50) (by norm_num : (0 : ℝ) < 25)]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [Real.rpow_neg_natCast, Real.rpow_natCast]

private theorem prime_two_endpoint_A_lt :
    (2 : ℝ) ^ (-(3 / 5 : ℝ) * Real.goldenRatio ^ 2) < 17 / 50 := by
  have hexponent :
      -(3 / 5 : ℝ) * Real.goldenRatio ^ 2 < -(39 / 25 : ℝ) := by
    nlinarith [golden_sq_gt_thirteen_fifths]
  calc
    (2 : ℝ) ^ (-(3 / 5 : ℝ) * Real.goldenRatio ^ 2) <
        (2 : ℝ) ^ (-(39 / 25 : ℝ)) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexponent
    _ < 17 / 50 :=
      two_rpow_neg_thirty_nine_twenty_fifths_lt_seventeen_fiftieths

private theorem prime_two_endpoint_small :
    (2 : ℝ) ^ (-(3 / 5 : ℝ) * Real.goldenRatio ^ 2) +
      (2 : ℝ) ^ (-(3 / 5 : ℝ)) < 1 := by
  linarith [prime_two_endpoint_A_lt,
    two_rpow_neg_three_fifths_lt_thirty_three_fiftieths]

private theorem prime_two_small_of_re_ge (s : ℂ)
    (hs : (3 / 5 : ℝ) ≤ s.re) :
    (2 : ℝ) ^ (-s.re * Real.goldenRatio ^ 2) +
      (2 : ℝ) ^ (-s.re) < 1 := by
  have hAexp :
      -s.re * Real.goldenRatio ^ 2 ≤
        -(3 / 5 : ℝ) * Real.goldenRatio ^ 2 := by
    nlinarith [sq_pos_of_pos Real.goldenRatio_pos]
  have hqexp : -s.re ≤ -(3 / 5 : ℝ) := by
    linarith
  calc
    (2 : ℝ) ^ (-s.re * Real.goldenRatio ^ 2) +
        (2 : ℝ) ^ (-s.re) ≤
      (2 : ℝ) ^ (-(3 / 5 : ℝ) * Real.goldenRatio ^ 2) +
        (2 : ℝ) ^ (-(3 / 5 : ℝ)) :=
      add_le_add
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hAexp)
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hqexp)
    _ < 1 := prime_two_endpoint_small

private theorem excited_term_norm_le_geometric (s : ℂ)
    (hs : 1 / Real.goldenRatio ^ 2 < s.re) (p : Nat.Primes) (v : ℕ) :
    ‖(p : ℂ) ^ (-s * (o5Beta (v + 1) : ℂ))‖ ≤
      (p : ℝ) ^ (-s.re * Real.goldenRatio ^ 2) *
        ((p : ℝ) ^ (-s.re)) ^ v := by
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

private theorem excited_tail_norm_lt_one (s : ℂ)
    (hs : 1 / Real.goldenRatio ^ 2 < s.re) (p : Nat.Primes)
    (hsmall :
      (p : ℝ) ^ (-s.re * Real.goldenRatio ^ 2) +
        (p : ℝ) ^ (-s.re) < 1) :
    ‖excitedTail s p‖ < 1 := by
  let A : ℝ := (p : ℝ) ^ (-s.re * Real.goldenRatio ^ 2)
  let q : ℝ := (p : ℝ) ^ (-s.re)
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  have hqnonneg : 0 ≤ q :=
    Real.rpow_nonneg (by exact_mod_cast p.prop.pos.le) _
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

/-- The prime-2 golden local factor is nonzero on `Re s >= 3/5`. -/
theorem germ_local_factor_two_ne_zero_of_re_ge_three_fifths
    (s : ℂ) (hs : (3 / 5 : ℝ) ≤ s.re) :
    germLocalFactor s (⟨2, Nat.prime_two⟩ : Nat.Primes) ≠ 0 := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  fail_if_success (solve | trivial)
  by_cases htwo_thirds : (2 / 3 : ℝ) ≤ s.re
  · exact germ_local_factor_two_ne_zero_of_re_ge_two_thirds s htwo_thirds
  · let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hconv : 1 / Real.goldenRatio ^ 2 < s.re :=
      golden_convergence_lt_three_fifths.trans_le hs
    apply local_factor_ne_zero_of_tail_norm_lt_one s hconv p
    apply excited_tail_norm_lt_one s hconv p
    change (2 : ℝ) ^ (-s.re * Real.goldenRatio ^ 2) +
      (2 : ℝ) ^ (-s.re) < 1
    exact prime_two_small_of_re_ge s hs

private theorem endpoint_half_plane_numeric_check :
    (3 / 5 : ℝ) ≤ (((3 / 5 : ℝ) : ℂ)).re := by
  norm_num

private theorem three_fifths_lt_two_thirds_numeric_check :
    (3 / 5 : ℝ) < 2 / 3 := by
  norm_num

private theorem endpoint_prime_two_nonzero_numeric_check :
    germLocalFactor (((3 / 5 : ℝ) : ℂ))
      (⟨2, Nat.prime_two⟩ : Nat.Primes) ≠ 0 :=
  germ_local_factor_two_ne_zero_of_re_ge_three_fifths
    ((3 / 5 : ℝ) : ℂ) endpoint_half_plane_numeric_check

/-- The golden Euler product is nonzero on the half-plane `Re s >= 3/5`. -/
theorem germ_product_ne_zero_of_re_ge_three_fifths
    (s : ℂ) (hs : (3 / 5 : ℝ) ≤ s.re) :
    (∏' p : Nat.Primes, germLocalFactor s p) ≠ 0 := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  fail_if_success (solve | trivial)
  have hconv : 1 / Real.goldenRatio ^ 2 < s.re :=
    golden_convergence_lt_three_fifths.trans_le hs
  apply germ_product_ne_zero_of_local_factors_ne_zero s hconv
  intro p
  by_cases hp : (p : ℕ) = 2
  · have hp_eq : p = (⟨2, Nat.prime_two⟩ : Nat.Primes) :=
      Nat.Primes.coe_nat_injective hp
    rw [hp_eq]
    exact germ_local_factor_two_ne_zero_of_re_ge_three_fifths s hs
  · exact germ_local_factor_ne_zero_of_prime_ne_two s hconv p hp

#print axioms germ_product_ne_zero_of_re_ge_three_fifths

end

end D5.S3.Analytic.EulerGerm.GermProductNonvanishingAboveThreeFifths
