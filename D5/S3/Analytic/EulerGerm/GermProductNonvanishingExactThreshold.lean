/- GID: D5/S3/Analytic/EulerGerm/GermProductNonvanishingExactThreshold
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The exact prime-two majorant threshold and zero-free half-plane above it. -/

import Mathlib
import D5.S3.Analytic.EulerGerm.GermProductNonvanishingAboveThreeFifths

/- Provenance: Native proof over pinned mathlib and frozen repository inputs. -/
/- SEARCH RECEIPT (2026-09-03):
   * Repository `D5/**/*.lean` was searched for the exact-threshold statement,
     `three_fifths`, `3 / 5`, prime-local nonvanishing, and product
     nonvanishing. No prior declaration defines this threshold or proves its
     half-plane conclusion.
   * The frozen three-fifths module was read in full. It exports only its
     endpoint local-factor and product theorems; its generic tail estimate is
     private. This module therefore rebuilds the parameterized geometric-tail
     argument under the explicit hypothesis `primeTwoMajorant sigma < 1`, and
     reuses the exported endpoint theorem on the `Re s >= 3/5` branch.
   * Frozen public inputs used below are `o5_beta_growth`,
     `germ_excited_norm_summable`, `germLocalFactor_eq_one_add`,
     `germ_local_factor_ne_zero_of_prime_ne_two`,
     `germ_local_factor_two_ne_zero_of_re_ge_three_fifths`, and
     `germ_product_ne_zero_of_local_factors_ne_zero`.
   * Pinned mathlib supplies continuity and monotonicity of real powers,
     `intermediate_value_Icc'`, geometric-series summation, and the norm bound
     for a convergent complex `tsum`.

   `primeTwoThreshold` is the exact threshold of this explicit prime-2
   majorant method. No claim is made that it is the actual boundary of the
   local zero set, and no O-5 or RH conclusion is asserted. -/

namespace D5.S3.Analytic.EulerGerm.GermProductNonvanishingExactThreshold

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set
open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GermProductConvergence
open D5.S3.Analytic.EulerGerm.GermProductNonvanishing
open D5.S3.Analytic.EulerGerm.GermProductNonvanishingAboveTwoThirds
open D5.S3.Analytic.EulerGerm.GermProductNonvanishingAboveThreeFifths

noncomputable section

/-- The two-term majorant governing the prime-2 geometric-tail argument. -/
noncomputable def primeTwoMajorant (sigma : ℝ) : ℝ :=
  (2 : ℝ) ^ (-sigma * Real.goldenRatio ^ 2) + (2 : ℝ) ^ (-sigma)

theorem prime_two_majorant_continuous : Continuous primeTwoMajorant := by
  unfold primeTwoMajorant
  exact
    ((Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).comp
      (continuous_id.neg.mul continuous_const)).add
      ((Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).comp
        continuous_id.neg)

theorem prime_two_majorant_strictAnti : StrictAnti primeTwoMajorant := by
  intro x y hxy
  unfold primeTwoMajorant
  apply add_lt_add
  · apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    nlinarith [sq_pos_of_pos Real.goldenRatio_pos]
  · apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    linarith

private theorem golden_convergence_pos :
    0 < 1 / Real.goldenRatio ^ 2 := by
  positivity

private theorem golden_convergence_lt_one :
    1 / Real.goldenRatio ^ 2 < (1 : ℝ) := by
  rw [div_lt_iff₀ (sq_pos_of_pos Real.goldenRatio_pos)]
  nlinarith [Real.one_lt_goldenRatio, Real.goldenRatio_pos]

private theorem golden_sq_gt_thirteen_fifths :
    (13 / 5 : ℝ) < Real.goldenRatio ^ 2 := by
  rw [Real.goldenRatio_sq, Real.goldenRatio]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5),
    Real.sqrt_nonneg 5]

private theorem golden_convergence_lt_three_fifths :
    1 / Real.goldenRatio ^ 2 < (3 / 5 : ℝ) := by
  rw [div_lt_iff₀ (sq_pos_of_pos Real.goldenRatio_pos)]
  nlinarith [golden_sq_gt_thirteen_fifths]

private theorem prime_two_majorant_left_gt_one :
    1 < primeTwoMajorant (1 / Real.goldenRatio ^ 2) := by
  have hsq_ne : Real.goldenRatio ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos Real.goldenRatio_pos)
  have hexponent :
      -(1 / Real.goldenRatio ^ 2) * Real.goldenRatio ^ 2 = (-1 : ℝ) := by
    field_simp
  have hfirst :
      (2 : ℝ) ^ (-(1 / Real.goldenRatio ^ 2) * Real.goldenRatio ^ 2) =
        1 / 2 := by
    rw [hexponent, Real.rpow_neg_one]
    norm_num
  have hsecond :
      (1 / 2 : ℝ) < (2 : ℝ) ^ (-(1 / Real.goldenRatio ^ 2)) := by
    calc
      (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by
        norm_num [Real.rpow_neg_one]
      _ < (2 : ℝ) ^ (-(1 / Real.goldenRatio ^ 2)) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
          (by linarith [golden_convergence_lt_one])
  rw [primeTwoMajorant, hfirst]
  linarith

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

private theorem prime_two_majorant_right_lt_one :
    primeTwoMajorant (3 / 5) < 1 := by
  have hexponent :
      -(3 / 5 : ℝ) * Real.goldenRatio ^ 2 < -(39 / 25 : ℝ) := by
    nlinarith [golden_sq_gt_thirteen_fifths]
  have hA :
      (2 : ℝ) ^ (-(3 / 5 : ℝ) * Real.goldenRatio ^ 2) < 17 / 50 :=
    (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexponent).trans
      two_rpow_neg_thirty_nine_twenty_fifths_lt_seventeen_fiftieths
  rw [primeTwoMajorant]
  linarith [hA, two_rpow_neg_three_fifths_lt_thirty_three_fiftieths]

private theorem prime_two_threshold_exists_unique :
    ∃! sigma : ℝ,
      sigma ∈ Ioo (1 / Real.goldenRatio ^ 2) (3 / 5) ∧
        primeTwoMajorant sigma = 1 := by
  have hab : (1 / Real.goldenRatio ^ 2 : ℝ) ≤ 3 / 5 :=
    golden_convergence_lt_three_fifths.le
  have hone : (1 : ℝ) ∈
      Icc (primeTwoMajorant (3 / 5))
        (primeTwoMajorant (1 / Real.goldenRatio ^ 2)) :=
    ⟨prime_two_majorant_right_lt_one.le,
      prime_two_majorant_left_gt_one.le⟩
  obtain ⟨sigma, hsigma, heq⟩ :=
    intermediate_value_Icc' hab prime_two_majorant_continuous.continuousOn hone
  have hleft : 1 / Real.goldenRatio ^ 2 < sigma := by
    rcases lt_or_eq_of_le hsigma.1 with h | h
    · exact h
    · subst sigma
      linarith [prime_two_majorant_left_gt_one]
  have hright : sigma < (3 / 5 : ℝ) := by
    rcases lt_or_eq_of_le hsigma.2 with h | h
    · exact h
    · subst sigma
      linarith [prime_two_majorant_right_lt_one]
  refine ⟨sigma, ⟨⟨hleft, hright⟩, heq⟩, ?_⟩
  intro tau htau
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := prime_two_majorant_strictAnti hlt
    rw [htau.2, heq] at h
    exact (lt_irrefl 1 h)
  · have h := prime_two_majorant_strictAnti hgt
    rw [htau.2, heq] at h
    exact (lt_irrefl 1 h)

/-- The unique root of the prime-2 majorant inside the certified interval. -/
noncomputable def primeTwoThreshold : ℝ :=
  Classical.choose prime_two_threshold_exists_unique

private theorem prime_two_threshold_spec :
    primeTwoThreshold ∈ Ioo (1 / Real.goldenRatio ^ 2) (3 / 5) ∧
      primeTwoMajorant primeTwoThreshold = 1 :=
  (Classical.choose_spec prime_two_threshold_exists_unique).1

private theorem prime_two_threshold_unique (sigma : ℝ)
    (hsigma : sigma ∈ Ioo (1 / Real.goldenRatio ^ 2) (3 / 5) ∧
      primeTwoMajorant sigma = 1) :
    sigma = primeTwoThreshold :=
  (Classical.choose_spec prime_two_threshold_exists_unique).2 sigma hsigma

private def excitedTail (s : ℂ) (p : ℕ) : ℂ :=
  ∑' v : ℕ, (p : ℂ) ^ (-s * (o5Beta (v + 1) : ℂ))

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

private theorem excited_term_norm_le_geometric (s : ℂ)
    (hs : 1 / Real.goldenRatio ^ 2 < s.re) (p : Nat.Primes) (v : ℕ) :
    ‖(p : ℂ) ^ (-s * (o5Beta (v + 1) : ℂ))‖ ≤
      (p : ℝ) ^ (-s.re * Real.goldenRatio ^ 2) *
        ((p : ℝ) ^ (-s.re)) ^ v := by
  have hspos : 0 < s.re := golden_convergence_pos.trans hs
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
  have hspos : 0 < s.re := golden_convergence_pos.trans hs
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

/-- The prime-2 local factor is nonzero strictly above the exact majorant
threshold. -/
theorem germ_local_factor_two_ne_zero_above_prime_two_threshold
    (s : ℂ) (hs : primeTwoThreshold < s.re) :
    germLocalFactor s (⟨2, Nat.prime_two⟩ : Nat.Primes) ≠ 0 := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  fail_if_success (solve | trivial)
  by_cases hthree_fifths : (3 / 5 : ℝ) ≤ s.re
  · exact germ_local_factor_two_ne_zero_of_re_ge_three_fifths
      s hthree_fifths
  · let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hconv : 1 / Real.goldenRatio ^ 2 < s.re :=
      prime_two_threshold_spec.1.1.trans hs
    apply local_factor_ne_zero_of_tail_norm_lt_one s hconv p
    apply excited_tail_norm_lt_one s hconv p
    change primeTwoMajorant s.re < 1
    have hanti := prime_two_majorant_strictAnti hs
    rw [prime_two_threshold_spec.2] at hanti
    exact hanti

/-- The full golden Euler product is nonzero strictly above the exact prime-2
majorant threshold. -/
theorem germ_product_ne_zero_above_prime_two_threshold
    (s : ℂ) (hs : primeTwoThreshold < s.re) :
    (∏' p : Nat.Primes, germLocalFactor s p) ≠ 0 := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  fail_if_success (solve | trivial)
  have hconv : 1 / Real.goldenRatio ^ 2 < s.re :=
    prime_two_threshold_spec.1.1.trans hs
  apply germ_product_ne_zero_of_local_factors_ne_zero s hconv
  intro p
  by_cases hp : (p : ℕ) = 2
  · have hp_eq : p = (⟨2, Nat.prime_two⟩ : Nat.Primes) :=
      Nat.Primes.coe_nat_injective hp
    rw [hp_eq]
    exact germ_local_factor_two_ne_zero_above_prime_two_threshold s hs
  · exact germ_local_factor_ne_zero_of_prime_ne_two s hconv p hp

private theorem endpoint_prime_two_nonzero_numeric_check :
    germLocalFactor (((3 / 5 : ℝ) : ℂ))
      (⟨2, Nat.prime_two⟩ : Nat.Primes) ≠ 0 := by
  apply germ_local_factor_two_ne_zero_above_prime_two_threshold
  simpa using prime_two_threshold_spec.1.2

/-- The majorant is continuous and strictly decreasing on the positive ray,
its unique unit crossing lies in `(1 / phi^2, 3/5)`, and both the prime-2
factor and the full golden Euler product are zero-free above that crossing. -/
theorem germ_product_nonvanishing_exact_threshold :
    ContinuousOn primeTwoMajorant (Ioi 0) ∧
      StrictAntiOn primeTwoMajorant (Ioi 0) ∧
      (primeTwoThreshold ∈ Ioo (1 / Real.goldenRatio ^ 2) (3 / 5) ∧
        primeTwoMajorant primeTwoThreshold = 1 ∧
        ∀ sigma : ℝ,
          sigma ∈ Ioo (1 / Real.goldenRatio ^ 2) (3 / 5) →
          primeTwoMajorant sigma = 1 → sigma = primeTwoThreshold) ∧
      (∀ s : ℂ, primeTwoThreshold < s.re →
        germLocalFactor s (⟨2, Nat.prime_two⟩ : Nat.Primes) ≠ 0) ∧
      (∀ s : ℂ, primeTwoThreshold < s.re →
        (∏' p : Nat.Primes, germLocalFactor s p) ≠ 0) := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  fail_if_success (solve | trivial)
  refine ⟨prime_two_majorant_continuous.continuousOn,
    fun _ _ _ _ hxy => prime_two_majorant_strictAnti hxy,
    ?_, germ_local_factor_two_ne_zero_above_prime_two_threshold,
    germ_product_ne_zero_above_prime_two_threshold⟩
  exact ⟨prime_two_threshold_spec.1, prime_two_threshold_spec.2,
    fun sigma hmem heq => prime_two_threshold_unique sigma ⟨hmem, heq⟩⟩

#print axioms germ_product_nonvanishing_exact_threshold

end

end D5.S3.Analytic.EulerGerm.GermProductNonvanishingExactThreshold
