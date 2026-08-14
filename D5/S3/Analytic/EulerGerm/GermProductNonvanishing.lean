/- GID: D5/S3/Analytic/EulerGerm/GermProductNonvanishing
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden Euler germ nonvanishing, conditionally and for Re s at least one. -/

import Mathlib
import D5.S3.Analytic.EulerGerm.GermProductConvergence

/- Provenance: Native proof over pinned mathlib. -/
/- OPEN NOTE: This file does not decide whether a golden local factor can vanish
   in the strip

     1 / Real.goldenRatio ^ 2 < Re s < 1.

   Consequently it does not assert unconditional nonvanishing of the germ
   product on that strip.  The direct tail estimate

     p ^ (-sigma * Real.goldenRatio ^ 2) / (1 - p ^ (-sigma))

   cannot settle the question near the convergence boundary: for p = 2 and
   sigma decreasing to 1 / Real.goldenRatio ^ 2 (approximately 0.382), its
   numerator approaches 2 ^ (-1) = 0.5, while the reciprocal denominator is
   approximately 4.3, giving approximately 2.15 > 1.  Thus the norm-less-than-
   one argument used below genuinely fails there; this is a specific failure
   of that bound, not evidence that a local zero does or does not exist. -/
/- SEARCH RECEIPT (2026-08-15):
   * Repository D5 tree, semantic searches `zero-free`, `zeroFree`,
     `nonvanishing`, `non-vanishing`, `EulerProduct`, `Euler product`, `tprod`,
     `germ.*ne_zero`, `localFactor.*ne_zero`, and `tprod.*ne_zero`: no existing
     theorem states nonvanishing of `germLocalFactor` or its prime `tprod`.
   * `D5/S3/Weil/EulerProduct.lean`: hit
     `finite_euler_zero_free_and_pole_locus`, for a finite classical Euler
     window and its denominator lattice.  It is not a golden germ result.
   * `D5/S3/Weil/ZetaCore/Statement.lean`: hit `IsNontrivialZero`, the zeta
     zero-counting definitions, and `ZetaSeam`; these concern `riemannZeta`,
     not the golden germ.
   * `D5/S3/Weil/ZetaAnalytic/RectangleLogDeriv.lean`: hit
     `finite_zeros_rectangle`, whose nonvanishing hypothesis is a single
     interior point `x` of the rectangle with `f x != 0`, and
     `rectangleIntegral'_mul_logDeriv_of_poles` and
     `rectangleIntegral'_mul_logDeriv`, whose hypothesis is pointwise
     nonvanishing on the rectangle border.  All three are generic analytic
     tools taking nonvanishing as an assumption; none concludes nonvanishing
     of this local factor.
   * Every file under `D5/S3/Weil/ZetaExplicit/` was searched by declaration
     and by `zero-free`/`nonvanishing`.  The relevant hits are the zeta good-
     height, completed-zeta horizontal, Landau, contour, and explicit-formula
     declarations (`good_heights`, `completedZeta_ne_zero_on_horizontals`,
     `zeta_logDeriv_partial_fraction`, `rectangle_identity`, and
     `EF_lit_zeta`).  They concern `riemannZeta` or `completedRiemannZeta`; none
     states a golden-germ local or infinite-product nonvanishing result.
   * Reused repository declarations, each actually invoked below:
     `germ_excited_norm_summable` and `germLocalFactor_eq_one_add` from
     `GermProductConvergence.lean`, plus `o5_beta_growth`, `germLocalFactor`,
     and the golden-ratio facts already imported through that module.
     `germLocalFactor_multipliable` is available through the same import but is
     **not** invoked here: multipliability is supplied inside mathlib's
     `tprod_one_add_ne_zero_of_summable` from the summability hypothesis.  No
     convergence or local-factor definition is reproved here.
   * Pinned mathlib `Analysis/SpecialFunctions/Log/Summable.lean`: exact hit
     `tprod_one_add_ne_zero_of_summable [CompleteSpace R] [NormMulClass R]
     (hf : forall i, 1 + f i != 0) (hu : Summable (norm f))`.  It is applied
     directly below.  Its proof uses the separately inspected existing facts
     `Multipliable.norm_tprod` from
     `Topology/Algebra/InfiniteSum/Field.lean` and
     `Real.rexp_tsum_eq_tprod` from the same Summable file; this file does not
     duplicate either argument.
   * Pinned mathlib also supplied `Complex.norm_natCast_cpow_of_pos`,
     `Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos`,
     `Real.rpow_le_rpow_of_nonpos`, `summable_geometric_two'`,
     `tsum_geometric_two'`, `norm_tsum_le_tsum_norm`, and
     `Summable.tsum_le_tsum`; all quantitative product and tail steps below use
     these library declarations. -/

namespace D5.S3.Analytic.EulerGerm.GermProductNonvanishing

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GermProductConvergence

noncomputable section

private def excitedTail (s : ℂ) (p : ℕ) : ℂ :=
  ∑' v : ℕ, (p : ℂ) ^ (-s * (o5Beta (v + 1) : ℂ))

private theorem convergence_of_re_ge_one {s : ℂ} (hs : 1 ≤ s.re) :
    1 / Real.goldenRatio ^ 2 < s.re := by
  apply lt_of_lt_of_le _ hs
  rw [div_lt_iff₀ (sq_pos_of_pos Real.goldenRatio_pos)]
  nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]

private theorem excited_tail_norm_summable (s : ℂ)
    (hs : 1 / Real.goldenRatio ^ 2 < s.re) :
    Summable (fun p : Nat.Primes => ‖excitedTail s p‖) := by
  let excited : Nat.Primes × ℕ → ℂ := fun q =>
    (q.1 : ℂ) ^ (-s * (o5Beta (q.2 + 1) : ℂ))
  have hnorm : Summable (fun q : Nat.Primes × ℕ => ‖excited q‖) := by
    simpa [excited] using germ_excited_norm_summable s hs
  refine hnorm.prod.of_nonneg_of_le (fun _ => norm_nonneg _) fun p => ?_
  simpa [excitedTail, excited] using
    norm_tsum_le_tsum_norm (hnorm.prod_factor p)

/-- If every prime-local golden factor is nonzero, absolute convergence of the
excited tails makes the full golden Euler product nonzero. -/
theorem germ_product_ne_zero_of_local_factors_ne_zero
    (s : ℂ) (hs : 1 / Real.goldenRatio ^ 2 < s.re)
    (hloc : ∀ p : Nat.Primes, germLocalFactor s p ≠ 0) :
    (∏' p : Nat.Primes, germLocalFactor s p) ≠ 0 := by
  have hfactor : ∀ p : Nat.Primes,
      germLocalFactor s p = 1 + excitedTail s p := fun p => by
    simpa [excitedTail] using
      germLocalFactor_eq_one_add s p p.prop hs
  rw [show (fun p : Nat.Primes => germLocalFactor s p) =
      (fun p : Nat.Primes => 1 + excitedTail s p) by
    funext p
    exact hfactor p]
  exact tprod_one_add_ne_zero_of_summable
    (fun p => by simpa [← hfactor p] using hloc p)
    (excited_tail_norm_summable s hs)

private theorem o5_beta_one_ge_two : (2 : ℝ) ≤ o5Beta 1 := by
  have hsqrt : (2 : ℝ) < Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5),
      Real.sqrt_nonneg 5]
  have hphi : (3 : ℝ) / 2 < Real.goldenRatio := by
    rw [Real.goldenRatio]
    linarith
  have hfloor : ⌊(2 : ℝ) * Real.goldenRatio⌋ = (3 : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · norm_num
      linarith
    · norm_num
      nlinarith [Real.goldenRatio_lt_two]
  rw [o5Beta]
  norm_num [hfloor]
  exact Real.one_lt_goldenRatio.le

private theorem o5_beta_succ_ge_add_two (v : ℕ) :
    (v : ℝ) + 2 ≤ o5Beta (v + 1) := by
  cases v with
  | zero => simpa using o5_beta_one_ge_two
  | succ v =>
      have hsqrt : (2 : ℝ) ≤ Real.sqrt 5 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5),
          Real.sqrt_nonneg 5]
      have hmul :
          2 * ((v + 2 : ℕ) : ℝ) ≤
            Real.sqrt 5 * ((v + 2 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hsqrt (by positivity)
      have hinv : 0 < 1 / Real.goldenRatio := by positivity
      have hv : 0 ≤ (v : ℝ) := by positivity
      calc
        ((v + 1 : ℕ) : ℝ) + 2 ≤
            Real.sqrt 5 * ((v + 2 : ℕ) : ℝ) +
              1 / Real.goldenRatio - 1 := by
          push_cast
          nlinarith
        _ ≤ o5Beta (v + 2) := o5_beta_growth (v + 2)

private theorem excited_term_norm_le_geometric (s : ℂ) (hs : 1 ≤ s.re)
    (p : Nat.Primes) (v : ℕ) :
    ‖(p : ℂ) ^ (-s * (o5Beta (v + 1) : ℂ))‖ ≤
      (1 / 2 : ℝ) / 2 / 2 ^ v := by
  have hbeta := o5_beta_succ_ge_add_two v
  have hbeta_nonneg : 0 ≤ o5Beta (v + 1) :=
    (by positivity : (0 : ℝ) ≤ (v : ℝ) + 2).trans hbeta
  have hproduct : (v : ℝ) + 2 ≤ s.re * o5Beta (v + 1) :=
    hbeta.trans (by simpa using mul_le_mul_of_nonneg_right hs hbeta_nonneg)
  have hexponent :
      (-s * (o5Beta (v + 1) : ℂ)).re ≤
        (-(((v + 2 : ℕ) : ℝ) : ℂ)).re := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    push_cast
    linarith
  calc
    ‖(p : ℂ) ^ (-s * (o5Beta (v + 1) : ℂ))‖ ≤
        ‖(p : ℂ) ^ (-(((v + 2 : ℕ) : ℝ) : ℂ))‖ :=
      Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos p.prop.pos hexponent
    _ = (p : ℝ) ^ (-((v + 2 : ℕ) : ℝ)) := by
      rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
      simp
    _ ≤ (2 : ℝ) ^ (-((v + 2 : ℕ) : ℝ)) := by
      exact Real.rpow_le_rpow_of_nonpos zero_lt_two
        (by exact_mod_cast p.prop.two_le)
        (neg_nonpos.mpr (Nat.cast_nonneg (v + 2)))
    _ = (1 / 2 : ℝ) / 2 / 2 ^ v := by
      rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]
      norm_num [pow_add, one_div_pow, div_eq_mul_inv, inv_pow, mul_comm]

private theorem excited_tail_norm_lt_one (s : ℂ) (hs : 1 ≤ s.re)
    (p : Nat.Primes) : ‖excitedTail s p‖ < 1 := by
  have hconv := convergence_of_re_ge_one hs
  have hnorm : Summable (fun v : ℕ =>
      ‖(p : ℂ) ^ (-s * (o5Beta (v + 1) : ℂ))‖) :=
    (germ_excited_norm_summable s hconv).prod_factor p
  calc
    ‖excitedTail s p‖ ≤
        ∑' v : ℕ, ‖(p : ℂ) ^ (-s * (o5Beta (v + 1) : ℂ))‖ := by
      exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' v : ℕ, (1 / 2 : ℝ) / 2 / 2 ^ v :=
      hnorm.tsum_le_tsum (excited_term_norm_le_geometric s hs p)
        (summable_geometric_two' (1 / 2))
    _ = 1 / 2 := tsum_geometric_two' (1 / 2)
    _ < 1 := by norm_num

/-- Every prime-local golden factor is nonzero on the explicit half-plane
`Re s ≥ 1`. -/
theorem germ_local_factor_ne_zero_of_re_ge (s : ℂ) (hs : 1 ≤ s.re)
    (p : Nat.Primes) : germLocalFactor s p ≠ 0 := by
  rw [germLocalFactor_eq_one_add s p p.prop (convergence_of_re_ge_one hs)]
  change 1 + excitedTail s p ≠ 0
  intro hzero
  have htail : excitedTail s p = -1 := by
    linear_combination hzero
  have hlt := excited_tail_norm_lt_one s hs p
  rw [htail, norm_neg, norm_one] at hlt
  exact lt_irrefl 1 hlt

/-- The golden Euler product is unconditionally nonzero on the explicit
half-plane `Re s ≥ 1`. -/
theorem germ_product_ne_zero_of_re_ge (s : ℂ) (hs : 1 ≤ s.re) :
    (∏' p : Nat.Primes, germLocalFactor s p) ≠ 0 :=
  germ_product_ne_zero_of_local_factors_ne_zero s
    (convergence_of_re_ge_one hs)
    (germ_local_factor_ne_zero_of_re_ge s hs)

end

end D5.S3.Analytic.EulerGerm.GermProductNonvanishing
