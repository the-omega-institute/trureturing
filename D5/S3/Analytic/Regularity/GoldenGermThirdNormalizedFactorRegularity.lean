/- GID: D5/S3/Analytic/Regularity/GoldenGermThirdNormalizedFactorRegularity
   generality: I
   mirror-B: D5/B/S3/Analytic/Regularity/GoldenGermThirdNormalizedFactorRegularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The third normalized golden germ is regular above one over phi to the fifth. -/

import D5.S3.Analytic.Regularity.GoldenGermThirdNormalizedFactorMajorant
import D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderFactorization
import D5.S3.Analytic.EulerGerm.GermProductNonvanishingAboveThreeFifths
import D5.S3.Analytic.EulerGerm.LocalFactorZeroDivisor

/- Library-search audit trail (2026-09-03):
   * The sibling majorant module supplies the summable uniform bound, local
     factor differentiability, and locally uniform prime-product convergence.
   * Frozen factorization and nonvanishing theorems supply pointwise deviation
     summability and the established complex zero-free half-plane.
   * Pinned Mathlib supplies locally uniform differentiation, `tsum_pos`, and
     `tprod_one_add_ne_zero_of_summable`. No stronger regularity theorem exists. -/

namespace D5.S3.Analytic.Regularity.GoldenGermThirdNormalizedFactorRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderFactorization
open D5.S3.Analytic.EulerGerm.GermProductNonvanishingAboveThreeFifths
open D5.S3.Analytic.EulerGerm.LocalFactorZeroDivisor
open D5.S3.Analytic.Regularity.GoldenGermThirdNormalizedFactorMajorant

noncomputable section

private theorem mixed_mode_cpow (s : Complex) (p : Nat.Primes) (a b : Nat) :
    (p : Complex) ^ (-s * ((((a : Real) * Real.goldenRatio ^ 2 +
      (b : Real) * Real.goldenRatio ^ 3) : Real) : Complex)) =
    ((p : Complex) ^ (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ a *
    ((p : Complex) ^ (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ b := by
  have hbase : (p : Complex) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  have hexponent :
      -s * ((((a : Real) * Real.goldenRatio ^ 2 +
        (b : Real) * Real.goldenRatio ^ 3) : Real) : Complex) =
      (a : Complex) * (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)) +
      (b : Complex) * (-s * ((Real.goldenRatio ^ 3 : Real) : Complex)) := by
    push_cast
    ring
  rw [hexponent, Complex.cpow_add _ _ hbase]
  exact congrArg₂ (fun z w : Complex => z * w)
    (Complex.cpow_nat_mul (p : Complex) a
      (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))
    (Complex.cpow_nat_mul (p : Complex) b
      (-s * ((Real.goldenRatio ^ 3 : Real) : Complex)))

private theorem mixed_mode_norm_lt_one (s : Complex) (hs : 0 < s.re)
    (p : Nat.Primes) (a b : Nat)
    (hweight : 0 < (a : Real) * Real.goldenRatio ^ 2 +
      (b : Real) * Real.goldenRatio ^ 3) :
    ‖((p : Complex) ^ (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ a *
     ((p : Complex) ^ (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ b‖ < 1 := by
  rw [← mixed_mode_cpow s p a b]
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast p.prop.one_lt) (by nlinarith)

private theorem third_normalized_local_factor_ne_zero_iff (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 5 < s.re) (p : Nat.Primes) :
    (let x := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor s p ≠ 0) ↔
      germLocalFactor s p ≠ 0 := by
  dsimp only
  let x : Complex := (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
  let y : Complex := (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  have hlt (a b : Nat) (hweight : 0 < (a : Real) * Real.goldenRatio ^ 2 +
      (b : Real) * Real.goldenRatio ^ 3) : ‖x ^ a * y ^ b‖ < 1 := by
    simpa [x, y] using mixed_mode_norm_lt_one s hspos p a b hweight
  have hySquare : 1 - y ^ 2 ≠ 0 := by
    rw [sub_ne_zero]
    intro heq
    have h : ‖y ^ 2‖ < 1 := by simpa using hlt 0 2 (by positivity)
    rw [← heq, norm_one] at h
    exact lt_irrefl 1 h
  have hxy : 1 - x ^ 2 * y ≠ 0 := by
    rw [sub_ne_zero]
    intro heq
    have h := hlt 2 1 (by positivity)
    rw [pow_one, ← heq, norm_one] at h
    exact lt_irrefl 1 h
  have hy : 1 - y ≠ 0 := by
    rw [sub_ne_zero]
    intro heq
    have h : ‖y‖ < 1 := by simpa using hlt 0 1 (by positivity)
    rw [← heq, norm_one] at h
    exact lt_irrefl 1 h
  have hx : 1 + x ≠ 0 := by
    intro hzero
    have heq : x = -1 := by linear_combination hzero
    have h := hlt 1 0 (by positivity)
    rw [pow_one, pow_zero, mul_one, heq, norm_neg, norm_one] at h
    exact lt_irrefl 1 h
  change ((1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
      (1 - y) * (1 + x)⁻¹ * germLocalFactor s p ≠ 0) ↔ _
  constructor
  · intro h hlocal
    apply h
    simp [hlocal]
  · intro hlocal
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero hySquare) hxy) hy)
        (inv_ne_zero hx)) hlocal

private theorem natCast_le_o5Beta (v : Nat) : (v : Real) <= o5Beta v := by
  cases v with
  | zero => simp [o5_beta_zero]
  | succ v =>
      have hgrowth := o5_beta_growth (v + 1)
      have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
        Real.sq_sqrt (by norm_num)
      have hsqrt_nonneg : 0 <= Real.sqrt 5 := Real.sqrt_nonneg 5
      have hsqrt_two : 2 < Real.sqrt 5 := by nlinarith
      have hinv_pos : 0 < 1 / Real.goldenRatio :=
        one_div_pos.mpr Real.goldenRatio_pos
      push_cast at hgrowth ⊢
      nlinarith

private theorem real_local_factor_summable (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 5 < sigma) (p : Nat.Primes) :
    Summable (fun v : Nat => (p : Real) ^ (-sigma * o5Beta v)) := by
  have hsigma_pos : 0 < sigma := lt_trans (by positivity) hsigma
  let q : Real := (p : Real) ^ (-sigma)
  have hp_pos : (0 : Real) < p := by exact_mod_cast p.prop.pos
  have hq_nonneg : 0 <= q := Real.rpow_nonneg hp_pos.le _
  have hq_lt_one : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast p.prop.one_lt) (neg_neg_of_pos hsigma_pos)
  have hgeom : Summable (fun v : Nat => q ^ v) :=
    summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_nonneg hq_nonneg]
      exact hq_lt_one)
  apply Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg hp_pos.le _)
    (fun v => ?_) hgeom
  calc
    (p : Real) ^ (-sigma * o5Beta v) <= (p : Real) ^ (-sigma * (v : Real)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.prop.one_lt.le)
        (by nlinarith [natCast_le_o5Beta v])
    _ = q ^ v := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp_pos.le]

private theorem real_local_factor_pos (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 5 < sigma) (p : Nat.Primes) :
    0 < ∑' v : Nat, (p : Real) ^ (-sigma * o5Beta v) := by
  refine (real_local_factor_summable sigma hsigma p).tsum_pos
    (fun _ => Real.rpow_nonneg (by positivity) _) 0 ?_
  simp [o5_beta_zero]

private theorem ofReal_real_local_factor_eq (sigma : Real) (p : Nat.Primes) :
    ((∑' v : Nat, (p : Real) ^ (-sigma * o5Beta v) : Real) : Complex) =
      germLocalFactor (sigma : Complex) p := by
  rw [germLocalFactor, Complex.ofReal_tsum]
  congr 1 with v
  rw [Complex.ofReal_cpow (by positivity)]
  congr 1
  norm_num

private theorem real_point_local_factor_ne_zero (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 5 < sigma) (p : Nat.Primes) :
    germLocalFactor (sigma : Complex) p ≠ 0 := by
  rw [← ofReal_real_local_factor_eq sigma p]
  exact_mod_cast (real_local_factor_pos sigma hsigma p).ne'

private theorem half_lt_three_fifths_numeric_check :
    (1 / 2 : Real) < 3 / 5 := by norm_num

private theorem fifth_threshold_lt_three_fifths :
    1 / Real.goldenRatio ^ 5 < (3 / 5 : Real) := by
  have htwo_lt_phi2 : (2 : Real) < Real.goldenRatio ^ 2 := by
    rw [Real.goldenRatio_sq]
    linarith [Real.one_lt_goldenRatio]
  have hphi2 : 0 < Real.goldenRatio ^ 2 := by positivity
  have hphi3 : 0 < Real.goldenRatio ^ 3 := by positivity
  have hphi4 : 0 < Real.goldenRatio ^ 4 := by positivity
  have hphi2_lt_phi3 : Real.goldenRatio ^ 2 < Real.goldenRatio ^ 3 := by
    calc
      Real.goldenRatio ^ 2 < Real.goldenRatio ^ 2 * Real.goldenRatio :=
        (lt_mul_iff_one_lt_right hphi2).mpr Real.one_lt_goldenRatio
      _ = Real.goldenRatio ^ 3 := by ring
  have hphi3_lt_phi4 : Real.goldenRatio ^ 3 < Real.goldenRatio ^ 4 := by
    calc
      Real.goldenRatio ^ 3 < Real.goldenRatio ^ 3 * Real.goldenRatio :=
        (lt_mul_iff_one_lt_right hphi3).mpr Real.one_lt_goldenRatio
      _ = Real.goldenRatio ^ 4 := by ring
  have hphi4_lt_phi5 : Real.goldenRatio ^ 4 < Real.goldenRatio ^ 5 := by
    calc
      Real.goldenRatio ^ 4 < Real.goldenRatio ^ 4 * Real.goldenRatio :=
        (lt_mul_iff_one_lt_right hphi4).mpr Real.one_lt_goldenRatio
      _ = Real.goldenRatio ^ 5 := by ring
  have htwo_lt_phi5 : (2 : Real) < Real.goldenRatio ^ 5 :=
    htwo_lt_phi2.trans (hphi2_lt_phi3.trans (hphi3_lt_phi4.trans hphi4_lt_phi5))
  exact (one_div_lt_one_div_of_lt (by norm_num) htwo_lt_phi5).trans
    half_lt_three_fifths_numeric_check

private theorem fifth_threshold_lt_fourth_threshold :
    1 / Real.goldenRatio ^ 5 < 1 / Real.goldenRatio ^ 4 := by
  have hphi4 : 0 < Real.goldenRatio ^ 4 := by positivity
  exact one_div_lt_one_div_of_lt hphi4 (by
    calc
      Real.goldenRatio ^ 4 < Real.goldenRatio ^ 4 * Real.goldenRatio :=
        (lt_mul_iff_one_lt_right hphi4).mpr Real.one_lt_goldenRatio
      _ = Real.goldenRatio ^ 5 := by ring)

/-- The third signed cancellation yields a locally uniform prime-product
M-test and holomorphy on `Re s > 1 / phi^5`. Complex nonvanishing is proved
on the frozen zero-free half-plane `Re s >= 3/5`; throughout the wider domain
the product is nonzero on the positive real axis, in particular at
`s = 1 / phi^4`, where it is also continuous. -/
theorem golden_germ_third_normalized_factor_regularity :
    let Kp : Complex -> Nat.Primes -> Complex := fun s p =>
      let x := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor s p
    let G3 : Complex -> Complex := fun s => ∏' p : Nat.Primes, Kp s p
    (∀ sigma : Real, 1 / Real.goldenRatio ^ 5 < sigma ->
      ∃ u : Nat.Primes -> Real, Summable u ∧
        ∀ p : Nat.Primes, ∀ s : Complex, sigma <= s.re ->
          ‖Kp s p - 1‖ <= u p) ∧
    AnalyticOnNhd Complex G3
      {s : Complex | 1 / Real.goldenRatio ^ 5 < s.re} ∧
    (∀ s : Complex, (3 / 5 : Real) <= s.re -> G3 s ≠ 0) ∧
    (∀ sigma : Real, 1 / Real.goldenRatio ^ 5 < sigma ->
      G3 (sigma : Complex) ≠ 0) ∧
    ContinuousAt G3 ((1 / Real.goldenRatio ^ 4 : Real) : Complex) ∧
    G3 ((1 / Real.goldenRatio ^ 4 : Real) : Complex) ≠ 0 := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  fail_if_success (solve | trivial)
  dsimp only
  let K : Set Complex := {s : Complex | 1 / Real.goldenRatio ^ 5 < s.re}
  have hK : IsOpen K := isOpen_lt continuous_const Complex.continuous_re
  have hmajorant : ∀ sigma : Real, 1 / Real.goldenRatio ^ 5 < sigma ->
      ∃ u : Nat.Primes -> Real, Summable u ∧
        ∀ p : Nat.Primes, ∀ s : Complex, sigma <= s.re ->
          ‖(let x := (p : Complex) ^
                (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
             let y := (p : Complex) ^
                (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
             (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) * (1 - y) * (1 + x)⁻¹ *
               germLocalFactor s p) - 1‖ <= u p := by
    intro sigma hsigma
    have h := golden_germ_third_normalized_factor_majorant sigma hsigma
    dsimp only at h
    exact h.1
  have hanalytic : AnalyticOnNhd Complex
      (fun s : Complex => ∏' p : Nat.Primes,
        let x := (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
        let y := (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
        (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
          (1 - y) * (1 + x)⁻¹ * germLocalFactor s p) K := by
    intro s hs
    change 1 / Real.goldenRatio ^ 5 < s.re at hs
    let sigma : Real := (1 / Real.goldenRatio ^ 5 + s.re) / 2
    have hsigma : 1 / Real.goldenRatio ^ 5 < sigma := by dsimp [sigma]; linarith
    have hssigma : sigma < s.re := by dsimp [sigma]; linarith
    have hU : IsOpen {z : Complex | sigma < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have h := golden_germ_third_normalized_factor_majorant sigma hsigma
    dsimp only at h
    let U : Set Complex := {z : Complex | sigma < z.re}
    let f : Nat.Primes -> Complex -> Complex := fun p z =>
      let x := (p : Complex) ^
        (-z * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-z * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor z p - 1
    have hfinite : ∀ J : Finset Nat.Primes,
        DifferentiableOn Complex (fun z : Complex => ∏ p ∈ J, (1 + f p z)) U := by
      intro J
      induction J using Finset.induction_on with
      | empty =>
          simp only [Finset.prod_empty]
          exact differentiableOn_const (c := (1 : Complex))
      | @insert p J hp ih =>
          simp only [Finset.prod_insert hp]
          exact ((differentiableOn_const (c := (1 : Complex))).add
            (by simpa [f, U] using h.2.1 p)).mul ih
    have hlimit := h.2.2.differentiableOn
      (Filter.Eventually.of_forall hfinite) hU
    simpa [f, U] using hlimit.analyticAt (hU.mem_nhds hssigma)
  have hthird := golden_germ_third_order_factorization
  dsimp only at hthird
  have hcomplex : ∀ s : Complex, (3 / 5 : Real) <= s.re ->
      (∏' p : Nat.Primes,
        let x := (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
        let y := (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
        (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
          (1 - y) * (1 + x)⁻¹ * germLocalFactor s p) ≠ 0 := by
    intro s hs
    have hdomain : 1 / Real.goldenRatio ^ 5 < s.re :=
      fifth_threshold_lt_three_fifths.trans_le hs
    let factor : Nat.Primes -> Complex := fun p =>
      let x := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor s p
    have hsum : Summable (fun p : Nat.Primes => ‖factor p - 1‖) := by
      simpa [factor] using hthird.1 s hdomain
    have hgerm := germ_product_ne_zero_of_re_ge_three_fifths s hs
    have hgermLocal : ∀ p : Nat.Primes, germLocalFactor s p ≠ 0 := by
      intro p hzero
      apply hgerm
      exact tprod_of_exists_eq_zero ⟨p, hzero⟩
    have hlocal : ∀ p : Nat.Primes, factor p ≠ 0 := by
      intro p
      simpa [factor] using
        (third_normalized_local_factor_ne_zero_iff s hdomain p).2 (hgermLocal p)
    have hnonzeroAux := tprod_one_add_ne_zero_of_summable
      (f := fun p : Nat.Primes => factor p - 1)
      (fun p => by
        rw [show 1 + (factor p - 1) = factor p by ring]
        exact hlocal p) hsum
    have hfun : (fun p : Nat.Primes => 1 + (factor p - 1)) = factor := by
      funext p
      ring
    rw [hfun] at hnonzeroAux
    simpa [factor] using hnonzeroAux
  have hreal : ∀ sigma : Real, 1 / Real.goldenRatio ^ 5 < sigma ->
      (∏' p : Nat.Primes,
        let x := (p : Complex) ^
          (-(sigma : Complex) * ((Real.goldenRatio ^ 2 : Real) : Complex))
        let y := (p : Complex) ^
          (-(sigma : Complex) * ((Real.goldenRatio ^ 3 : Real) : Complex))
        (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
          (1 - y) * (1 + x)⁻¹ * germLocalFactor (sigma : Complex) p) ≠ 0 := by
    intro sigma hsigma
    let factor : Nat.Primes -> Complex := fun p =>
      let x := (p : Complex) ^
        (-(sigma : Complex) * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-(sigma : Complex) * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor (sigma : Complex) p
    have hsum : Summable (fun p : Nat.Primes => ‖factor p - 1‖) := by
      simpa [factor] using hthird.1 (sigma : Complex) (by simpa using hsigma)
    have hlocal : ∀ p : Nat.Primes, factor p ≠ 0 := by
      intro p
      simpa [factor] using
        (third_normalized_local_factor_ne_zero_iff
          (sigma : Complex) (by simpa using hsigma) p).2
            (real_point_local_factor_ne_zero sigma hsigma p)
    have hnonzeroAux := tprod_one_add_ne_zero_of_summable
      (f := fun p : Nat.Primes => factor p - 1)
      (fun p => by
        rw [show 1 + (factor p - 1) = factor p by ring]
        exact hlocal p) hsum
    have hfun : (fun p : Nat.Primes => 1 + (factor p - 1)) = factor := by
      funext p
      ring
    rw [hfun] at hnonzeroAux
    simpa [factor] using hnonzeroAux
  have hcontinuous : ContinuousAt
      (fun s : Complex => ∏' p : Nat.Primes,
        let x := (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
        let y := (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
        (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
          (1 - y) * (1 + x)⁻¹ * germLocalFactor s p)
      ((1 / Real.goldenRatio ^ 4 : Real) : Complex) :=
    hanalytic.continuousOn.continuousAt
      (hK.mem_nhds (by
        change 1 / Real.goldenRatio ^ 5 < 1 / Real.goldenRatio ^ 4
        exact fifth_threshold_lt_fourth_threshold))
  have hpoint := hreal (1 / Real.goldenRatio ^ 4)
    fifth_threshold_lt_fourth_threshold
  exact ⟨hmajorant, hanalytic, hcomplex, hreal, hcontinuous, hpoint⟩

#print axioms golden_germ_third_normalized_factor_regularity

end

end D5.S3.Analytic.Regularity.GoldenGermThirdNormalizedFactorRegularity
