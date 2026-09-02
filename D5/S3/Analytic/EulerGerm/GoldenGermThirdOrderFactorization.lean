/- GID: D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderFactorization
   generality: I
   mirror-B: D5/B/S3/Analytic/EulerGerm/GoldenGermThirdOrderFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Continue the golden Euler germ through its third-order factorization. -/

import D5.S3.Analytic.EulerGerm.GoldenGermSecondOrderFactorization
import D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderLedger

/- Library-search audit trail (2026-09-03):
   * The frozen `golden_germ_second_order_factorization` supplies the first
     three global zeta factors, its normalized local family, and agreement with
     the canonical prime product. This module only extracts the next two Euler
     factors from that normalized family.
   * The frozen third-order ledger exposes the exact local factor needed here
     only through
     `golden_third_normalized_factor_deviation_norm_summable`. Its proof already
     uses the canonical `o5_beta_growth` bound for the rank-five tail, so that
     estimate is imported and reused rather than reproved here.
   * Pinned Mathlib supplies `riemannZeta_eulerProduct_hasProd`,
     `Nat.Primes.summable_rpow`, `multipliable_one_add_of_summable`, and
     `HasProd.unique`. No repository theorem already assembles the displayed
     third-order global factorization. -/

namespace D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderFactorization

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.EulerGerm.GermProductConvergence
open D5.S3.Analytic.EulerGerm.GoldenGermSecondOrderFactorization
open D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderLedger
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor

noncomputable section

private theorem zeta_reciprocal_euler_hasProd (w : Complex)
    (hw : 1 < w.re) :
    HasProd (fun p : Nat.Primes =>
      1 - (p : Complex) ^ (-w)) (riemannZeta w)⁻¹ := by
  have hnorm : Summable (fun p : Nat.Primes =>
      ‖-((p : Complex) ^ (-w))‖) := by
    have hexponent : -w.re < -1 := by linarith
    refine (Nat.Primes.summable_rpow.mpr hexponent).congr fun p => ?_
    rw [norm_neg, Complex.norm_natCast_cpow_of_pos p.prop.pos]
    simp only [Complex.neg_re]
  have hdirect : Multipliable (fun p : Nat.Primes =>
      1 - (p : Complex) ^ (-w)) := by
    have h := multipliable_one_add_of_summable hnorm
    refine h.congr fun p => ?_
    ring
  have hzeta := riemannZeta_eulerProduct_hasProd hw
  let directProduct : Complex :=
    ∏' p : Nat.Primes, (1 - (p : Complex) ^ (-w))
  have hlocal (p : Nat.Primes) :
      (1 - (p : Complex) ^ (-w)) *
        (1 - (p : Complex) ^ (-w))⁻¹ = 1 := by
    apply mul_inv_cancel₀
    rw [sub_ne_zero]
    intro heq
    have hnorm_lt : ‖(p : Complex) ^ (-w)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
      simp only [Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast p.prop.one_lt) (by linarith)
    rw [← heq, norm_one] at hnorm_lt
    exact lt_irrefl 1 hnorm_lt
  have hcombined : HasProd (fun _ : Nat.Primes => (1 : Complex))
      (directProduct * riemannZeta w) := by
    dsimp [directProduct]
    exact (hdirect.hasProd.mul hzeta).congr_fun fun p => (hlocal p).symm
  have hvalue : directProduct * riemannZeta w = 1 :=
    HasProd.unique hcombined hasProd_one
  have hzeta_ne : riemannZeta w ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re hw.le
  have htprod : directProduct = (riemannZeta w)⁻¹ :=
    (mul_eq_one_iff_eq_inv₀ hzeta_ne).mp hvalue
  rw [← htprod]
  simpa [directProduct] using hdirect.hasProd

private theorem second_normalized_factor_multipliable (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 4 < s.re) :
    Multipliable (fun p : Nat.Primes =>
      (1 - (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
        (1 + (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
        germLocalFactor s p) := by
  have hsecond := golden_germ_second_order_factorization
  dsimp only at hsecond
  have hdev := hsecond.2 s hs
  have hproduct := multipliable_one_add_of_summable hdev
  refine hproduct.congr fun p => ?_
  ring

private theorem third_normalized_factor_multipliable (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 5 < s.re) :
    Multipliable (fun p : Nat.Primes =>
      let x := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor s p) := by
  have hdev :=
    golden_third_normalized_factor_deviation_norm_summable s hs
  dsimp only at hdev ⊢
  have hproduct := multipliable_one_add_of_summable hdev
  refine hproduct.congr fun p => ?_
  ring

private theorem second_normalized_product_third_factorization (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 2 < s.re) :
    (∏' p : Nat.Primes,
      (1 - (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
        (1 + (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
        germLocalFactor s p) =
      (riemannZeta
        (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s))⁻¹ *
        riemannZeta
          ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
            Complex) * s)) *
        ∏' p : Nat.Primes,
          let x := (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
          let y := (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
          (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
            (1 - y) * (1 + x)⁻¹ * germLocalFactor s p := by
  have hphi2 : 0 < Real.goldenRatio ^ 2 := by positivity
  have hphi3 : 0 < Real.goldenRatio ^ 3 := by positivity
  have hphi4 : 0 < Real.goldenRatio ^ 4 := by positivity
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  have hphi2_lt_phi4 :
      Real.goldenRatio ^ 2 < Real.goldenRatio ^ 4 := by
    have hphi2_one : 1 < Real.goldenRatio ^ 2 := by
      nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
    calc
      Real.goldenRatio ^ 2 <
          Real.goldenRatio ^ 2 * Real.goldenRatio ^ 2 :=
        (lt_mul_iff_one_lt_right hphi2).mpr hphi2_one
      _ = Real.goldenRatio ^ 4 := by ring
  have hphi4_lt_phi5 :
      Real.goldenRatio ^ 4 < Real.goldenRatio ^ 5 := by
    calc
      Real.goldenRatio ^ 4 <
          Real.goldenRatio ^ 4 * Real.goldenRatio :=
        (lt_mul_iff_one_lt_right hphi4).mpr Real.one_lt_goldenRatio
      _ = Real.goldenRatio ^ 5 := by ring
  have hs4 : 1 / Real.goldenRatio ^ 4 < s.re :=
    (one_div_lt_one_div_of_lt hphi2 hphi2_lt_phi4).trans hs
  have hs5 : 1 / Real.goldenRatio ^ 5 < s.re :=
    (one_div_lt_one_div_of_lt hphi2
      (hphi2_lt_phi4.trans hphi4_lt_phi5)).trans hs
  have hbase : 1 < s.re * Real.goldenRatio ^ 2 :=
    (div_lt_iff₀ hphi2).mp (by simpa [div_eq_mul_inv] using hs)
  have hdoubleCoefficient :
      Real.goldenRatio ^ 2 < 2 * Real.goldenRatio ^ 3 := by
    nlinarith
  have hmixedCoefficient :
      Real.goldenRatio ^ 2 <
        2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 := by
    nlinarith
  have hdomainDouble :
      1 < ((((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s).re) := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hscaled :=
      mul_lt_mul_of_pos_left hdoubleCoefficient hspos
    nlinarith
  have hdomainMixed :
      1 < (((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
        Complex) * s).re)) := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hscaled := mul_lt_mul_of_pos_left hmixedCoefficient hspos
    nlinarith
  have hreciprocal := zeta_reciprocal_euler_hasProd
    (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s) hdomainDouble
  have hmixed := riemannZeta_eulerProduct_hasProd hdomainMixed
  have hthird := third_normalized_factor_multipliable s hs5
  have hsecond := second_normalized_factor_multipliable s hs4
  have hcombined := (hreciprocal.mul hmixed).mul hthird.hasProd
  have hlocal (p : Nat.Primes) :
      (1 - (p : Complex) ^
          (-(((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s))) *
        (1 - (p : Complex) ^
          (-((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
            Complex) * s))))⁻¹ *
        ((1 - ((p : Complex) ^
            (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ 2)⁻¹ *
          (1 - ((p : Complex) ^
              (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ 2 *
            (p : Complex) ^
              (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
          (1 - (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
          (1 + (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
          germLocalFactor s p) =
        (1 - (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
          (1 + (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
          germLocalFactor s p := by
    let x : Complex := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
    let y : Complex := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
    have hpne : (p : Complex) ≠ 0 := by
      exact_mod_cast p.prop.ne_zero
    have hdoublePower :
        (p : Complex) ^
            (-(((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s)) =
          y ^ 2 := by
      have hexponent :
          -(((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s) =
            -s * ((Real.goldenRatio ^ 3 : Real) : Complex) +
              -s * ((Real.goldenRatio ^ 3 : Real) : Complex) := by
        push_cast
        ring
      rw [hexponent, Complex.cpow_add _ _ hpne]
      change y * y = y ^ 2
      ring
    have hmixedPower :
        (p : Complex) ^
            (-((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
              Complex) * s))) =
          x ^ 2 * y := by
      have hexponent :
          -((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
              Complex) * s)) =
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex) +
              -s * ((Real.goldenRatio ^ 2 : Real) : Complex)) +
                -s * ((Real.goldenRatio ^ 3 : Real) : Complex) := by
        push_cast
        ring
      rw [hexponent, Complex.cpow_add _ _ hpne,
        Complex.cpow_add _ _ hpne]
      change x * x * y = x ^ 2 * y
      ring
    have hySquareNorm : ‖y ^ 2‖ < 1 := by
      rw [← hdoublePower]
      rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
      simp only [Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast p.prop.one_lt) (by linarith)
    have hxyNorm : ‖x ^ 2 * y‖ < 1 := by
      rw [← hmixedPower]
      rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
      simp only [Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast p.prop.one_lt) (by linarith)
    have hySquareMinus : 1 - y ^ 2 ≠ 0 := by
      rw [sub_ne_zero]
      intro heq
      rw [← heq, norm_one] at hySquareNorm
      exact lt_irrefl 1 hySquareNorm
    have hxyMinus : 1 - x ^ 2 * y ≠ 0 := by
      rw [sub_ne_zero]
      intro heq
      rw [← heq, norm_one] at hxyNorm
      exact lt_irrefl 1 hxyNorm
    have hxyMinus' : 1 - y * x ^ 2 ≠ 0 := by
      simpa [mul_comm] using hxyMinus
    rw [hdoublePower, hmixedPower]
    change (1 - y ^ 2) * (1 - x ^ 2 * y)⁻¹ *
      ((1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor s p) =
      (1 - y) * (1 + x)⁻¹ * germLocalFactor s p
    field_simp [hySquareMinus, hxyMinus, hxyMinus']
  have hfactored : HasProd (fun p : Nat.Primes =>
      (1 - (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) *
        (1 + (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))⁻¹ *
        germLocalFactor s p)
      ((riemannZeta
        (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s))⁻¹ *
        riemannZeta
          ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
            Complex) * s)) *
        ∏' p : Nat.Primes,
          let x := (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
          let y := (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
          (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
            (1 - y) * (1 + x)⁻¹ * germLocalFactor s p) :=
    hcombined.congr_fun fun p => (hlocal p).symm
  exact hsecond.hasProd.unique hfactored

private theorem germ_product_third_factorization (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 2 < s.re) :
    (∏' p : Nat.Primes, germLocalFactor s p) =
      riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s) *
        riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s) *
        (riemannZeta
          (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s))⁻¹ *
        ((riemannZeta
          (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s))⁻¹ *
          riemannZeta
            ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
              Complex) * s)) *
          ∏' p : Nat.Primes,
            let x := (p : Complex) ^
              (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
            let y := (p : Complex) ^
              (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
            (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
              (1 - y) * (1 + x)⁻¹ * germLocalFactor s p) := by
  have hphi2 : 0 < Real.goldenRatio ^ 2 := by positivity
  have hphi2_one : 1 < Real.goldenRatio ^ 2 := by
    nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  have hphi2_lt_phi4 :
      Real.goldenRatio ^ 2 < Real.goldenRatio ^ 4 := by
    calc
      Real.goldenRatio ^ 2 <
          Real.goldenRatio ^ 2 * Real.goldenRatio ^ 2 :=
        (lt_mul_iff_one_lt_right hphi2).mpr hphi2_one
      _ = Real.goldenRatio ^ 4 := by ring
  have hs4 : 1 / Real.goldenRatio ^ 4 < s.re :=
    (one_div_lt_one_div_of_lt hphi2 hphi2_lt_phi4).trans hs
  have hsecond := golden_germ_second_order_factorization
  dsimp only at hsecond
  rcases hsecond.1 with ⟨continuedSecond, hcontinuedSecond, _⟩
  let sSecond : {z : Complex // 1 / Real.goldenRatio ^ 4 < z.re} :=
    ⟨s, hs4⟩
  have horiginal := hcontinuedSecond.1 sSecond hs
  have hformula := hcontinuedSecond.2 sSecond
  have hnext := second_normalized_product_third_factorization s hs
  have hraw := germLocalFactor_multipliable s hs
  have hfactored : HasProd
      (fun p : Nat.Primes => germLocalFactor s p)
      (riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s) *
        riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s) *
        (riemannZeta
          (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s))⁻¹ *
        ((riemannZeta
          (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s))⁻¹ *
          riemannZeta
            ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
              Complex) * s)) *
          ∏' p : Nat.Primes,
            let x := (p : Complex) ^
              (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
            let y := (p : Complex) ^
              (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
            (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
              (1 - y) * (1 + x)⁻¹ * germLocalFactor s p)) := by
    rw [← hnext, ← hformula, horiginal]
    exact hraw.hasProd
  exact hraw.hasProd.unique hfactored

/-- The third-order normalized local factors have summable deviations on
`Re s > 1 / phi^5`. Their prime product gives the unique continuation with the
five displayed zeta factors, agreeing with the canonical germ product on
`Re s > 1 / phi^2`. -/
theorem golden_germ_third_order_factorization :
    let Kp : Complex -> Nat.Primes -> Complex := fun s p =>
      let x := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor s p
    let G3 : Complex -> Complex := fun s =>
      ∏' p : Nat.Primes, Kp s p
    (∀ s : Complex, 1 / Real.goldenRatio ^ 5 < s.re ->
      Summable (fun p : Nat.Primes => ‖Kp s p - 1‖)) ∧
    ∃! continuedGerm :
        {s : Complex // 1 / Real.goldenRatio ^ 5 < s.re} -> Complex,
      (∀ s, 1 / Real.goldenRatio ^ 2 < s.1.re ->
        continuedGerm s = ∏' p : Nat.Primes, germLocalFactor s.1 p) ∧
      (∀ s, continuedGerm s =
        riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1) *
          riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s.1) *
          (riemannZeta
            (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s.1))⁻¹ *
          ((riemannZeta
            (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s.1))⁻¹ *
            riemannZeta
              ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
                Complex) * s.1)) *
            G3 s.1)) := by
  dsimp only
  constructor
  · intro s hs
    simpa using
      golden_third_normalized_factor_deviation_norm_summable s hs
  · let continuedGerm :
        {s : Complex // 1 / Real.goldenRatio ^ 5 < s.re} -> Complex := fun s =>
      riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1) *
        riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s.1) *
        (riemannZeta
          (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s.1))⁻¹ *
        ((riemannZeta
          (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s.1))⁻¹ *
          riemannZeta
            ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
              Complex) * s.1)) *
          ∏' p : Nat.Primes,
            let x := (p : Complex) ^
              (-s.1 * ((Real.goldenRatio ^ 2 : Real) : Complex))
            let y := (p : Complex) ^
              (-s.1 * ((Real.goldenRatio ^ 3 : Real) : Complex))
            (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
              (1 - y) * (1 + x)⁻¹ * germLocalFactor s.1 p)
    refine ⟨continuedGerm, ?_, ?_⟩
    · constructor
      · intro s hs
        exact (germ_product_third_factorization s.1 hs).symm
      · intro s
        rfl
    · intro other hother
      funext s
      rw [hother.2 s]

#print axioms golden_germ_third_order_factorization

end

end D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderFactorization
