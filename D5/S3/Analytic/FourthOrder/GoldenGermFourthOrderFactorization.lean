/- GID: D5/S3/Analytic/FourthOrder/GoldenGermFourthOrderFactorization
   generality: I
   mirror-B: D5/B/S3/Analytic/FourthOrder/GoldenGermFourthOrderFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fourth-order seven-zeta factorization and unique golden germ continuation. -/

import D5.S3.Analytic.EulerGerm.GoldenGermFourthOrderLedger

/- Library-search audit trail (2026-09-03):
   * The frozen fourth-order ledger supplies the exact local identity
     `C4 * K3 = 1 + R4` and, crucially, norm summability of the resulting
     fourth-order factor above `1 / o5Beta 6`.  This module reuses that final
     summability conjunct and does not repeat its local expansion or estimates.
   * The frozen third-order factorization supplies the five-zeta continuation,
     its agreement with the canonical prime product, and the uniqueness
     pattern.  Its displayed function is used as the bridge on the original
     convergence half-plane.
   * The fourth-order census supplies `o5Beta 6 = 2 * phi^4` and
     `phi^5 < o5Beta 6`, which transport the original half-plane into both
     predecessor domains.  Its private arithmetic is not reconstructed.
   * Pinned Mathlib supplies `riemannZeta_eulerProduct_hasProd`,
     `HasProd.inv₀`, `HasProd.mul`, `HasProd.unique`,
     `multipliable_one_add_of_summable`, and `Complex.cpow_add`.  Repository
     and pinned-library searches found no existing seven-zeta fourth-order
     factorization.  The mixed-power calculation below is definition-level:
     the corresponding ledger helper is private and is not exposed for reuse. -/

namespace D5.S3.Analytic.FourthOrder.GoldenGermFourthOrderFactorization

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderFactorization
open D5.S3.Analytic.EulerGerm.GoldenGermFourthOrderExponentCensus
open D5.S3.Analytic.EulerGerm.GoldenGermFourthOrderLedger

noncomputable section

private theorem zeta_reciprocal_euler_hasProd (w : Complex)
    (hw : 1 < w.re) :
    HasProd (fun p : Nat.Primes =>
      1 - (p : Complex) ^ (-w)) (riemannZeta w)⁻¹ := by
  have hzeta := riemannZeta_eulerProduct_hasProd hw
  have hzeta_ne : riemannZeta w ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hw
  simpa only [inv_inv] using hzeta.inv₀ hzeta_ne

private theorem one_sub_prime_cpow_ne_zero (p : Nat.Primes)
    (w : Complex) (hw : 1 < w.re) :
    1 - (p : Complex) ^ (-w) ≠ 0 := by
  rw [sub_ne_zero]
  intro heq
  have hnorm : ‖(p : Complex) ^ (-w)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
    simp only [Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.prop.one_lt) (by linarith)
  rw [← heq, norm_one] at hnorm
  exact lt_irrefl 1 hnorm

private theorem mixed_mode_cpow (s : Complex) (p : Nat.Primes)
    (a b : Nat) :
    (p : Complex) ^
        (-s * ((((a : Real) * Real.goldenRatio ^ 2 +
          (b : Real) * Real.goldenRatio ^ 3) : Real) : Complex)) =
      ((p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ a *
        ((p : Complex) ^
          (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))) ^ b := by
  have hbase : (p : Complex) ≠ 0 := by
    exact_mod_cast p.prop.ne_zero
  have hexponent :
      -s * ((((a : Real) * Real.goldenRatio ^ 2 +
        (b : Real) * Real.goldenRatio ^ 3) : Real) : Complex) =
        (a : Complex) *
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)) +
          (b : Complex) *
            (-s * ((Real.goldenRatio ^ 3 : Real) : Complex)) := by
    push_cast
    ring
  rw [hexponent, Complex.cpow_add _ _ hbase]
  exact congrArg₂ (fun z w : Complex => z * w)
    (Complex.cpow_nat_mul (p : Complex) a
      (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)))
    (Complex.cpow_nat_mul (p : Complex) b
      (-s * ((Real.goldenRatio ^ 3 : Real) : Complex)))

private theorem original_domain_implies_fifth_and_beta_six
    (s : Complex) (hs : 1 / Real.goldenRatio ^ 2 < s.re) :
    1 / Real.goldenRatio ^ 5 < s.re ∧ 1 / o5Beta 6 < s.re := by
  have hphi2 : 0 < Real.goldenRatio ^ 2 := by positivity
  have hphi4 : 0 < Real.goldenRatio ^ 4 := by positivity
  have hphi2_one : 1 < Real.goldenRatio ^ 2 := by
    nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  have hphi2_lt_phi4 :
      Real.goldenRatio ^ 2 < Real.goldenRatio ^ 4 := by
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
  have hs5 : 1 / Real.goldenRatio ^ 5 < s.re :=
    (one_div_lt_one_div_of_lt hphi2
      (hphi2_lt_phi4.trans hphi4_lt_phi5)).trans hs
  have hphi5_lt_beta6 : Real.goldenRatio ^ 5 < o5Beta 6 :=
    golden_germ_fourth_order_exponent_census.2.2.2.2.1
  have hs6 : 1 / o5Beta 6 < s.re :=
    (one_div_lt_one_div_of_lt (by positivity) hphi5_lt_beta6).trans hs5
  exact ⟨hs5, hs6⟩

private theorem one_tenth_in_fourth_order_domain_numeric_check :
    1 / o5Beta 6 < (1 : Real) / 10 := by
  rw [golden_germ_fourth_order_exponent_census.1]
  have hsq : Real.sqrt 5 ^ 2 = (5 : Real) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hphi_fourth :
      Real.goldenRatio ^ 4 = 3 * Real.goldenRatio + 2 := by
    rw [show Real.goldenRatio ^ 4 = (Real.goldenRatio ^ 2) ^ 2 by ring,
      Real.goldenRatio_sq]
    nlinarith [Real.goldenRatio_sq]
  have hten : (10 : Real) < 2 * Real.goldenRatio ^ 4 := by
    rw [hphi_fourth, Real.goldenRatio]
    nlinarith
  exact one_div_lt_one_div_of_lt (by norm_num) hten

private theorem third_normalized_product_fourth_factorization
    (s : Complex) (hs : 1 / Real.goldenRatio ^ 2 < s.re) :
    (∏' p : Nat.Primes,
      let x := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor s p) =
      riemannZeta
          ((((Real.goldenRatio ^ 2 + 2 * Real.goldenRatio ^ 3 : Real) :
            Complex) * s)) *
        (riemannZeta
          ((((3 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
            Complex) * s)))⁻¹ *
        ∏' p : Nat.Primes,
          let x := (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
          let y := (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
          (1 - x * y ^ 2) * (1 - x ^ 3 * y)⁻¹ *
            ((1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
              (1 - y) * (1 + x)⁻¹ * germLocalFactor s p) := by
  let A : Real := Real.goldenRatio ^ 2 + 2 * Real.goldenRatio ^ 3
  let B : Real := 3 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3
  let x : Nat.Primes → Complex := fun p =>
    (p : Complex) ^ (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
  let y : Nat.Primes → Complex := fun p =>
    (p : Complex) ^ (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
  let K3 : Nat.Primes → Complex := fun p =>
    (1 - y p ^ 2)⁻¹ * (1 - x p ^ 2 * y p) *
      (1 - y p) * (1 + x p)⁻¹ * germLocalFactor s p
  let K4 : Nat.Primes → Complex := fun p =>
    (1 - x p * y p ^ 2) * (1 - x p ^ 3 * y p)⁻¹ * K3 p
  change (∏' p : Nat.Primes, K3 p) =
    riemannZeta ((A : Complex) * s) *
      (riemannZeta ((B : Complex) * s))⁻¹ *
        ∏' p : Nat.Primes, K4 p
  rcases original_domain_implies_fifth_and_beta_six s hs with ⟨hs5, hs6⟩
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  have hphi2 : 0 < Real.goldenRatio ^ 2 := by positivity
  have hbase : 1 < s.re * Real.goldenRatio ^ 2 :=
    (div_lt_iff₀ hphi2).mp (by simpa [div_eq_mul_inv] using hs)
  have hAcoeff : Real.goldenRatio ^ 2 < A := by
    dsimp [A]
    nlinarith [show 0 < Real.goldenRatio ^ 3 by positivity]
  have hBcoeff : Real.goldenRatio ^ 2 < B := by
    dsimp [B]
    nlinarith [hphi2, show 0 < Real.goldenRatio ^ 3 by positivity]
  have hdomainA : 1 < (((A : Real) : Complex) * s).re := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hscaled := mul_lt_mul_of_pos_left hAcoeff hspos
    nlinarith
  have hdomainB : 1 < (((B : Real) : Complex) * s).re := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hscaled := mul_lt_mul_of_pos_left hBcoeff hspos
    nlinarith
  have hA := riemannZeta_eulerProduct_hasProd hdomainA
  have hB := zeta_reciprocal_euler_hasProd ((B : Complex) * s) hdomainB
  have hthird := golden_germ_third_order_factorization
  dsimp only at hthird
  have hK3Dev : Summable (fun p : Nat.Primes => ‖K3 p - 1‖) := by
    simpa [x, y, K3] using hthird.1 s hs5
  have hK3 : Multipliable K3 := by
    have hproduct := multipliable_one_add_of_summable hK3Dev
    refine hproduct.congr fun p => ?_
    ring
  have hfourth :=
    golden_fourth_normalized_factor_deviation_norm_summable s hs6
  dsimp only at hfourth
  have hK4Dev : Summable (fun p : Nat.Primes => ‖K4 p - 1‖) := by
    simpa [x, y, K3, K4] using hfourth.2.2.2.2.2.1
  have hK4 : Multipliable K4 := by
    have hproduct := multipliable_one_add_of_summable hK4Dev
    refine hproduct.congr fun p => ?_
    ring
  have hcombined := (hA.mul hB).mul hK4.hasProd
  have hlocal (p : Nat.Primes) :
      (1 - (p : Complex) ^ (-((A : Complex) * s)))⁻¹ *
          (1 - (p : Complex) ^ (-((B : Complex) * s))) * K4 p =
        K3 p := by
    have hAexponent : -((A : Complex) * s) = -s * (A : Complex) := by
      ring
    have hBexponent : -((B : Complex) * s) = -s * (B : Complex) := by
      ring
    have hApower :
        (p : Complex) ^ (-s * (A : Complex)) = x p * y p ^ 2 := by
      simpa [A, x, y] using mixed_mode_cpow s p 1 2
    have hBpower :
        (p : Complex) ^ (-s * (B : Complex)) = x p ^ 3 * y p := by
      simpa [B, x, y] using mixed_mode_cpow s p 3 1
    have hAne := one_sub_prime_cpow_ne_zero p ((A : Complex) * s) hdomainA
    have hBne := one_sub_prime_cpow_ne_zero p ((B : Complex) * s) hdomainB
    rw [hAexponent, hApower] at hAne
    rw [hBexponent, hBpower] at hBne
    rw [hAexponent, hBexponent, hApower, hBpower]
    dsimp [K4]
    field_simp [hAne, hBne]
  have hfactored : HasProd K3
      (riemannZeta ((A : Complex) * s) *
        (riemannZeta ((B : Complex) * s))⁻¹ *
          ∏' p : Nat.Primes, K4 p) :=
    hcombined.congr_fun fun p => (hlocal p).symm
  exact hK3.hasProd.unique hfactored

private theorem germ_product_fourth_factorization
    (s : Complex) (hs : 1 / Real.goldenRatio ^ 2 < s.re) :
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
          (riemannZeta
            ((((Real.goldenRatio ^ 2 + 2 * Real.goldenRatio ^ 3 : Real) :
              Complex) * s)) *
            (riemannZeta
              ((((3 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
                Complex) * s)))⁻¹ *
            ∏' p : Nat.Primes,
              let x := (p : Complex) ^
                (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
              let y := (p : Complex) ^
                (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
              (1 - x * y ^ 2) * (1 - x ^ 3 * y)⁻¹ *
                ((1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
                  (1 - y) * (1 + x)⁻¹ * germLocalFactor s p))) := by
  have hs5 := (original_domain_implies_fifth_and_beta_six s hs).1
  have hthird := golden_germ_third_order_factorization
  dsimp only at hthird
  rcases hthird.2 with ⟨continuedThird, hcontinuedThird, _⟩
  let sThird : {z : Complex // 1 / Real.goldenRatio ^ 5 < z.re} :=
    ⟨s, hs5⟩
  have horiginal := hcontinuedThird.1 sThird hs
  have hformula := hcontinuedThird.2 sThird
  have hnext := third_normalized_product_fourth_factorization s hs
  calc
    (∏' p : Nat.Primes, germLocalFactor s p) = continuedThird sThird :=
      horiginal.symm
    _ = riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s) *
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
        simpa [sThird] using hformula
    _ = _ := by rw [hnext]

/-- The fourth-order normalized local factors have summable deviations on
`Re s > 1 / o5Beta 6`.  Their prime product gives the unique function on that
half-plane which agrees with the canonical golden germ product on
`Re s > 1 / phi^2` and satisfies the displayed seven-zeta factorization. -/
theorem golden_germ_fourth_order_factorization :
    let A : Real := Real.goldenRatio ^ 2 + 2 * Real.goldenRatio ^ 3
    let B : Real := 3 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3
    let K4 : Complex → Nat.Primes → Complex := fun s p =>
      let x := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - x * y ^ 2) * (1 - x ^ 3 * y)⁻¹ *
        ((1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
          (1 - y) * (1 + x)⁻¹ * germLocalFactor s p)
    let G4 : Complex → Complex := fun s =>
      ∏' p : Nat.Primes, K4 s p
    (∀ s : Complex, 1 / o5Beta 6 < s.re →
      Summable (fun p : Nat.Primes => ‖K4 s p - 1‖)) ∧
    ∃! continuedGerm : {s : Complex // 1 / o5Beta 6 < s.re} → Complex,
      (∀ s, 1 / Real.goldenRatio ^ 2 < s.1.re →
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
            (riemannZeta ((A : Complex) * s.1) *
              (riemannZeta ((B : Complex) * s.1))⁻¹ * G4 s.1))) := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  fail_if_success (solve | trivial)
  dsimp only
  constructor
  · intro s hs
    have hfourth :=
      golden_fourth_normalized_factor_deviation_norm_summable s hs
    dsimp only at hfourth
    exact hfourth.2.2.2.2.2.1
  · let continuedGerm :
        {s : Complex // 1 / o5Beta 6 < s.re} → Complex := fun s =>
      riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1) *
        riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s.1) *
        (riemannZeta
          (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s.1))⁻¹ *
        ((riemannZeta
          (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s.1))⁻¹ *
          riemannZeta
            ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
              Complex) * s.1)) *
          (riemannZeta
            ((((Real.goldenRatio ^ 2 + 2 * Real.goldenRatio ^ 3 : Real) :
              Complex) * s.1)) *
            (riemannZeta
              ((((3 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
                Complex) * s.1)))⁻¹ *
            ∏' p : Nat.Primes,
              let x := (p : Complex) ^
                (-s.1 * ((Real.goldenRatio ^ 2 : Real) : Complex))
              let y := (p : Complex) ^
                (-s.1 * ((Real.goldenRatio ^ 3 : Real) : Complex))
              (1 - x * y ^ 2) * (1 - x ^ 3 * y)⁻¹ *
                ((1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
                  (1 - y) * (1 + x)⁻¹ * germLocalFactor s.1 p)))
    refine ⟨continuedGerm, ?_, ?_⟩
    · constructor
      · intro s hs
        exact (germ_product_fourth_factorization s.1 hs).symm
      · intro s
        rfl
    · intro other hother
      funext s
      rw [hother.2 s]

#print axioms golden_germ_fourth_order_factorization

end

end D5.S3.Analytic.FourthOrder.GoldenGermFourthOrderFactorization
