/- GID: D5/S3/Analytic/GermWindow/GoldenGermThirdOrderWindowZeroCriterion
   generality: I
   mirror-B: D5/B/S3/Analytic/GermWindow/GoldenGermThirdOrderWindowZeroCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Classify third-order golden-germ zeros in the RH window. -/

import D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderFactorization
import D5.S3.Analytic.EulerGerm.GoldenGermWindowZeroCriterion
import D5.S3.Weil.ZetaCore.Statement
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/- Library-search audit trail (2026-09-03):
   * The frozen `golden_germ_third_order_factorization` supplies the exact
     third-order normalized factor and its summable deviation on
     `Re s > 1 / phi^5`.
   * The frozen `golden_window_zero_on_line_of_rh` supplies the RH confinement
     implication for a surviving residual factor.
   * The frozen second-order zero-divisor theorem has the same infinite-product
     proof shape but a different normalized factor and a stronger half-plane.
   * Pinned Mathlib supplies `tprod_one_add_ne_zero_of_summable`,
     `tprod_of_exists_eq_zero`, `Complex.cpow_ne_zero_iff`, and
     `Complex.norm_natCast_cpow_of_pos`. No existing declaration gives any of
     the three statements below. -/

namespace D5.S3.Analytic.GermWindow.GoldenGermThirdOrderWindowZeroCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderFactorization
open D5.S3.Analytic.EulerGerm.GoldenGermWindowZeroCriterion
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor

noncomputable section

private theorem normalized_mode_norm_lt_one (s : Complex) (hs : 0 < s.re)
    (c : Real) (hc : 0 < c) (p : Nat.Primes) :
    ‖(p : Complex) ^ (-s * (c : Complex))‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  rw [show (-s * (c : Complex)).re = -s.re * c by norm_num]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast p.prop.one_lt) (mul_neg_of_neg_of_pos (by linarith) hc)

private theorem third_normalized_factor_ne_zero_iff (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 5 < s.re) (p : Nat.Primes) :
    (let x := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor s p ≠ 0) ↔
      germLocalFactor s p ≠ 0 := by
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  let x : Complex := (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
  let y : Complex := (p : Complex) ^
    (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
  have hxlt : ‖x‖ < 1 := by
    exact normalized_mode_norm_lt_one s hspos
      (Real.goldenRatio ^ 2) (by positivity) p
  have hylt : ‖y‖ < 1 := by
    exact normalized_mode_norm_lt_one s hspos
      (Real.goldenRatio ^ 3) (by positivity) p
  have hy2lt : ‖y ^ 2‖ < 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg y]
  have hx2lt : ‖x‖ ^ 2 < 1 := by
    nlinarith [norm_nonneg x]
  have hypos : 0 < ‖y‖ := by
    apply norm_pos_iff.mpr
    dsimp [y]
    apply Complex.cpow_ne_zero_iff.mpr
    left
    exact_mod_cast p.prop.ne_zero
  have hx2ylt : ‖x ^ 2 * y‖ < 1 := by
    rw [norm_mul, norm_pow]
    calc
      ‖x‖ ^ 2 * ‖y‖ < 1 * 1 :=
        mul_lt_mul hx2lt hylt.le hypos (by norm_num)
      _ = 1 := by norm_num
  have hy2minus : 1 - y ^ 2 ≠ 0 := by
    intro h
    have hy2 : y ^ 2 = 1 := (sub_eq_zero.mp h).symm
    rw [hy2, norm_one] at hy2lt
    exact (lt_irrefl 1) hy2lt
  have hxyminus : 1 - x ^ 2 * y ≠ 0 := by
    intro h
    have hxy : x ^ 2 * y = 1 := (sub_eq_zero.mp h).symm
    rw [hxy, norm_one] at hx2ylt
    exact (lt_irrefl 1) hx2ylt
  have hyminus : 1 - y ≠ 0 := by
    intro h
    have hy : y = 1 := (sub_eq_zero.mp h).symm
    rw [hy, norm_one] at hylt
    exact (lt_irrefl 1) hylt
  have hxplus : 1 + x ≠ 0 := by
    intro h
    have hx : x = -1 := by linear_combination h
    rw [hx, norm_neg, norm_one] at hxlt
    exact (lt_irrefl 1) hxlt
  change ((1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
    (1 - y) * (1 + x)⁻¹ * germLocalFactor s p ≠ 0) ↔ _
  constructor
  · intro h hlocal
    apply h
    simp [hlocal]
  · intro hlocal
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (inv_ne_zero hy2minus) hxyminus) hyminus)
        (inv_ne_zero hxplus)) hlocal

/-- Under RH, a zero of the continued third-order golden germ in the open
window lies on the pulled-back critical line whenever the third-order residual
survives. -/
theorem golden_continued_germ_window_zero_on_line_of_rh
    (hRH : RiemannHypothesis) :
    let Kp : Complex -> Nat.Primes -> Complex := fun s p =>
      let x := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor s p
    let G3 : Complex -> Complex := fun s =>
      ∏' p : Nat.Primes, Kp s p
    ∀ continuedGerm :
        {s : Complex // 1 / Real.goldenRatio ^ 5 < s.re} -> Complex,
      ((∀ s, 1 / Real.goldenRatio ^ 2 < s.1.re ->
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
            G3 s.1))) ->
      ∀ s, 1 / (2 * Real.goldenRatio ^ 3) < s.1.re ->
        s.1.re < 1 / Real.goldenRatio ^ 2 ->
        continuedGerm s = 0 -> G3 s.1 ≠ 0 ->
        s.1.re = 1 / (2 * Real.goldenRatio ^ 2) := by
  dsimp only
  intro continuedGerm hcontinued s hlo hhi hzero hG3
  apply golden_window_zero_on_line_of_rh hRH
    (fun z => ∏' p : Nat.Primes,
      let x := (p : Complex) ^
        (-z * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-z * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor z p)
    s.1 hlo hhi _ hG3
  rw [← hcontinued.2 s]
  exact hzero

/-- On `Re s > 1 / phi^5`, the frozen third-order residual vanishes exactly
when one of the canonical golden local factors vanishes. -/
theorem golden_third_residual_eq_zero_iff_exists_local_factor_zero
    (s : Complex) (hs : 1 / Real.goldenRatio ^ 5 < s.re) :
    let Kp : Complex -> Nat.Primes -> Complex := fun s p =>
      let x := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor s p
    let G3 : Complex -> Complex := fun s =>
      ∏' p : Nat.Primes, Kp s p
    G3 s = 0 ↔ ∃ p : Nat.Primes, germLocalFactor s p = 0 := by
  dsimp only
  let Kp : Nat.Primes -> Complex := fun p =>
    let x := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
    let y := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
    (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
      (1 - y) * (1 + x)⁻¹ * germLocalFactor s p
  have hdev : Summable (fun p : Nat.Primes => ‖Kp p - 1‖) := by
    have hthird := golden_germ_third_order_factorization
    dsimp only at hthird
    simpa [Kp] using hthird.1 s hs
  constructor
  · intro hprod
    by_contra hlocal
    push Not at hlocal
    have hKp : ∀ p : Nat.Primes, Kp p ≠ 0 := by
      intro p
      simpa [Kp] using
        (third_normalized_factor_ne_zero_iff s hs p).2 (hlocal p)
    have hne : (∏' p : Nat.Primes, Kp p) ≠ 0 := by
      have hone (p : Nat.Primes) : 1 + (Kp p - 1) = Kp p := by ring
      have h := tprod_one_add_ne_zero_of_summable
        (f := fun p : Nat.Primes => Kp p - 1)
        (fun p => by rw [hone p]; exact hKp p) hdev
      rw [tprod_congr hone] at h
      exact h
    exact hne (by simpa [Kp] using hprod)
  · rintro ⟨p, hp⟩
    change (∏' p : Nat.Primes, Kp p) = 0
    apply tprod_of_exists_eq_zero
    exact ⟨p, by simp [Kp, hp]⟩

private theorem zeta_ne_zero_of_rh_of_half_lt_re
    (hRH : RiemannHypothesis) {rho : Complex}
    (hhalf : (1 : Real) / 2 < rho.re) : riemannZeta rho ≠ 0 := by
  intro hzero
  by_cases hone : 1 <= rho.re
  · exact (riemannZeta_ne_zero_of_one_le_re hone) hzero
  · have hlt : rho.re < 1 := lt_of_not_ge hone
    have hline : rho.re = (1 : Real) / 2 :=
      Zeta23.RH_implies_on_line hRH ⟨hzero, by linarith, hlt⟩
    linarith

/-- Under RH, the open-window zero set of the continued third-order golden germ
is the union of pulled-back zeta zeros on the pulled-back critical line and the
zeros of the canonical local factors. -/
theorem golden_continued_germ_window_zero_iff_of_rh
    (hRH : RiemannHypothesis) :
    let Kp : Complex -> Nat.Primes -> Complex := fun s p =>
      let x := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor s p
    let G3 : Complex -> Complex := fun s =>
      ∏' p : Nat.Primes, Kp s p
    ∀ continuedGerm :
        {s : Complex // 1 / Real.goldenRatio ^ 5 < s.re} -> Complex,
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
            G3 s.1)) ->
      ∀ s, 1 / (2 * Real.goldenRatio ^ 3) < s.1.re ->
        s.1.re < 1 / Real.goldenRatio ^ 2 ->
        (continuedGerm s = 0 ↔
          ((riemannZeta
              (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1) = 0 ∧
            s.1.re = 1 / (2 * Real.goldenRatio ^ 2)) ∨
          ∃ p : Nat.Primes, germLocalFactor s.1 p = 0)) := by
  dsimp only
  intro continuedGerm hformula s hlo hhi
  have hphi : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hphi2 : 0 < Real.goldenRatio ^ 2 := pow_pos hphi _
  have hphi3 : 0 < Real.goldenRatio ^ 3 := pow_pos hphi _
  have hspos : 0 < s.1.re :=
    lt_trans (by positivity : 0 < 1 / (2 * Real.goldenRatio ^ 3)) hlo
  have hphi_lt_two : Real.goldenRatio < 2 := by
    nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  have hlo_mul : 1 < s.1.re * (2 * Real.goldenRatio ^ 3) :=
    (div_lt_iff₀ (by positivity : 0 < 2 * Real.goldenRatio ^ 3)).mp hlo
  have hphi3_scaled : (1 : Real) / 2 < Real.goldenRatio ^ 3 * s.1.re := by
    nlinarith
  have hcoefficient_comparison :
      Real.goldenRatio * (Real.goldenRatio ^ 2 * s.1.re) <
        2 * (Real.goldenRatio ^ 2 * s.1.re) :=
    mul_lt_mul_of_pos_right hphi_lt_two (mul_pos hphi2 hspos)
  have htwo_phi2_scaled :
      (1 : Real) / 2 < 2 * Real.goldenRatio ^ 2 * s.1.re := by
    nlinarith
  have htwo_phi3_scaled :
      (1 : Real) / 2 < 2 * Real.goldenRatio ^ 3 * s.1.re := by
    nlinarith
  have hmixed_scaled :
      (1 : Real) / 2 <
        (2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3) * s.1.re := by
    have hextra : 0 < 2 * Real.goldenRatio ^ 2 * s.1.re := by positivity
    nlinarith
  have hphi3_ne :
      riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s.1) ≠ 0 :=
    zeta_ne_zero_of_rh_of_half_lt_re hRH (by
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] using hphi3_scaled)
  have htwo_phi2_ne :
      riemannZeta (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s.1) ≠ 0 :=
    zeta_ne_zero_of_rh_of_half_lt_re hRH (by
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] using htwo_phi2_scaled)
  have htwo_phi3_ne :
      riemannZeta (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s.1) ≠ 0 :=
    zeta_ne_zero_of_rh_of_half_lt_re hRH (by
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] using htwo_phi3_scaled)
  have hmixed_ne :
      riemannZeta
        ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
          Complex) * s.1)) ≠ 0 :=
    zeta_ne_zero_of_rh_of_half_lt_re hRH (by
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] using hmixed_scaled)
  have hprimary_line
      (hzero : riemannZeta
        (((Real.goldenRatio ^ 2 : Real) : Complex) * s.1) = 0) :
      s.1.re = 1 / (2 * Real.goldenRatio ^ 2) := by
    have hscaledPos :
        0 < ((((Real.goldenRatio ^ 2 : Real) : Complex) * s.1).re) := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      exact mul_pos hphi2 hspos
    have hscaledLt :
        ((((Real.goldenRatio ^ 2 : Real) : Complex) * s.1).re) < 1 := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      simpa only [mul_comm] using (lt_div_iff₀ hphi2).mp hhi
    have hline :
        ((((Real.goldenRatio ^ 2 : Real) : Complex) * s.1).re) =
          (1 : Real) / 2 :=
      Zeta23.RH_implies_on_line hRH ⟨hzero, hscaledPos, hscaledLt⟩
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at hline
    apply (eq_div_iff (by positivity : 2 * Real.goldenRatio ^ 2 ≠ 0)).mpr
    nlinarith
  have hzeroIff :=
    golden_third_residual_eq_zero_iff_exists_local_factor_zero s.1 s.property
  dsimp only at hzeroIff
  constructor
  · intro hzero
    rw [hformula s] at hzero
    rcases mul_eq_zero.mp hzero with hleft | hright
    · rcases mul_eq_zero.mp hleft with hab | htwoPhi2Inv
      · rcases mul_eq_zero.mp hab with hphi2zero | hphi3zero
        · exact Or.inl ⟨hphi2zero, hprimary_line hphi2zero⟩
        · exact (hphi3_ne hphi3zero).elim
      · exact ((inv_ne_zero htwo_phi2_ne) htwoPhi2Inv).elim
    · rcases mul_eq_zero.mp hright with hde | hG3zero
      · rcases mul_eq_zero.mp hde with htwoPhi3Inv | hmixedZero
        · exact ((inv_ne_zero htwo_phi3_ne) htwoPhi3Inv).elim
        · exact (hmixed_ne hmixedZero).elim
      · exact Or.inr (hzeroIff.1 hG3zero)
  · rintro (⟨hzeta, _⟩ | hlocal)
    · rw [hformula s, hzeta]
      simp
    · have hG3 := hzeroIff.2 hlocal
      rw [hformula s, hG3]
      simp

/- These checked examples provide the domain and premise-package witnesses used
by the non-hollowness review. The RH premise remains the explicit mathematical
input of the two conditional theorems. -/
example : Nonempty Complex := ⟨0⟩

example : Nonempty {s : Complex // 1 / Real.goldenRatio ^ 5 < s.re} := by
  refine ⟨⟨1, ?_⟩⟩
  have hpow : (1 : Real) < Real.goldenRatio ^ 5 :=
    one_lt_pow₀ Real.one_lt_goldenRatio (by norm_num)
  simpa using (inv_lt_one_of_one_lt₀ hpow)

example :
    let Kp : Complex -> Nat.Primes -> Complex := fun s p =>
      let x := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor s p
    let G3 : Complex -> Complex := fun s =>
      ∏' p : Nat.Primes, Kp s p
    ∃ continuedGerm :
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
  have hthird := golden_germ_third_order_factorization
  dsimp only at hthird ⊢
  exact hthird.2.exists

#print axioms golden_continued_germ_window_zero_on_line_of_rh
#print axioms golden_third_residual_eq_zero_iff_exists_local_factor_zero
#print axioms golden_continued_germ_window_zero_iff_of_rh

end

end D5.S3.Analytic.GermWindow.GoldenGermThirdOrderWindowZeroCriterion
