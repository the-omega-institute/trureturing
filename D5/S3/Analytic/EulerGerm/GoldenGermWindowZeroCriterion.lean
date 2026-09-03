/- GID: D5/S3/Analytic/EulerGerm/GoldenGermWindowZeroCriterion
   generality: G
   mirror-B: D5/B/S3/Analytic/EulerGerm/GoldenGermWindowZeroCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: RH confines surviving golden-window germ zeros to the pulled-back critical line. -/

import D5.S3.Weil.ZetaCore.Statement
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Complex

namespace D5.S3.Analytic.EulerGerm.GoldenGermWindowZeroCriterion

private lemma zeta_zero_false_of_rh_of_half_lt_re
    (hRH : RiemannHypothesis) {rho : Complex}
    (hzero : riemannZeta rho = 0) (hhalf : (1 : Real) / 2 < rho.re) : False := by
  by_cases hone : 1 <= rho.re
  · exact (riemannZeta_ne_zero_of_one_le_re hone) hzero
  · have hlt : rho.re < 1 := lt_of_not_ge hone
    have hline : rho.re = (1 : Real) / 2 :=
      Zeta23.RH_implies_on_line hRH <| by
        exact ⟨hzero, by linarith, hlt⟩
    linarith

/-- Assuming RH, a zero of the continued golden germ inside the open window lies
on the pulled-back critical line whenever the arbitrary residual factor survives. -/
theorem golden_window_zero_on_line_of_rh (hRH : RiemannHypothesis) (G : Complex -> Complex)
    (s : Complex)
    (hlo : 1 / (2 * Real.goldenRatio ^ 3) < s.re)
    (hhi : s.re < 1 / Real.goldenRatio ^ 2)
    (hzero : riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s) *
        riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s) *
        (riemannZeta (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s))⁻¹ *
        ((riemannZeta (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s))⁻¹ *
          riemannZeta ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
            Complex) * s)) * G s) = 0)
    (hG : G s ≠ 0) : s.re = 1 / (2 * Real.goldenRatio ^ 2) := by
  have hphi : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hphi2 : 0 < Real.goldenRatio ^ 2 := pow_pos hphi _
  have hphi3 : 0 < Real.goldenRatio ^ 3 := pow_pos hphi _
  have hspos : 0 < s.re :=
    lt_trans (by positivity : 0 < 1 / (2 * Real.goldenRatio ^ 3)) hlo
  have hphi_lt_two : Real.goldenRatio < 2 := by
    nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  have hlo_mul : 1 < s.re * (2 * Real.goldenRatio ^ 3) :=
    (div_lt_iff₀ (by positivity : 0 < 2 * Real.goldenRatio ^ 3)).mp hlo
  have hphi3_scaled : (1 : Real) / 2 < Real.goldenRatio ^ 3 * s.re := by
    nlinarith
  have hcoefficient_comparison :
      Real.goldenRatio * (Real.goldenRatio ^ 2 * s.re) <
        2 * (Real.goldenRatio ^ 2 * s.re) :=
    mul_lt_mul_of_pos_right hphi_lt_two (mul_pos hphi2 hspos)
  have htwo_phi2_scaled :
      (1 : Real) / 2 < 2 * Real.goldenRatio ^ 2 * s.re := by
    nlinarith
  have htwo_phi3_scaled :
      (1 : Real) / 2 < 2 * Real.goldenRatio ^ 3 * s.re := by
    nlinarith
  have hmixed_scaled :
      (1 : Real) / 2 <
        (2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3) * s.re := by
    have hextra : 0 < 2 * Real.goldenRatio ^ 2 * s.re := by positivity
    nlinarith
  rcases mul_eq_zero.mp hzero with hleft | hright
  · rcases mul_eq_zero.mp hleft with hab | htwoPhi2Inv
    · rcases mul_eq_zero.mp hab with hphi2zero | hphi3zero
      · have hscaledPos :
            0 < ((((Real.goldenRatio ^ 2 : Real) : Complex) * s).re) := by
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
          exact mul_pos hphi2 hspos
        have hscaledLt :
            ((((Real.goldenRatio ^ 2 : Real) : Complex) * s).re) < 1 := by
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
          simpa only [mul_comm] using (lt_div_iff₀ hphi2).mp hhi
        have hline :
            ((((Real.goldenRatio ^ 2 : Real) : Complex) * s).re) =
              (1 : Real) / 2 :=
          Zeta23.RH_implies_on_line hRH ⟨hphi2zero, hscaledPos, hscaledLt⟩
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          sub_zero] at hline
        apply (eq_div_iff (by positivity : 2 * Real.goldenRatio ^ 2 ≠ 0)).mpr
        nlinarith
      · apply False.elim
        apply zeta_zero_false_of_rh_of_half_lt_re hRH hphi3zero
        simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          sub_zero] using hphi3_scaled
    · apply False.elim
      apply zeta_zero_false_of_rh_of_half_lt_re hRH (inv_eq_zero.mp htwoPhi2Inv)
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero] using htwo_phi2_scaled
  · rcases mul_eq_zero.mp hright with hde | hGzero
    · rcases mul_eq_zero.mp hde with htwoPhi3Inv | hmixedZero
      · apply False.elim
        apply zeta_zero_false_of_rh_of_half_lt_re hRH (inv_eq_zero.mp htwoPhi3Inv)
        simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          sub_zero] using htwo_phi3_scaled
      · apply False.elim
        apply zeta_zero_false_of_rh_of_half_lt_re hRH hmixedZero
        simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          sub_zero] using hmixed_scaled
    · exact (hG hGzero).elim

/-- If the residual survives at every pulled-back right-half-strip zeta zero,
then golden-window confinement conditionally excludes every such zeta zero. -/
theorem golden_window_zero_right_half_strip_converse
    (G : Complex -> Complex)
    (hResidual : forall rho : Complex, riemannZeta rho = 0 ->
      (1 : Real) / 2 < rho.re -> rho.re < 1 ->
      G (rho / ((Real.goldenRatio ^ 2 : Real) : Complex)) ≠ 0)
    (hConfinement : forall s : Complex,
      1 / (2 * Real.goldenRatio ^ 3) < s.re ->
      s.re < 1 / Real.goldenRatio ^ 2 ->
      riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s) *
        riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s) *
        (riemannZeta (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s))⁻¹ *
        ((riemannZeta (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s))⁻¹ *
          riemannZeta ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
            Complex) * s)) * G s) = 0 ->
      G s ≠ 0 -> s.re = 1 / (2 * Real.goldenRatio ^ 2)) :
    forall rho : Complex, riemannZeta rho = 0 ->
      (1 : Real) / 2 < rho.re -> rho.re < 1 -> False := by
  intro rho hzero hhalf hlt
  have hphi : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hphi2 : 0 < Real.goldenRatio ^ 2 := pow_pos hphi _
  have hphi3 : 0 < Real.goldenRatio ^ 3 := pow_pos hphi _
  have hphi2_lt_phi3 : Real.goldenRatio ^ 2 < Real.goldenRatio ^ 3 := by
    calc
      Real.goldenRatio ^ 2 < Real.goldenRatio ^ 2 * Real.goldenRatio :=
        (lt_mul_iff_one_lt_right hphi2).mpr Real.one_lt_goldenRatio
      _ = Real.goldenRatio ^ 3 := by ring
  let s : Complex := rho / ((Real.goldenRatio ^ 2 : Real) : Complex)
  have hscale : ((Real.goldenRatio ^ 2 : Real) : Complex) * s = rho := by
    dsimp [s]
    simpa only [mul_div_assoc] using
      (mul_div_cancel_left₀ rho <|
        Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 Real.goldenRatio_ne_zero))
  have hscaleRe : Real.goldenRatio ^ 2 * s.re = rho.re := by
    have := congrArg Complex.re hscale
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] using this
  have hsLowerLine : 1 / (2 * Real.goldenRatio ^ 2) < s.re := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.goldenRatio ^ 2)).mpr
    nlinarith
  have hsLowerWindow : 1 / (2 * Real.goldenRatio ^ 3) < s.re := by
    have hden : 2 * Real.goldenRatio ^ 2 < 2 * Real.goldenRatio ^ 3 := by
      nlinarith
    exact (one_div_lt_one_div_of_lt (by positivity) hden).trans hsLowerLine
  have hsUpper : s.re < 1 / Real.goldenRatio ^ 2 := by
    apply (lt_div_iff₀ hphi2).mpr
    nlinarith
  have hProductZero :
      riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s) *
        riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s) *
        (riemannZeta (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s))⁻¹ *
        ((riemannZeta (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s))⁻¹ *
          riemannZeta ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
            Complex) * s)) * G s) = 0 := by
    rw [hscale, hzero]
    simp
  have hsLine := hConfinement s hsLowerWindow hsUpper hProductZero
    (hResidual rho hzero hhalf hlt)
  have hlineScale :
      Real.goldenRatio ^ 2 * (1 / (2 * Real.goldenRatio ^ 2)) = (1 : Real) / 2 := by
    field_simp
  rw [hsLine, hlineScale] at hscaleRe
  linarith

/- The following checked examples provide the non-hollowness witnesses used by
the deposit review. The first premise package is inhabited relative to exactly
the mathematical inputs it needs: RH and a nontrivial zeta zero. -/
example : Nonempty Complex := ⟨0⟩

example (hRH : RiemannHypothesis) {rho : Complex}
    (hrho : Zeta23.IsNontrivialZero rho) :
    ∃ (G : Complex -> Complex) (s : Complex),
      1 / (2 * Real.goldenRatio ^ 3) < s.re ∧
      s.re < 1 / Real.goldenRatio ^ 2 ∧
      riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s) *
          riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s) *
          (riemannZeta (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s))⁻¹ *
          ((riemannZeta (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s))⁻¹ *
            riemannZeta ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
              Complex) * s)) * G s) = 0 ∧
      G s ≠ 0 := by
  have hphi : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hphi2 : 0 < Real.goldenRatio ^ 2 := pow_pos hphi _
  have hphi3 : 0 < Real.goldenRatio ^ 3 := pow_pos hphi _
  have hphi2_lt_phi3 : Real.goldenRatio ^ 2 < Real.goldenRatio ^ 3 := by
    calc
      Real.goldenRatio ^ 2 < Real.goldenRatio ^ 2 * Real.goldenRatio :=
        (lt_mul_iff_one_lt_right hphi2).mpr Real.one_lt_goldenRatio
      _ = Real.goldenRatio ^ 3 := by ring
  let s : Complex := rho / ((Real.goldenRatio ^ 2 : Real) : Complex)
  have hscale : ((Real.goldenRatio ^ 2 : Real) : Complex) * s = rho := by
    dsimp [s]
    simpa only [mul_div_assoc] using
      (mul_div_cancel_left₀ rho <|
        Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 Real.goldenRatio_ne_zero))
  have hscaleRe : Real.goldenRatio ^ 2 * s.re = rho.re := by
    have := congrArg Complex.re hscale
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] using this
  have hline : rho.re = (1 : Real) / 2 :=
    Zeta23.RH_implies_on_line hRH hrho
  have hsLine : s.re = 1 / (2 * Real.goldenRatio ^ 2) := by
    apply (eq_div_iff (by positivity : 2 * Real.goldenRatio ^ 2 ≠ 0)).mpr
    nlinarith
  refine ⟨fun _ => 1, s, ?_, ?_, ?_, by norm_num⟩
  · rw [hsLine]
    have hden : 2 * Real.goldenRatio ^ 2 < 2 * Real.goldenRatio ^ 3 := by
      nlinarith
    exact one_div_lt_one_div_of_lt (by positivity) hden
  · rw [hsLine]
    have hden : Real.goldenRatio ^ 2 < 2 * Real.goldenRatio ^ 2 := by
      nlinarith
    exact one_div_lt_one_div_of_lt hphi2 hden
  · rw [hscale, hrho.1]
    simp

/- Under RH, the constant residual simultaneously satisfies the conditional
residual-survival premise and the window-confinement premise of the converse. -/
example (hRH : RiemannHypothesis) :
    ∃ G : Complex -> Complex,
      (forall rho : Complex, riemannZeta rho = 0 ->
        (1 : Real) / 2 < rho.re -> rho.re < 1 ->
        G (rho / ((Real.goldenRatio ^ 2 : Real) : Complex)) ≠ 0) ∧
      (forall s : Complex,
        1 / (2 * Real.goldenRatio ^ 3) < s.re ->
        s.re < 1 / Real.goldenRatio ^ 2 ->
        riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s) *
          riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s) *
          (riemannZeta (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s))⁻¹ *
          ((riemannZeta (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s))⁻¹ *
            riemannZeta ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
              Complex) * s)) * G s) = 0 ->
        G s ≠ 0 -> s.re = 1 / (2 * Real.goldenRatio ^ 2)) := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro rho hzero hhalf hlt
    norm_num
  · intro s hlo hhi hzero hG
    exact golden_window_zero_on_line_of_rh hRH (fun _ => 1) s hlo hhi hzero hG

#print axioms golden_window_zero_on_line_of_rh
#print axioms golden_window_zero_right_half_strip_converse

end D5.S3.Analytic.EulerGerm.GoldenGermWindowZeroCriterion
