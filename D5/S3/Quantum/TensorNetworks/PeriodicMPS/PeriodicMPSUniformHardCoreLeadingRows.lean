/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreLeadingRows
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreLeadingRows
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreAnalyticPartner, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreJetGerm]
   utility: none
   digest: The cross-multiplied observation rows agree at leading order with the normalized first and second coefficients up to the square of the witness mass. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreAnalyticPartner
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreJetGerm
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Leading coefficients of the cross-multiplied hard-core observations. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreLeadingRows

open PeriodicMPSAnalyticPartnerPolynomial
open PeriodicMPSUniformHardCoreAnalyticPartner
open PeriodicMPSUniformHardCoreFirstJet (witness regularReadout)
open PeriodicMPSUniformHardCoreFoldCurvature (nullSlope)
open PeriodicMPSUniformHardCoreQuarticSign (Z denominator_factors)
open PeriodicMPSUniformHardCoreJetElimination (Path)
open PeriodicMPSUniformHardCoreNormalizedJet (ratio normalizedCoeff massCoeff rawCoeff)
open Polynomial Filter
open scoped Matrix Topology

open private mass_eval value_eval component_eq_div difference_eval from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreAnalyticPartner
open private twoMass from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreFirstJet
open private realMass realEntry coeff_realMass coeff_realEntry eval_realPolynomial project_apply
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreJetGerm

noncomputable section


/-- The parameters with the regular imaginary slopes fixed at prescribed free slope. -/
def leadingParameters (n : ℕ) (t : ℝ) (v : RealRegular) : Parameters :=
  (![-nullSlope n * t, 1, 0], v, t)

/-- The corresponding polynomial jet with no terms beyond quadratic. -/
def leadingPath (t : ℝ) (v : RealRegular) : Path :=
  ⟨t, v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0, 0⟩

@[simp] theorem leadingParameters_one (n : ℕ) :
    leadingParameters n 1 0 = original (nullSlope n) := by
  simp [leadingParameters, original]

@[simp] theorem leadingPath_one : leadingPath 1 0 = PeriodicMPSUniformHardCoreJetElimination.original := rfl

private theorem coordinates_leadingPath (n : ℕ) (t : ℝ) (v : RealRegular) (ε : ℝ) :
    PeriodicMPSUniformHardCoreNormalizedJet.coordinates n (leadingPath t v) ε = chart ε (leadingParameters n t v) := by
  funext i
  fin_cases i <;>
    simp [PeriodicMPSUniformHardCoreNormalizedJet.coordinates, PeriodicMPSUniformHardCoreHigherJet.pathCoordinate,
      PeriodicMPSUniformHardCoreHigherJet.pathTerms, PeriodicMPSUniformHardCoreNormalizedJet.parameters, leadingPath,
      leadingParameters, nullSlope, chart, imagDirection, witness, ratio,
      Fin.sum_univ_succ, Complex.I_sq] <;> ring

private def specialize (p : Family) (w : Parameters) : ℝ[X] :=
  p.map (Pi.evalRingHom _ w)

@[simp] private theorem coeff_specialize (p : Family) (w : Parameters) (k : ℕ) :
    (specialize p w).coeff k = p.coeff k w := by simp [specialize]

@[simp] private theorem eval_specialize (p : Family) (w : Parameters) (ε : ℝ) :
    (specialize p w).eval ε = evaluate p ε w := by simp [specialize, evaluate, eval_map]

private theorem specialize_mass (s : ℕ) (t : ℝ) (v : RealRegular) :
    specialize (massFamily (s + 4)) (leadingParameters (s + 4) t v) =
      realMass (s + 4) (leadingPath t v) := by
  apply Polynomial.funext
  intro ε
  rw [eval_specialize, mass_eval, realMass, eval_realPolynomial, PeriodicMPSUniformHardCoreNormalizedJet.mass_eval,
    project_apply, coordinates_leadingPath]
  rfl

private theorem specialize_value (s : ℕ) (t : ℝ) (v : RealRegular) (i : Rows) :
    specialize (valueFamily i (s + 4)) (leadingParameters (s + 4) t v) =
      realEntry (rowData i).1 (s + 4) (leadingPath t v) (rowData i).2 := by
  apply Polynomial.funext
  intro ε
  rw [eval_specialize, value_eval, realEntry, eval_realPolynomial, PeriodicMPSUniformHardCoreNormalizedJet.numerator_eval,
    project_apply, coordinates_leadingPath]
  cases (rowData i).1 <;> rfl

private theorem specialize_difference (s : ℕ) (w : Parameters) (i : Rows) :
    specialize (difference s (nullSlope (s + 4)) i) w =
      specialize (valueFamily i (s + 4)) w *
        specialize (massFamily (s + 4)) (original (nullSlope (s + 4))) -
      specialize (valueFamily i (s + 4)) (original (nullSlope (s + 4))) *
        specialize (massFamily (s + 4)) w := by
  apply Polynomial.funext
  intro ε
  simp only [eval_specialize, eval_sub, eval_mul, difference_eval]

theorem witnessMass_ne_zero {n : ℕ} (hn : 7 ≤ n) : Z n ≠ 0 :=
  (denominator_factors hn).2.1.ne'

private theorem massCoeff_zero (n : ℕ) (hn : 7 ≤ n) (x : Path) : massCoeff n x 0 = Z n := by
  rw [PeriodicMPSUniformHardCoreNormalizedJet.mass_zero n hn, Z, PeriodicMPSUniformHardCoreNormalizedJet.F_eq_ratio_mul n hn]
  ring

private theorem mass_at_zero (s : ℕ) (hs : 3 ≤ s) (w : Parameters) :
    evaluate (massFamily (s + 4)) 0 w = Z (s + 4) := by
  have h (u : Parameters) : evaluate (massFamily (s + 4)) 0 w =
      evaluate (massFamily (s + 4)) 0 u := by simp only [mass_eval, chart_zero]
  rw [h (leadingParameters (s + 4) 1 0), ← eval_specialize, specialize_mass,
    ← coeff_zero_eq_eval_zero, coeff_realMass, massCoeff_zero _ (by omega)]

private theorem cross_coeff_two (n : ℕ) (hn : 7 ≤ n) (x y : Path) (row : Fin 8) :
    (realEntry false n x row * realMass n y - realEntry false n y row * realMass n x).coeff 2 =
      Z n ^ 2 * (normalizedCoeff false n x row 2 - normalizedCoeff false n y row 2) := by
  have hz := witnessMass_ne_zero hn
  have hr : rawCoeff false n x row 0 = rawCoeff false n y row 0 :=
    (PeriodicMPSUniformHardCoreNormalizedJet.raw_zero n hn x row).1.trans (PeriodicMPSUniformHardCoreNormalizedJet.raw_zero n hn y row).1.symm
  norm_num [coeff_sub, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ,
    coeff_realEntry, coeff_realMass, massCoeff_zero n hn, PeriodicMPSUniformHardCoreNormalizedJet.mass_one n hn, hr,
    mul_zero, add_zero, PeriodicMPSUniformHardCoreNormalizedJet.normalized_two false n hn, PeriodicMPSUniformHardCoreNormalizedJet.normalized_zero]
  field_simp
  ring

/-- Each rescaled real row is its literal normalized jet difference times the squared mass. -/
theorem real_leading_row (s : ℕ) (hs : 3 ≤ s) (t : ℝ) (v : RealRegular)
    (i : Fin 4 ⊕ Unit) :
    let n := s + 4
    let row := (rowData (.inr i)).2
    (difference s (nullSlope n) (.inr i)).coeff 2 (leadingParameters n t v) =
      Z n ^ 2 * (normalizedCoeff false n (leadingPath t v) row 2 -
        normalizedCoeff false n PeriodicMPSUniformHardCoreJetElimination.original row 2) := by
  have hi : (rowData (.inr i)).1 = false := by cases i <;> rfl
  dsimp only
  rw [← coeff_specialize, specialize_difference, ← leadingParameters_one,
    specialize_value, specialize_value, specialize_mass, specialize_mass, hi, leadingPath_one]
  exact cross_coeff_two (s + 4) (by omega) _ _ _

/-- On the prescribed slope family the imaginary leading rows also agree
with the first coefficients of the checked formal normalized jet. -/
theorem imag_leading_row_on_path (s : ℕ) (hs : 3 ≤ s) (t : ℝ) (v : RealRegular)
    (i : Fin 3) :
    let n := s + 4
    let row := (rowData (.inl i)).2
    (difference s (nullSlope n) (.inl i)).coeff 1 (leadingParameters n t v) =
      Z n ^ 2 * (normalizedCoeff true n (leadingPath t v) row 1 -
        normalizedCoeff true n PeriodicMPSUniformHardCoreJetElimination.original row 1) := by
  have hn : 7 ≤ s + 4 := by omega
  dsimp only
  rw [← coeff_specialize, specialize_difference, ← leadingParameters_one,
    specialize_value, specialize_value, specialize_mass, specialize_mass, leadingPath_one]
  norm_num [coeff_sub, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, coeff_realEntry, coeff_realMass, massCoeff_zero _ hn,
    PeriodicMPSUniformHardCoreNormalizedJet.mass_one _ hn,
    PeriodicMPSUniformHardCoreNormalizedJet.normalized_one true _ hn, rowData,
    (PeriodicMPSUniformHardCoreNormalizedJet.raw_first _ hn _ _).2]

private theorem hasDerivAt_chart (w : Parameters) :
    HasDerivAt (fun ε : ℝ => chart ε w)
      (fun i => (imagDirection w i : ℂ) * Complex.I) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  have h := ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_id (0 : ℝ)).const_mul (imagDirection w i))).mul_const Complex.I)
  have hr := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0
    (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (w.2.1 i))
  simpa [chart, Function.comp_def, Pi.add_apply] using ((hasDerivAt_const (0 : ℝ) (witness i)).fun_add h).fun_add hr

private theorem hasDerivAt_imag_readout (s : ℕ) (hs : 3 ≤ s) (w : Parameters) :
    HasDerivAt (fun ε : ℝ => (regularReadout s (chart ε w)).2)
      (PeriodicMPSUniformHardCoreFirstJet.imagBlock (s + 4) *ᵥ w.1 + w.2.2 • PeriodicMPSUniformHardCoreFirstJet.imagA (s + 4)) 0 := by
  have hd := ((PeriodicMPSUniformHardCoreFirstJet.regularReadout_contDiffAt s hs).differentiableAt
    (by decide)).hasFDerivAt
  have h := (hd.comp_hasDerivAt_of_eq 0 (hasDerivAt_chart w) (chart_zero w).symm)
    |>.hasFDerivAt |>.snd |>.hasDerivAt
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
  let u : PeriodicMPSUniformHardCoreFirstJet.Coord :=
    fun i => (imagDirection w i : ℂ) * Complex.I
  change HasDerivAt (fun ε => (regularReadout s (chart ε w)).2)
    (fderiv ℝ (regularReadout s) witness u).2 0 at h
  rw [PeriodicMPSUniformHardCoreFirstJet.fderiv_regularReadout_apply s hs] at h
  have hu (i : Fin 4) : (u i).im = imagDirection w i := by
    simp [u, Complex.mul_im]
  have hη : (![(u 1).im, (u 2).im, (u 3).im] : Imaginary) = w.1 := by
    funext i
    fin_cases i <;> simp [hu, imagDirection]
  change HasDerivAt (fun ε => (regularReadout s (chart ε w)).2)
    (PeriodicMPSUniformHardCoreFirstJet.imagBlock (s + 4) *ᵥ
      ![(u 1).im, (u 2).im, (u 3).im] +
      (u 0).im • PeriodicMPSUniformHardCoreFirstJet.imagA (s + 4)) 0 at h
  rw [hη, hu] at h
  exact h

/-- The normalized imaginary first coefficient for an arbitrary chart path. -/
def imagLeading (n : ℕ) (w : Parameters) : Imaginary :=
  PeriodicMPSUniformHardCoreFirstJet.imagBlock n *ᵥ w.1 + w.2.2 • PeriodicMPSUniformHardCoreFirstJet.imagA n

/-- For arbitrary chart parameters the literal imaginary rows carry the same
squared witness mass as the real rows. -/
theorem imag_leading_row (s : ℕ) (hs : 3 ≤ s) (w : Parameters) (i : Fin 3) :
    let n := s + 4
    (difference s (nullSlope n) (.inl i)).coeff 1 w =
      Z n ^ 2 * (imagLeading n w i - imagLeading n (original (nullSlope n)) i) := by
  let n := s + 4
  let w₁ := original (nullSlope n)
  let p := specialize (difference s (nullSlope n) (.inl i)) w
  let m (v : Parameters) := specialize (massFamily n) v
  let r (v : Parameters) (ε : ℝ) := (regularReadout s (chart ε v)).2 i
  have hm₀ (v : Parameters) : (m v).eval 0 = Z n := by
    simpa only [m, eval_specialize] using mass_at_zero s hs v
  have hn : 7 ≤ n := by omega
  have hm (v : Parameters) : ∀ᶠ ε in 𝓝 (0 : ℝ), (m v).eval ε ≠ 0 :=
    (m v).continuous.continuousAt.eventually_ne (hm₀ v ▸ witnessMass_ne_zero hn)
  have hr₀ (v : Parameters) : r v 0 = r w₁ 0 := by simp [r]
  have hr (v : Parameters) :
      HasDerivAt (r v) (imagLeading n v i) 0 :=
    (ContinuousLinearMap.proj i : Imaginary →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0
      (hasDerivAt_imag_readout s hs v)
  have hrdiv (v : Parameters) (ε : ℝ) :
      r v ε = (specialize (valueFamily (.inl i) n) v).eval ε / (m v).eval ε := by
    dsimp only [r]
    have h := component_eq_div (.inl i) s ε v
    fin_cases i <;>
      simpa [m, n, eval_specialize, regularReadout, rowData] using h
  have he : (fun ε => p.eval ε) =ᶠ[𝓝 0]
      (fun ε => (m w).eval ε * (m w₁).eval ε * (r w ε - r w₁ ε)) := by
    filter_upwards [hm w, hm w₁] with ε h₀ h₁
    dsimp only [p]
    rw [specialize_difference, eval_sub, eval_mul, eval_mul, hrdiv, hrdiv]
    field_simp
    ring
  have h := (((m w).hasDerivAt 0).mul ((m w₁).hasDerivAt 0)).mul ((hr w).sub (hr w₁))
  have H := (p.hasDerivAt 0).unique (h.congr_of_eventuallyEq he)
  simpa [p, hm₀, hr₀, ← coeff_zero_eq_eval_zero, coeff_derivative, pow_two] using H

#print axioms real_leading_row
#print axioms imag_leading_row_on_path
#print axioms imag_leading_row

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreLeadingRows
