/- GID: D5/S3/Weil/ZetaLinear/HorizonThermodynamicAsymptotics
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaLinear/HorizonThermodynamicAsymptotics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The single-defect horizon coordinates have exact first-order asymptotics. -/

import D5.S3.Weil.ZetaLinear.HorizonFreeEnergyDivergence
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/- Library-search audit trail (2026-09-01):
   * The target atom remains residual-open with empty `coverage_gids`, and its
     atom id occurs in no formalization receipt on `origin/dev`.
   * `HorizonFreeEnergyDivergence` proves the determinant identities and the
     negative-log divergence, but contains neither the squeezing coordinate,
     occupation number, nor any of the three stated asymptotic expansions.
   * `BoundaryArtanhDivergence` proves an unnormalized artanh boundary limit,
     and `DoubleArtanhBounds` gives rational bounds. Neither gives the exact
     first-order corrections below.
   * Pinned Mathlib supplies `Real.artanh_eq_half_log`,
     `Real.cosh_artanh`, `Real.log_sqrt`, `Real.hasDerivAt_log`, and
     `HasDerivAt.tendsto_slope_zero_right`; these are reused directly.
   * Installed non-Mathlib Lean packages have no declaration matching horizon
     thermodynamic identities or artanh boundary asymptotics. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaLinear.HorizonThermodynamicAsymptotics

open Filter Set Topology
open D5.S3.Weil.ZetaLinear.HorizonFreeEnergyDivergence

/-- The squeezing coordinate of an interior single-defect mode. -/
def squeezeParameter (delta omega : ℝ) : ℝ :=
  Real.artanh (omega / delta)

/-- The occupation number associated with an interior single-defect mode. -/
def occupationNumber (delta omega : ℝ) : ℝ :=
  omega ^ 2 / (delta ^ 2 - omega ^ 2)

/-- In the strict horizon interior, the free energy has both the squeezing
and occupation-number representations from the source. -/
theorem horizon_free_energy_eq_log_coordinates
    (delta omega : ℝ) (hdelta : 0 < delta) (homega : |omega| < delta) :
    horizonFreeEnergy delta omega =
        2 * Real.log (Real.cosh (squeezeParameter delta omega)) ∧
      horizonFreeEnergy delta omega =
        Real.log (1 + occupationNumber delta omega) := by
  have hdeltaNe : delta ≠ 0 := ne_of_gt hdelta
  have hratio : omega / delta ∈ Ioo (-1 : ℝ) 1 := by
    rw [mem_Ioo, div_lt_iff₀ hdelta, lt_div_iff₀ hdelta]
    constructor <;> linarith [le_abs_self omega, neg_le_abs omega]
  have hDetPos : 0 < horizonDeterminant delta omega :=
    (horizon_determinant_pos_iff_abs_lt delta omega hdeltaNe).2
      (by simpa [abs_of_pos hdelta] using homega)
  constructor
  · rw [squeezeParameter, Real.cosh_artanh hratio]
    unfold horizonFreeEnergy
    rw [one_div, Real.log_inv]
    change -Real.log (horizonDeterminant delta omega) =
      2 * -Real.log (Real.sqrt (horizonDeterminant delta omega))
    rw [Real.log_sqrt hDetPos.le]
    ring
  · have hGap : 0 < delta ^ 2 - omega ^ 2 := by
      rw [sub_pos, sq_lt_sq]
      simpa [abs_of_pos hdelta] using homega
    have hReciprocal :
        1 + occupationNumber delta omega =
          (horizonDeterminant delta omega)⁻¹ := by
      rw [horizon_determinant_eq_div delta omega hdeltaNe]
      unfold occupationNumber
      field_simp [hdeltaNe, ne_of_gt hGap]
      <;> ring
    rw [hReciprocal]
    unfold horizonFreeEnergy
    rw [Real.log_inv]

/-- Exact correction to the leading artanh boundary term. Positivity and the
upper bound keep every denominator and logarithm in its analytic domain. -/
theorem squeeze_parameter_near_horizon
    (delta epsilon : ℝ) (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hepsilonLt : epsilon < 2 * delta) :
    squeezeParameter delta (delta - epsilon) =
      (1 / 2 : ℝ) * Real.log (2 * delta / epsilon) +
        (1 / 2 : ℝ) * Real.log (1 - epsilon / (2 * delta)) := by
  have hdeltaNe : delta ≠ 0 := ne_of_gt hdelta
  have hepsilonNe : epsilon ≠ 0 := ne_of_gt hepsilon
  have hratio : (delta - epsilon) / delta ∈ Icc (-1 : ℝ) 1 := by
    rw [mem_Icc, le_div_iff₀ hdelta, div_le_iff₀ hdelta]
    constructor <;> linarith
  have hfirst : 0 < 2 * delta / epsilon := div_pos (by positivity) hepsilon
  have hsecond : 0 < 1 - epsilon / (2 * delta) := by
    rw [sub_pos, div_lt_one (by positivity)]
    exact hepsilonLt
  have hratioEq :
      (1 + (delta - epsilon) / delta) /
          (1 - (delta - epsilon) / delta) =
        (2 * delta / epsilon) * (1 - epsilon / (2 * delta)) := by
    field_simp [hdeltaNe, hepsilonNe]
    <;> ring
  rw [squeezeParameter, Real.artanh_eq_half_log hratio, hratioEq,
    Real.log_mul (ne_of_gt hfirst) (ne_of_gt hsecond)]
  ring

/-- The occupation number differs from its pole term by an exact rational
correction, whose boundary value is `-3/4`. -/
theorem occupation_number_near_horizon
    (delta epsilon : ℝ) (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hepsilonLt : epsilon < 2 * delta) :
    occupationNumber delta (delta - epsilon) - delta / (2 * epsilon) =
      (2 * epsilon - 3 * delta) / (2 * (2 * delta - epsilon)) := by
  have hGap : 0 < delta ^ 2 - (delta - epsilon) ^ 2 := by
    nlinarith [mul_pos hepsilon (sub_pos.mpr hepsilonLt)]
  have hTwoDeltaEpsilon : 2 * delta - epsilon ≠ 0 :=
    ne_of_gt (sub_pos.mpr hepsilonLt)
  have hDenominator : delta * 2 - epsilon ≠ 0 := by
    linarith
  have hFactor :
      delta ^ 2 - (delta - epsilon) ^ 2 = epsilon * (2 * delta - epsilon) := by
    ring
  unfold occupationNumber
  rw [hFactor]
  field_simp [ne_of_gt hepsilon, hTwoDeltaEpsilon, hDenominator]
  <;> ring

/-- Exact correction to the leading negative-log boundary term. -/
theorem horizon_free_energy_near_horizon
    (delta epsilon : ℝ) (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hepsilonLt : epsilon < 2 * delta) :
    horizonFreeEnergy delta (delta - epsilon) -
        Real.log (delta / (2 * epsilon)) =
      -Real.log (1 - epsilon / (2 * delta)) := by
  have hdeltaNe : delta ≠ 0 := ne_of_gt hdelta
  have hepsilonNe : epsilon ≠ 0 := ne_of_gt hepsilon
  have hfirst : 0 < 2 * epsilon / delta := div_pos (by positivity) hdelta
  have hsecond : 0 < 1 - epsilon / (2 * delta) := by
    rw [sub_pos, div_lt_one (by positivity)]
    exact hepsilonLt
  have hFactor :
      horizonDeterminant delta (delta - epsilon) =
        (2 * epsilon / delta) * (1 - epsilon / (2 * delta)) := by
    unfold horizonDeterminant
    field_simp [hdeltaNe]
    <;> ring
  have hInverse : delta / (2 * epsilon) = (2 * epsilon / delta)⁻¹ := by
    field_simp [hdeltaNe, hepsilonNe]
  rw [horizonFreeEnergy, hFactor,
    Real.log_mul (ne_of_gt hfirst) (ne_of_gt hsecond), hInverse,
    Real.log_inv]
  ring

private theorem log_correction_normalized_limit (delta : ℝ) (hdelta : 0 < delta) :
    Tendsto (fun epsilon : ℝ =>
        Real.log (1 - epsilon / (2 * delta)) / epsilon)
      (nhdsWithin 0 (Ioi 0)) (nhds (-1 / (2 * delta))) := by
  have hInner :
      HasDerivAt (fun epsilon : ℝ => 1 - epsilon / (2 * delta))
        (-1 / (2 * delta)) 0 := by
    simpa only [id_eq, neg_div] using
      ((hasDerivAt_id 0).div_const (2 * delta)).const_sub (1 : ℝ)
  have hLog :
      HasDerivAt (fun epsilon : ℝ =>
          Real.log (1 - epsilon / (2 * delta)))
        (-1 / (2 * delta)) 0 := by
    convert hInner.log
      (by norm_num : 1 - (0 : ℝ) / (2 * delta) ≠ 0) using 1 <;> ring
  simpa [div_eq_mul_inv, mul_comm] using hLog.tendsto_slope_zero_right

/-- The artanh remainder is first order, with exact normalized coefficient
`-1/(4*delta)`. This strengthens the source's `O(epsilon)` statement. -/
theorem squeeze_parameter_normalized_error_limit (delta : ℝ) (hdelta : 0 < delta) :
    Tendsto (fun epsilon : ℝ =>
        (squeezeParameter delta (delta - epsilon) -
            (1 / 2 : ℝ) * Real.log (2 * delta / epsilon)) / epsilon)
      (nhdsWithin 0 (Ioi 0)) (nhds (-1 / (4 * delta))) := by
  have hLimit := (tendsto_const_nhds.mul
    (log_correction_normalized_limit delta hdelta) :
      Tendsto (fun epsilon : ℝ =>
          (1 / 2 : ℝ) *
            (Real.log (1 - epsilon / (2 * delta)) / epsilon))
        (nhdsWithin 0 (Ioi 0))
        (nhds ((1 / 2 : ℝ) * (-1 / (2 * delta)))))
  have hEventually :
      EventuallyEq (nhdsWithin 0 (Ioi 0))
        (fun epsilon : ℝ =>
          (squeezeParameter delta (delta - epsilon) -
            (1 / 2 : ℝ) * Real.log (2 * delta / epsilon)) / epsilon)
        (fun epsilon : ℝ =>
          (1 / 2 : ℝ) *
            (Real.log (1 - epsilon / (2 * delta)) / epsilon)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 2 * delta by positivity)).filter_mono
        nhdsWithin_le_nhds] with epsilon hepsilon hepsilonLt
    rw [squeeze_parameter_near_horizon delta epsilon hdelta hepsilon hepsilonLt]
    ring
  convert hLimit.congr' hEventually.symm using 1 <;> field_simp [ne_of_gt hdelta] <;> ring

/-- The occupation-number pole has bounded remainder, converging exactly to
`-3/4`. This strengthens the source's `O(1)` statement. -/
theorem occupation_number_error_limit (delta : ℝ) (hdelta : 0 < delta) :
    Tendsto (fun epsilon : ℝ =>
        occupationNumber delta (delta - epsilon) - delta / (2 * epsilon))
      (nhdsWithin 0 (Ioi 0)) (nhds (-3 / 4 : ℝ)) := by
  have hRational :
      Tendsto (fun epsilon : ℝ =>
          (2 * epsilon - 3 * delta) / (2 * (2 * delta - epsilon)))
        (nhdsWithin 0 (Ioi 0)) (nhds (-3 / 4 : ℝ)) := by
    have hContinuous : ContinuousAt (fun epsilon : ℝ =>
        (2 * epsilon - 3 * delta) / (2 * (2 * delta - epsilon))) 0 := by
      refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
      norm_num [ne_of_gt hdelta]
    have hValue :
        (2 * (0 : ℝ) - 3 * delta) / (2 * (2 * delta - 0)) = -3 / 4 := by
      field_simp [ne_of_gt hdelta]
      ring
    simpa only [hValue] using
      hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hEventually :
      EventuallyEq (nhdsWithin 0 (Ioi 0))
        (fun epsilon : ℝ =>
          occupationNumber delta (delta - epsilon) - delta / (2 * epsilon))
        (fun epsilon : ℝ =>
          (2 * epsilon - 3 * delta) / (2 * (2 * delta - epsilon))) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 2 * delta by positivity)).filter_mono
        nhdsWithin_le_nhds] with epsilon hepsilon hepsilonLt
    exact occupation_number_near_horizon delta epsilon hdelta hepsilon hepsilonLt
  exact hRational.congr' hEventually.symm

/-- The free-energy remainder is first order, with exact normalized
coefficient `1/(2*delta)`. This strengthens the source's `O(epsilon)` claim. -/
theorem horizon_free_energy_normalized_error_limit (delta : ℝ) (hdelta : 0 < delta) :
    Tendsto (fun epsilon : ℝ =>
        (horizonFreeEnergy delta (delta - epsilon) -
            Real.log (delta / (2 * epsilon))) / epsilon)
      (nhdsWithin 0 (Ioi 0)) (nhds (1 / (2 * delta))) := by
  have hLimit := (log_correction_normalized_limit delta hdelta).neg
  have hEventually :
      EventuallyEq (nhdsWithin 0 (Ioi 0))
        (fun epsilon : ℝ =>
          (horizonFreeEnergy delta (delta - epsilon) -
            Real.log (delta / (2 * epsilon))) / epsilon)
        (fun epsilon : ℝ =>
          -(Real.log (1 - epsilon / (2 * delta)) / epsilon)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 2 * delta by positivity)).filter_mono
        nhdsWithin_le_nhds] with epsilon hepsilon hepsilonLt
    rw [horizon_free_energy_near_horizon delta epsilon hdelta hepsilon hepsilonLt]
    ring
  convert hLimit.congr' hEventually.symm using 1 <;> ring

/-- Exact finite-side values for `delta=2`, `omega=1`. -/
theorem interior_numeric_witness :
    squeezeParameter 2 1 = Real.log 3 / 2 ∧
      occupationNumber 2 1 = 1 / 3 ∧
      horizonDeterminant 2 1 = 3 / 4 ∧
      horizonFreeEnergy 2 1 = Real.log (4 / 3) := by
  have hArtanh := Real.artanh_eq_half_log
    (show (1 / 2 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
  refine ⟨?_, by norm_num [occupationNumber], by norm_num [horizonDeterminant], ?_⟩
  · norm_num [squeezeParameter, hArtanh]
    ring
  · exact horizon_free_energy_numeric_witnesses.2.2.1

/-- At zero depth, the positivity premise fails and the quotient form of the
determinant is numerically false because Lean totalizes division by zero. -/
theorem zero_depth_counterexample :
    ¬(0 : ℝ) < 0 ∧
      horizonDeterminant 0 1 = 1 ∧
      ((0 : ℝ) ^ 2 - 1 ^ 2) / (0 : ℝ) ^ 2 = 0 ∧
      horizonDeterminant 0 1 ≠
        ((0 : ℝ) ^ 2 - 1 ^ 2) / (0 : ℝ) ^ 2 := by
  norm_num [horizonDeterminant]

/-- Universal single-defect horizon thermodynamics. The existing determinant
and divergence theorem is reused, while the exact coordinate identities and
all three first-order boundary corrections are added here. -/
theorem single_defect_horizon_thermodynamic_asymptotics
    (delta : NNReal) (hdelta : delta ≠ 0) :
    (forall omega : ℝ,
        horizonDeterminant delta omega =
          ((delta : ℝ) ^ 2 - omega ^ 2) / (delta : ℝ) ^ 2) ∧
      (forall omega : ℝ, |omega| < (delta : ℝ) →
        horizonFreeEnergy delta omega =
            2 * Real.log (Real.cosh (squeezeParameter delta omega)) ∧
          horizonFreeEnergy delta omega =
            Real.log (1 + occupationNumber delta omega)) ∧
      Tendsto (fun epsilon : ℝ =>
          (squeezeParameter delta (delta - epsilon) -
              (1 / 2 : ℝ) * Real.log (2 * delta / epsilon)) / epsilon)
        (nhdsWithin 0 (Ioi 0)) (nhds (-1 / (4 * (delta : ℝ)))) ∧
      Tendsto (fun epsilon : ℝ =>
          occupationNumber delta (delta - epsilon) - delta / (2 * epsilon))
        (nhdsWithin 0 (Ioi 0)) (nhds (-3 / 4 : ℝ)) ∧
      Tendsto (fun epsilon : ℝ =>
          (horizonFreeEnergy delta (delta - epsilon) -
              Real.log (delta / (2 * epsilon))) / epsilon)
        (nhdsWithin 0 (Ioi 0)) (nhds (1 / (2 * (delta : ℝ)))) ∧
      Tendsto (fun omega : ℝ => horizonFreeEnergy delta omega)
        (nhdsWithin (delta : ℝ) (Iio (delta : ℝ))) atTop := by
  have hdeltaPos : (0 : ℝ) < delta :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hdelta)
  have hExisting := single_defect_horizon_free_energy_universal_divergence delta hdelta
  exact ⟨hExisting.1,
    fun omega homega =>
      horizon_free_energy_eq_log_coordinates delta omega hdeltaPos homega,
    squeeze_parameter_normalized_error_limit delta hdeltaPos,
    occupation_number_error_limit delta hdeltaPos,
    horizon_free_energy_normalized_error_limit delta hdeltaPos,
    hExisting.2.2.2⟩

#print axioms single_defect_horizon_thermodynamic_asymptotics
#print axioms interior_numeric_witness
#print axioms zero_depth_counterexample

end D5.S3.Weil.ZetaLinear.HorizonThermodynamicAsymptotics
