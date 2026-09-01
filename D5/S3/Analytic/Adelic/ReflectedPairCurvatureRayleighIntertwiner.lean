/- GID: D5/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner
   generality: I
   mirror-B: D5/B/S3/Analytic/Adelic/ReflectedPairCurvatureRayleighIntertwiner
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Realize the off-line curvature dipole as a normalized even-channel quadratic readout. -/

import D5.S3.Analytic.Adelic.OffLineCurvatureDipole
import D5.S3.Analytic.Adelic.ReflectedGrowthPairSecondOrderSpectrum
import D5.S3.Quantum.FiniteDimensional
import D5.S3.Weil.Pick.HermitianKernelNegativeSquares
import D5.S3.Weil.ZetaLinear.OfflineZeroGeometricMonodromy
import D5.S3.Weil.ZetaLinear.Sylvester
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * `ReflectedGrowthPairSecondOrderSpectrum` already identifies the reflected
     signed determinant `-delta^2` with the scalar negative-second-derivative
     eigenvalue. It is imported and reused rather than reconstructed.
   * `OffLineCurvatureDipole` already proves the exact rational curvature,
     center value, zero set, integrability, zero total mass, and sign profile.
     This module transports that frozen curvature into a finite quadratic
     readout instead of reproving the analytic theorem.
   * `Quantum.FiniteDimensional` supplies the canonical `QubitMatrix` and Pauli
     `qubitX`; `RHLinalg.hermForm` supplies the repository's Hermitian
     quadratic-form readout. `OfflineZeroGeometricMonodromy` supplies the
     unitary-boundary versus hyperbolic-bulk classification.
   * `HermitianKernelNegativeSquares.oneNegativeKernel` supplies the canonical
     scalar negative kernel used by the center-polarity chart. No second
     negative-squares definition is introduced.
   * Repository searches for a curvature-Rayleigh intertwiner, detuned
     reflected generator, and normalized even-channel curvature readout found
     no existing owner. The only new objects below are the missing finite
     operator chart and its exact observer-agreement theorems.
   * The auxiliary detuning parameter is a spectral offset. No physical-time
     interpretation, global completed-zeta realization, or RH premise is
     introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace D5.S3.Analytic.Adelic.ReflectedPairCurvatureRayleighIntertwiner

open D5.S3.Analytic.Adelic.OffLineCurvatureDipole
open D5.S3.Analytic.Adelic.ReflectedGrowthPairNegativeSquare
open D5.S3.Analytic.Adelic.ReflectedGrowthPairSecondOrderSpectrum
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Weil.Pick.HermitianKernelNegativeSquares
open D5.S3.Weil.ZetaLinear.OfflineZeroCharacter
open D5.S3.Weil.ZetaLinear.OfflineZeroGeometricMonodromy
open D5.S3.Weil.ZetaLinear.ReflectedZeroModePhaseFlattening
open RHLinalg

/-- The two-dimensional complex operator carrying a common spectral detuning
`tau` and a reflected radial splitting `delta`. -/
def detunedReflectedGenerator (delta tau : ℝ) : QubitMatrix :=
  !![Complex.I * (tau : ℂ), (delta : ℂ);
     (delta : ℂ), Complex.I * (tau : ℂ)]

/-- The even channel in the branch-symmetric basis. -/
def evenChannelState : Fin 2 → ℂ :=
  ![1, 0]

/-- The even-channel quadratic readout of the negative operator square. -/
def evenChannelNegativeSquareReadout (delta tau : ℝ) : ℝ :=
  hermForm (-((detunedReflectedGenerator delta tau) ^ 2)) evenChannelState

/-- The even-channel energy of the detuned reflected generator. -/
def evenChannelEnergyReadout (delta tau : ℝ) : ℝ :=
  hermForm
    ((detunedReflectedGenerator delta tau)ᴴ *
      detunedReflectedGenerator delta tau)
    evenChannelState

/-- Normalize the signed negative-square readout by the square of the positive
energy readout. -/
def normalizedCurvatureRayleighReadout (delta tau : ℝ) : ℝ :=
  2 * evenChannelNegativeSquareReadout delta tau /
    evenChannelEnergyReadout delta tau ^ 2

/-- The zero kernel on the one-point carrier. -/
def zeroUnitKernel : HermitianKernel Unit where
  value := fun _ _ => 0
  conj_symm := by simp

/-- The coarse center-polarity chart: the unitary boundary is sent to the zero
kernel and every nonzero reflected split is sent to the canonical one-negative
kernel already owned by the Pick library. -/
def centerCurvaturePolarityKernel (delta : ℝ) : HermitianKernel Unit :=
  if delta = 0 then zeroUnitKernel else oneNegativeKernel

/-- The finite generator is the canonical Pauli-X reflected coupling plus a
scalar imaginary detuning. -/
theorem detuned_reflected_generator_pauli_decomposition
    (delta tau : ℝ) :
    detunedReflectedGenerator delta tau =
      (Complex.I * (tau : ℂ)) • (1 : QubitMatrix) +
        (delta : ℂ) • qubitX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [detunedReflectedGenerator, qubitX, Matrix.one_apply]

/-- The detuned reflected generator is normal and its Gram operator is the
scalar energy `tau^2 + delta^2`. -/
theorem detuned_reflected_generator_gram
    (delta tau : ℝ) :
    (detunedReflectedGenerator delta tau)ᴴ *
        detunedReflectedGenerator delta tau =
      (((tau ^ 2 + delta ^ 2 : ℝ) : ℂ)) • (1 : QubitMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [detunedReflectedGenerator, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply] <;>
    ring

private theorem hermForm_even_channel (A : QubitMatrix) :
    hermForm A evenChannelState = (A 0 0).re := by
  simp [hermForm, evenChannelState, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

/-- The even channel reads the hyperbolic numerator `tau^2 - delta^2` from the
negative square of the finite generator. -/
theorem even_channel_negative_square_readout_formula
    (delta tau : ℝ) :
    evenChannelNegativeSquareReadout delta tau =
      tau ^ 2 - delta ^ 2 := by
  unfold evenChannelNegativeSquareReadout
  rw [hermForm_even_channel]
  simp [detunedReflectedGenerator, pow_two, Matrix.mul_apply,
    Fin.sum_univ_two] <;>
    ring

/-- The even-channel energy is the positive radial denominator
`tau^2 + delta^2`. -/
theorem even_channel_energy_readout_formula
    (delta tau : ℝ) :
    evenChannelEnergyReadout delta tau =
      tau ^ 2 + delta ^ 2 := by
  unfold evenChannelEnergyReadout
  rw [detuned_reflected_generator_gram, hermForm_even_channel]
  simp

/-- The normalized quadratic readout is exactly the rational curvature-dipole
profile. -/
theorem normalized_curvature_rayleigh_readout_formula
    (delta tau : ℝ) :
    normalizedCurvatureRayleighReadout delta tau =
      2 * ((tau ^ 2 - delta ^ 2) /
        (tau ^ 2 + delta ^ 2) ^ 2) := by
  simp [normalizedCurvatureRayleighReadout,
    even_channel_negative_square_readout_formula,
    even_channel_energy_readout_formula]
  ring

/-- The frozen off-line curvature dipole is exactly the normalized
finite-dimensional even-channel Rayleigh readout at detuning `t - gamma`. -/
theorem off_line_curvature_rayleigh_intertwiner
    (delta gamma : ℝ) (hdelta : 0 < delta) :
    let potential := fun u t : ℝ =>
      Real.log ((u - delta) ^ 2 + (t - gamma) ^ 2) / 2 +
        Real.log ((u + delta) ^ 2 + (t - gamma) ^ 2) / 2
    let curvature := fun t : ℝ =>
      deriv (deriv (fun u => potential u t)) 0
    ∀ t, curvature t =
      normalizedCurvatureRayleighReadout delta (t - gamma) := by
  dsimp only
  intro t
  calc
    deriv
        (deriv
          (fun u : ℝ =>
            Real.log ((u - delta) ^ 2 + (t - gamma) ^ 2) / 2 +
              Real.log ((u + delta) ^ 2 + (t - gamma) ^ 2) / 2)) 0 =
        2 * (((t - gamma) ^ 2 - delta ^ 2) /
          ((t - gamma) ^ 2 + delta ^ 2) ^ 2) :=
      (off_line_curvature_dipole delta gamma hdelta).1 t
    _ = normalizedCurvatureRayleighReadout delta (t - gamma) := by
      rw [normalized_curvature_rayleigh_readout_formula]

/-- At zero detuning, the finite quadratic readout is the same signed
determinant already carried by the reflected scalar generator. -/
theorem center_negative_square_readout_eq_signed_determinant
    (delta : ℝ) :
    evenChannelNegativeSquareReadout delta 0 =
      reflectionPairSignedDeterminant delta := by
  rw [even_channel_negative_square_readout_formula]
  have hdet := (reflection_pair_signed_determinant delta 0).2.1
  rw [hdet]
  ring

/-- The finite center readout and the scalar negative-second-derivative
observer have the same eigenvalue on both reflected branches and their
symmetric sum. -/
theorem center_readout_matches_reflected_second_order_spectrum
    (delta time : ℝ) :
    negativeSecondDerivative (positiveRateBranch delta) time =
        evenChannelNegativeSquareReadout delta 0 *
          positiveRateBranch delta time ∧
      negativeSecondDerivative (negativeRateBranch delta) time =
        evenChannelNegativeSquareReadout delta 0 *
          negativeRateBranch delta time ∧
      negativeSecondDerivative (reflectedGrowthSum delta) time =
        evenChannelNegativeSquareReadout delta 0 *
          reflectedGrowthSum delta time := by
  simpa [center_negative_square_readout_eq_signed_determinant] using
    reflected_growth_pair_second_order_spectrum delta time

/-- Away from the unitary boundary, the normalized center readout is the
strictly negative value `-2 / delta^2`. -/
theorem normalized_curvature_rayleigh_center_value
    (delta : ℝ) (hdelta : delta ≠ 0) :
    normalizedCurvatureRayleighReadout delta 0 =
      -(2 / delta ^ 2) := by
  rw [normalized_curvature_rayleigh_readout_formula]
  have hsq : delta ^ 2 ≠ 0 := pow_ne_zero 2 hdelta
  field_simp [hsq]
  ring

/-- The center Rayleigh readout is negative exactly for a nonzero reflected
split. -/
theorem normalized_curvature_rayleigh_center_negative_iff
    (delta : ℝ) :
    normalizedCurvatureRayleighReadout delta 0 < 0 ↔
      delta ≠ 0 := by
  constructor
  · intro hnegative hzero
    subst delta
    rw [normalized_curvature_rayleigh_readout_formula] at hnegative
    norm_num at hnegative
  · intro hdelta
    rw [normalized_curvature_rayleigh_center_value delta hdelta]
    exact neg_neg_iff_pos.mpr
      (div_pos (by norm_num) (sq_pos_of_ne_zero hdelta))

/-- The center Rayleigh readout vanishes exactly on the unsplit boundary. -/
theorem normalized_curvature_rayleigh_center_zero_iff
    (delta : ℝ) :
    normalizedCurvatureRayleighReadout delta 0 = 0 ↔
      delta = 0 := by
  constructor
  · intro hzero
    by_contra hdelta
    have hnegative :=
      (normalized_curvature_rayleigh_center_negative_iff delta).2 hdelta
    linarith
  · rintro rfl
    rw [normalized_curvature_rayleigh_readout_formula]
    norm_num

/-- The frozen monodromy classification is exactly the sign classification of
this center curvature readout. -/
theorem offline_zero_monodromy_hyperbolic_iff_negative_center
    (rho : ℂ) :
    (offlineZeroMonodromy rho).IsHyperbolic ↔
      normalizedCurvatureRayleighReadout
        (criticalDisplacement rho) 0 < 0 := by
  rw [offline_zero_monodromy_hyperbolic_iff,
    normalized_curvature_rayleigh_center_negative_iff]

/-- The frozen unitary-boundary classification is exactly the zero set of the
center curvature readout. -/
theorem offline_zero_character_unitary_iff_zero_center
    (rho : ℂ) :
    IsUnitary (offlineZeroCharacter rho) ↔
      normalizedCurvatureRayleighReadout
        (criticalDisplacement rho) 0 = 0 := by
  rw [offline_zero_unitary_boundary_iff,
    normalized_curvature_rayleigh_center_zero_iff]

/-- The coarse polarity chart selects the existing canonical negative kernel
exactly away from the unsplit boundary. -/
theorem center_curvature_polarity_kernel_eq_one_negative_iff
    (delta : ℝ) :
    centerCurvaturePolarityKernel delta = oneNegativeKernel ↔
      delta ≠ 0 := by
  by_cases hdelta : delta = 0
  · subst delta
    simp [centerCurvaturePolarityKernel, zeroUnitKernel, oneNegativeKernel]
  · simp [centerCurvaturePolarityKernel, hdelta]

/-- After scale normalization, the exact center readout agrees with the scalar
entry of the coarse polarity kernel. -/
theorem normalized_center_readout_eq_polarity_kernel
    (delta : ℝ) :
    delta ^ 2 / 2 * normalizedCurvatureRayleighReadout delta 0 =
      ((centerCurvaturePolarityKernel delta).value () ()).re := by
  by_cases hdelta : delta = 0
  · subst delta
    simp [centerCurvaturePolarityKernel, zeroUnitKernel,
      normalized_curvature_rayleigh_readout_formula]
  · rw [normalized_curvature_rayleigh_center_value delta hdelta]
    have hsq : delta ^ 2 ≠ 0 := pow_ne_zero 2 hdelta
    simp [centerCurvaturePolarityKernel, hdelta, oneNegativeKernel]
    field_simp [hsq]
    ring

#print axioms detuned_reflected_generator_gram
#print axioms off_line_curvature_rayleigh_intertwiner
#print axioms center_readout_matches_reflected_second_order_spectrum
#print axioms offline_zero_monodromy_hyperbolic_iff_negative_center
#print axioms offline_zero_character_unitary_iff_zero_center
#print axioms normalized_center_readout_eq_polarity_kernel

end D5.S3.Analytic.Adelic.ReflectedPairCurvatureRayleighIntertwiner
