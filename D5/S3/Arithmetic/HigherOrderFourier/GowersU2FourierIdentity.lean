/- GID: D5/S3/Arithmetic/HigherOrderFourier/GowersU2FourierIdentity
   generality: G
   mirror-B: D5/B/S3/Arithmetic/HigherOrderFourier/GowersU2FourierIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Plancherel and autocorrelation diagonalization imply the finite U2 Fourier fourth-moment identity. -/

import D5.S3.Arithmetic.HigherOrderFourier.GowersTranslationModulationInvariance
import Mathlib.Tactic

/-!
# Finite U2 Fourier fourth-moment identity

The finite `U^2` identity requires two standard Fourier inputs: Plancherel and
the fact that Fourier transform sends additive autocorrelation to squared
Fourier magnitude.  This module packages those inputs without choosing a
particular finite dual-group implementation and derives

`U2Energy(f) = scale * sum_gamma |fhat(gamma)|^4`.

This isolates the exact library bridge still needed for a concrete finite
Pontryagin dual.  The theorem does not assume or claim an inverse theorem,
higher-order nilsequence representation, or prime uniformity estimate.
-/

/- Library-search audit trail (2026-09-01):
   * `FiniteGowersCubeMoment` owns the derivative definition of finite `U^2`
     energy.
   * `GowersTranslationModulationInvariance` owns its affine character
     symmetries.
   * Repository search found no finite Fourier transform interface carrying
     both Plancherel and autocorrelation diagonalization.
   * Pinned Mathlib has extensive character theory but no repository-level
     theorem directly matching the present normalization and energy owner. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace D5.S3.Arithmetic.HigherOrderFourier.GowersU2FourierIdentity

open D5.S3.Arithmetic.HigherOrderFourier.FiniteGowersCubeMoment

noncomputable section

universe u v

variable {G : Type u} [AddCommGroup G] [Fintype G]
variable {Spectrum : Type v} [Fintype Spectrum]

/-- Additive autocorrelation function used by the finite `U^2` energy. -/
def additiveAutocorrelation (function : G → ℂ) : G → ℂ :=
  fun direction =>
    ∑ point, multiplicativeDerivative function direction point

/-- A finite Fourier realization with exactly the two laws required by the
`U^2` fourth-moment proof. -/
structure FiniteFourierPlancherelSystem where
  fourier : (G → ℂ) → (Spectrum → ℂ)
  scale : ℝ
  scale_nonneg : 0 ≤ scale
  plancherel : ∀ function : G → ℂ,
    (∑ point, ‖function point‖ ^ 2) =
      scale * ∑ frequency, ‖fourier function frequency‖ ^ 2
  autocorrelation_transform : ∀ function frequency,
    fourier (additiveAutocorrelation function) frequency =
      ((‖fourier function frequency‖ ^ 2 : ℝ) : ℂ)

/-- Scaled fourth moment of finite Fourier coefficients. -/
def finiteFourierFourthMoment
    (system : FiniteFourierPlancherelSystem
      (G := G) (Spectrum := Spectrum))
    (function : G → ℂ) : ℝ :=
  system.scale * ∑ frequency,
    ‖system.fourier function frequency‖ ^ 4

/-- The derivative definition of finite `U^2` energy is the squared norm of
the additive autocorrelation function. -/
theorem finiteGowersU2Energy_eq_autocorrelation_norm
    (function : G → ℂ) :
    finiteGowersU2Energy function =
      ∑ direction, ‖additiveAutocorrelation function direction‖ ^ 2 := by
  rfl

/-- Plancherel plus autocorrelation diagonalization gives the finite Fourier
fourth-moment identity. -/
theorem finiteGowersU2Energy_eq_fourierFourthMoment
    (system : FiniteFourierPlancherelSystem
      (G := G) (Spectrum := Spectrum))
    (function : G → ℂ) :
    finiteGowersU2Energy function =
      finiteFourierFourthMoment system function := by
  rw [finiteGowersU2Energy_eq_autocorrelation_norm,
    system.plancherel]
  unfold finiteFourierFourthMoment
  congr 1
  apply Finset.sum_congr rfl
  intro frequency _
  rw [system.autocorrelation_transform]
  calc
    ‖((‖system.fourier function frequency‖ ^ 2 : ℝ) : ℂ)‖ ^ 2 =
        (‖system.fourier function frequency‖ ^ 2) ^ 2 := by
      simp [abs_of_nonneg (sq_nonneg
        ‖system.fourier function frequency‖)]
    _ = ‖system.fourier function frequency‖ ^ 4 := by ring

/-- The Fourier fourth moment is nonnegative. -/
theorem finiteFourierFourthMoment_nonneg
    (system : FiniteFourierPlancherelSystem
      (G := G) (Spectrum := Spectrum))
    (function : G → ℂ) :
    0 ≤ finiteFourierFourthMoment system function := by
  unfold finiteFourierFourthMoment
  exact mul_nonneg system.scale_nonneg
    (Finset.sum_nonneg fun frequency _ =>
      pow_nonneg (norm_nonneg _) _)

/-- Under the Fourier laws, zero `U^2` energy is equivalent to vanishing of
all Fourier coefficients. -/
theorem finiteGowersU2Energy_eq_zero_iff_fourier
    (system : FiniteFourierPlancherelSystem
      (G := G) (Spectrum := Spectrum))
    (hScale : 0 < system.scale)
    (function : G → ℂ) :
    finiteGowersU2Energy function = 0 ↔
      ∀ frequency, system.fourier function frequency = 0 := by
  rw [finiteGowersU2Energy_eq_fourierFourthMoment]
  constructor
  · intro hEnergy frequency
    unfold finiteFourierFourthMoment at hEnergy
    have hSumZero :
        (∑ index, ‖system.fourier function index‖ ^ 4) = 0 := by
      exact (mul_eq_zero.mp hEnergy).resolve_left (ne_of_gt hScale)
    have hTermLe :
        ‖system.fourier function frequency‖ ^ 4 ≤
          ∑ index, ‖system.fourier function index‖ ^ 4 := by
      exact Finset.single_le_sum
        (fun index _ => pow_nonneg (norm_nonneg _) _)
        (Finset.mem_univ frequency)
    rw [hSumZero] at hTermLe
    have hNormZero : ‖system.fourier function frequency‖ = 0 := by
      have hNonneg := norm_nonneg (system.fourier function frequency)
      nlinarith [sq_nonneg
        (‖system.fourier function frequency‖ ^ 2)]
    exact norm_eq_zero.mp hNormZero
  · intro hFourier
    unfold finiteFourierFourthMoment
    simp [hFourier]

#print axioms finiteGowersU2Energy_eq_autocorrelation_norm
#print axioms finiteGowersU2Energy_eq_fourierFourthMoment
#print axioms finiteFourierFourthMoment_nonneg
#print axioms finiteGowersU2Energy_eq_zero_iff_fourier

end

end D5.S3.Arithmetic.HigherOrderFourier.GowersU2FourierIdentity
