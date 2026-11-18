/- GID: D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/BKMLogarithmicMeanInverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Inversion of the actual BKM power integral on complex matrix directions. -/

import D5.S3.Quantum.Recovery.BKMMetricAdjointOrderObstruction
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.Convex.Integral

/-! # The inverse of the BKM logarithmic mean on complex matrices -/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace D5.S3.Quantum.Matrix.BKMLogarithmicMeanInverse

open D5.S3.Divergence.LogDerivTrace (logDeriv)
open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Matrix.ExponentialFirstResponse (derivative)
open D5.S3.Quantum.Recovery.BKMMetricAdjointOrderObstruction
  (basisChange omega omega_entry logDeriv_entry logMean_pos logDeriv_omega
    derivative_eq_omega continuous_mpow)

variable {n : Type*} [Fintype n] [DecidableEq n]

private abbrev Mat (n : Type*) := Matrix n n ℂ

private theorem omega_logDeriv (D : Mat n) (hD : D.PosDef) (X : Mat n) :
    omega D (logDeriv D X) = X := by
  apply (basisChange hD.isHermitian.eigenvectorUnitary).symm.injective
  ext i j
  rw [omega_entry D _ hD, logDeriv_entry D X hD, ← mul_assoc, mul_inv_cancel₀, one_mul]
  exact_mod_cast (logMean_pos _ _ (hD.eigenvalues_pos i) (hD.eigenvalues_pos j)).ne'

/-- The actual power integral and the resolvent logarithmic derivative are inverse
on the entire complex matrix space, including repeated eigenvalues. -/
theorem inverse_identities (D : Mat n) (hD : D.PosDef) :
    Function.LeftInverse (logDeriv D) (omega D) ∧ Function.RightInverse (logDeriv D) (omega D) :=
  ⟨fun X => logDeriv_omega D X hD, omega_logDeriv D hD⟩

/-- The actual BKM power integral as a complex-linear equivalence. -/
def omegaEquiv (D : Mat n) (hD : D.PosDef) : Mat n ≃ₗ[ℂ] Mat n :=
  LinearEquiv.ofBijective (derivative (CFC.log D)).toLinearMap (by
    have h : Function.Bijective (omega D) :=
      ⟨(inverse_identities D hD).1.injective, (inverse_identities D hD).2.surjective⟩
    change Function.Bijective (derivative (CFC.log D))
    rw [show (derivative (CFC.log D) : Mat n → Mat n) = omega D from
      funext (derivative_eq_omega D hD)]
    exact h)

/-- The forward action is the power integral from the local-order result. -/
theorem omegaEquiv_apply (D : Mat n) (hD : D.PosDef) (X : Mat n) :
    omegaEquiv D hD X = omega D X :=
  derivative_eq_omega D hD X

/-- The backward action is the resolvent integral, in arbitrary complex directions. -/
theorem omegaEquiv_symm_apply (D : Mat n) (hD : D.PosDef) (X : Mat n) :
    (omegaEquiv D hD).symm X = logDeriv D X := by
  apply (omegaEquiv D hD).injective
  rw [LinearEquiv.apply_symm_apply, omegaEquiv_apply]
  exact ((inverse_identities D hD).2 X).symm

private theorem omega_mem (B : StarSubalgebra ℂ (Mat n)) (D : B)
    (hD : (D : Mat n).PosDef) (X : B) : omega (D : Mat n) (X : Mat n) ∈ B := by
  have hB : IsClosed (B : Set (Mat n)) := B.toSubmodule.closed_of_finiteDimensional
  have hpow (u : ℝ) : mpow (D : Mat n) u ∈ B :=
    cfc_mem (fun t : ℝ => t ^ u) D.property
  let f : ℝ → Mat n := fun u => mpow (D : Mat n) u * (X : Mat n) * mpow (D : Mat n) (1 - u)
  have hi : IntervalIntegrable f volume 0 1 :=
    (((continuous_mpow _ hD).mul continuous_const).mul
      ((continuous_mpow _ hD).comp (continuous_const.sub continuous_id))).intervalIntegrable _ _
  have : IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; norm_num⟩
  rw [omega, intervalIntegral.integral_of_le zero_le_one]
  exact (B.toSubmodule.restrictScalars ℝ).convex.integral_mem hB
    (Filter.Eventually.of_forall fun u => B.mul_mem (B.mul_mem (hpow u) X.property) (hpow (1 - u)))
    hi.1

/-- The actual BKM integral restricts to a complex-linear automorphism of any
unital star-subalgebra containing the faithful base matrix. -/
def omegaRestrict (B : StarSubalgebra ℂ (Mat n)) (D : B) (hD : (D : Mat n).PosDef) :
    B ≃ₗ[ℂ] B := by
  let f := LinearMap.codRestrict B.toSubmodule
    ((omegaEquiv (D : Mat n) hD).toLinearMap.domRestrict B.toSubmodule)
    (fun X => by
      change omegaEquiv (D : Mat n) hD (X : Mat n) ∈ B
      rw [omegaEquiv_apply]
      exact omega_mem B D hD X)
  have hinj : Function.Injective f := by
    intro X Y h
    have hXY := congrArg (fun Z : B => (Z : Mat n)) h
    change omegaEquiv (D : Mat n) hD (X : Mat n) = omegaEquiv (D : Mat n) hD (Y : Mat n) at hXY
    exact Subtype.ext ((omegaEquiv (D : Mat n) hD).injective hXY)
  exact LinearEquiv.ofBijective f ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- The restriction acts by the original matrix integral. -/
theorem omegaRestrict_apply (B : StarSubalgebra ℂ (Mat n)) (D : B)
    (hD : (D : Mat n).PosDef) (X : B) :
    (omegaRestrict B D hD X : Mat n) = omega (D : Mat n) (X : Mat n) :=
  omegaEquiv_apply _ hD _

/-- The ambient resolvent integral preserves the subalgebra and computes the
inverse of its actual BKM integral. -/
theorem omegaRestrict_symm_apply (B : StarSubalgebra ℂ (Mat n)) (D : B)
    (hD : (D : Mat n).PosDef) (Y : B) :
    ((omegaRestrict B D hD).symm Y : Mat n) = logDeriv (D : Mat n) (Y : Mat n) := by
  rw [← omegaEquiv_symm_apply _ hD]
  apply (omegaEquiv (D : Mat n) hD).injective
  rw [LinearEquiv.apply_symm_apply, omegaEquiv_apply, ← omegaRestrict_apply B D hD,
    LinearEquiv.apply_symm_apply]

#print axioms inverse_identities
#print axioms omegaRestrict_symm_apply

end D5.S3.Quantum.Matrix.BKMLogarithmicMeanInverse
