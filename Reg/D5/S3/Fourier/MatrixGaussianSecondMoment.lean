import Reg.D5.S3.Fourier.MatrixGaussian
import D5.S3.Fourier.MatrixGaussianSecondMoment

open MeasureTheory Matrix
open scoped BigOperators
open D5.S3.Fourier.MatrixGaussian
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Fourier.MatrixGaussianSecondMoment
noncomputable section
open Reg.D5.S3.Fourier.MatrixGaussian

def fourierArena : Arena where
  signature := expSignature
  Law R := ∀ {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ), A.PosDef →
    ∀ (b : ℂ), 0 < b.re → ∀ (u v w : Fin r → ℝ),
    (∫ x : Fin r → ℝ, R.readout () () (-2 * Real.pi * Complex.I * (w ⬝ᵥ x : ℝ)) *
      ((u ⬝ᵥ A *ᵥ x : ℝ) : ℂ) * ((v ⬝ᵥ A *ᵥ x : ℝ) : ℂ) *
      R.readout () () (-Real.pi * b * (quadratic A x : ℂ))) =
    (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
      (((u ⬝ᵥ A *ᵥ v : ℝ) : ℂ) / (2 * Real.pi * b) -
        ((u ⬝ᵥ w : ℝ) : ℂ) * ((v ⬝ᵥ w : ℝ) : ℂ) / b ^ 2) *
      R.readout () () (-Real.pi / b * (quadratic A⁻¹ w : ℂ))

theorem fourier_bridge : (type_of% (@integral_fourier_second_moment)) ↔
    fourierArena.Law actual := Iff.rfl

def observedTerm (R : Realization expSignature) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℝ) (u v : Fin r → ℝ) (τ : ℂ) (n : Fin r → ℤ) : ℂ :=
  ((u ⬝ᵥ A *ᵥ (fun i => (n i : ℝ)) : ℝ) : ℂ) *
  ((v ⬝ᵥ A *ᵥ (fun i => (n i : ℝ)) : ℝ) : ℂ) *
  R.readout () () (Real.pi * Complex.I * τ * (quadratic A (fun i => (n i : ℝ)) : ℂ))

def inversionArena : Arena where
  signature := expSignature
  Law R := ∀ {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ), A.PosDef →
    ∀ (u v : Fin r → ℝ) (τ : ℂ), 0 < τ.im →
    Summable (fun n : Fin r → ℤ => ‖observedTerm R A u v (-1 / τ) n‖) ∧
    HasSum (observedTerm R A u v (-1 / τ))
      (((-Complex.I * τ) ^ ((r : ℂ) / 2) / (Real.sqrt A.det : ℂ)) *
        (τ ^ 2 * (∑' n : Fin r → ℤ, observedTerm R A⁻¹ (A *ᵥ u) (A *ᵥ v) τ n) +
          τ / (2 * Real.pi * Complex.I) * ((u ⬝ᵥ A *ᵥ v : ℝ) : ℂ) *
            ∑' n : Fin r → ℤ, R.readout () ()
              (Real.pi * Complex.I * τ * (quadratic A⁻¹ (fun i => (n i : ℝ)) : ℂ))))

theorem inversion_bridge : (type_of% (@second_moment_inversion)) ↔
    inversionArena.Law actual := Iff.rfl

end
end Reg.D5.S3.Fourier.MatrixGaussianSecondMoment
