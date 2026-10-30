import Reg.D5.S3.Fourier.MatrixGaussian
import D5.S3.Fourier.MatrixGaussianTheta

open Matrix
open scoped BigOperators
open D5.S3.Fourier.MatrixGaussian
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Fourier.MatrixGaussianTheta
noncomputable section
open Reg.D5.S3.Fourier.MatrixGaussian

def summableArena : Arena where
  signature := expSignature
  Law R := ∀ {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ), A.PosDef →
    ∀ (τ : ℂ), 0 < τ.im → Summable (fun a : Fin r → ℤ => ‖R.readout () ()
      (Real.pi * Complex.I * τ * (quadratic A (fun i => (a i : ℝ)) : ℂ))‖)

theorem summable_bridge : (type_of% (@summable_norm_theta)) ↔ summableArena.Law actual := Iff.rfl

abbrev thetaSignature : Signature where
  Params := Σ r : ℕ, Matrix (Fin r) (Fin r) ℝ
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def thetaActual : Realization thetaSignature :=
  realize thetaSignature (fun _ p τ => theta p.2 τ) (fun e => nomatch e)

def inversionArena : Arena where
  signature := thetaSignature
  Law R := ∀ {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ), A.PosDef →
    ∀ (τ : ℂ), 0 < τ.im → R.readout () ⟨r, A⟩ (-1 / τ) =
      (-Complex.I * τ) ^ ((r : ℂ) / 2) / (Real.sqrt A.det : ℂ) * R.readout () ⟨r, A⁻¹⟩ τ

theorem inversion_bridge : (type_of% (@theta_inversion)) ↔
    inversionArena.Law thetaActual := Iff.rfl

end
end Reg.D5.S3.Fourier.MatrixGaussianTheta
