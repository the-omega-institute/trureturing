import Reg.D5.S3.Fourier.MatrixGaussian
import D5.S3.Fourier.MatrixGaussianSourcePoisson

open MeasureTheory Matrix
open scoped BigOperators
open D5.S3.Fourier.MatrixGaussian
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Fourier.MatrixGaussian

namespace Reg.D5.S3.Fourier.MatrixGaussianSourcePoisson
noncomputable section

/-- Exact all-source Poisson arena; faithful variation, sensitivity and occurrence
reconstruction remain uncompleted. See the source-binding gap in issue 20151. -/
def poissonArena : Arena where
  signature := expSignature
  Law R := ∀ {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ), A.PosDef →
    ∀ (b : ℂ), 0 < b.re → ∀ (z : Fin r → ℂ),
    (∑' a : Fin r → ℤ, R.readout () ()
      (-Real.pi*b*(quadratic A (fun i => (a i : ℝ)) : ℂ) + ∑ i, z i*(a i : ℂ))) =
      ((Real.sqrt A.det : ℂ)⁻¹ * b^(-(r : ℂ)/2) *
        R.readout () () (complexQuadratic A⁻¹ z/(4*Real.pi*b))) *
      ∑' k : Fin r → ℤ, R.readout () ()
        (-Real.pi*b⁻¹*(quadratic A⁻¹ (fun i => (k i : ℝ)) : ℂ) +
          ∑ i, (-Complex.I/b*((A⁻¹.map Complex.ofRealHom *ᵥ z) i))*(k i : ℂ))

theorem poisson_bridge : (type_of% (@poisson_gaussian_source)) ↔
    poissonArena.Law actual := Iff.rfl

#print axioms poisson_bridge
end
end Reg.D5.S3.Fourier.MatrixGaussianSourcePoisson
