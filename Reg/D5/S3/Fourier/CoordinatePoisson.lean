import Reg.D5.S3.Fourier.MatrixGaussian
import D5.S3.Fourier.CoordinatePoisson

open MeasureTheory
open scoped BigOperators
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Fourier.CoordinatePoisson
noncomputable section
universe u
open Reg.D5.S3.Fourier.MatrixGaussian

def poissonArena : Arena where
  signature := expSignature
  Law R := ∀ {n : Type u} [Fintype n] {f : C(n → ℝ, ℂ)}, Integrable f →
    (∀ K : TopologicalSpace.Compacts (n → ℝ), Summable (fun a : n → ℤ =>
      ‖(f.comp (ContinuousMap.addRight (fun i => (a i : ℝ)))).restrict K‖)) →
    Summable (fun k : n → ℤ => ∫ x : n → ℝ, R.readout () ()
      (-2 * Real.pi * Complex.I * (∑ i, (k i : ℝ) * x i : ℝ)) * f x) →
    (∑' a : n → ℤ, f (fun i => (a i : ℝ))) =
      ∑' k : n → ℤ, ∫ x : n → ℝ, R.readout () ()
        (-2 * Real.pi * Complex.I * (∑ i, (k i : ℝ) * x i : ℝ)) * f x

theorem poisson_bridge :
    (type_of% (@D5.S3.Fourier.CoordinatePoisson.tsum_eq_tsum_integral.{u})) ↔
      poissonArena.{u}.Law actual := Iff.rfl

end
end Reg.D5.S3.Fourier.CoordinatePoisson
