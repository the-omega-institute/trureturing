import Reg.D5.S3.Fourier.MatrixGaussian
import D5.S3.Fourier.MatrixGaussianSourceDerivatives

open MeasureTheory Matrix
open scoped BigOperators
open D5.S3.Fourier.MatrixGaussian
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Fourier.MatrixGaussian

namespace Reg.D5.S3.Fourier.MatrixGaussianSourceDerivatives
noncomputable section

/-- Exact mixed-source law arena. Faithful reconstruction, variation and
sensitivity are not supplied by this arena alone; no validated registration
is claimed. Issue 20151 records the predecessor exponential source-binding gap. -/
def mixedSourceArena : Arena where
  signature := expSignature
  Law R := ∀ {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ), A.PosDef →
    ∀ (b : ℂ), 0 < b.re → ∀ (is : List (Fin r)) (z : Fin r → ℂ),
    sourcePartial is (fun w => ∑' a : Fin r → ℤ,
      R.readout () () (-Real.pi*b*(quadratic A (fun i => (a i : ℝ)) : ℂ) +
        ∑ i, w i*(a i : ℂ))) z =
      ∑' a : Fin r → ℤ, (is.map (fun i => (a i : ℂ))).prod *
        R.readout () () (-Real.pi*b*(quadratic A (fun i => (a i : ℝ)) : ℂ) +
          ∑ i, z i*(a i : ℂ))

theorem mixed_source_bridge : (type_of% (@sourcePartial_tsum)) ↔
    mixedSourceArena.Law actual := Iff.rfl

#print axioms mixed_source_bridge
end
end Reg.D5.S3.Fourier.MatrixGaussianSourceDerivatives
