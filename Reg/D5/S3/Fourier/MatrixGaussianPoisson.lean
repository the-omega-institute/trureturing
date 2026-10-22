import Reg.D5.S3.Fourier.MatrixGaussian
import D5.S3.Fourier.MatrixGaussianPoisson

open MeasureTheory Matrix
open scoped BigOperators
open D5.S3.Fourier.MatrixGaussian
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Fourier.MatrixGaussianPoisson
noncomputable section
open Reg.D5.S3.Fourier.MatrixGaussian

abbrev quadraticSignature : Signature where
  Params := Σ r : ℕ, Matrix (Fin r) (Fin r) ℝ
  State p := Fin p.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def quadraticActual : Realization quadraticSignature :=
  realize quadraticSignature (fun _ p x => quadratic p.2 x) (fun e => nomatch e)

def lowerArena : Arena where
  signature := quadraticSignature
  Law R := ∀ {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ), A.PosDef →
    ∃ t : ℝ, 0 < t ∧ ∀ x : Fin r → ℝ, t * (∑ i, x i ^ 2) ≤ R.readout () ⟨r, A⟩ x

theorem lower_bridge : (type_of% (@exists_quadratic_lower_bound)) ↔
    lowerArena.Law quadraticActual := Iff.rfl

def summableArena : Arena where
  signature := expSignature
  Law R := ∀ {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ), A.PosDef →
    ∀ (b : ℂ), 0 < b.re → Summable (fun a : Fin r → ℤ =>
      ‖R.readout () () (-Real.pi * b * (quadratic A (fun i => (a i : ℝ)) : ℂ))‖)

theorem summable_bridge : (type_of% (@summable_norm_gaussian)) ↔
    summableArena.Law actual := Iff.rfl

structure LocalParams where
  r : ℕ
  A : Matrix (Fin r) (Fin r) ℝ
  b : ℂ
  K : TopologicalSpace.Compacts (Fin r → ℝ)

abbrev localSignature : Signature where
  Params := LocalParams
  State p := Fin p.r → ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def localActual : Realization localSignature :=
  realize localSignature (fun _ p a =>
    ‖((gaussianMap p.A p.b).comp (ContinuousMap.addRight (fun i => (a i : ℝ)))).restrict p.K‖)
    (fun e => nomatch e)

def localArena : Arena where
  signature := localSignature
  Law R := ∀ {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ), A.PosDef →
    ∀ (b : ℂ), 0 < b.re → ∀ (K : TopologicalSpace.Compacts (Fin r → ℝ)),
      Summable (R.readout () ⟨r, A, b, K⟩)

theorem local_bridge : (type_of% (@locally_summable_norm_gaussian)) ↔
    localArena.Law localActual := Iff.rfl

def poissonArena : Arena where
  signature := expSignature
  Law R := ∀ {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ), A.PosDef →
    ∀ (b : ℂ), 0 < b.re →
      Summable (fun a : Fin r → ℤ => ‖R.readout () ()
        (-Real.pi * b * (quadratic A (fun i => (a i : ℝ)) : ℂ))‖) ∧
      Summable (fun k : Fin r → ℤ => ‖R.readout () ()
        (-Real.pi / b * (quadratic A⁻¹ (fun i => (k i : ℝ)) : ℂ))‖) ∧
      (∑' a : Fin r → ℤ, R.readout () ()
        (-Real.pi * b * (quadratic A (fun i => (a i : ℝ)) : ℂ))) =
      (Real.sqrt A.det : ℂ)⁻¹ * b ^ (-(r : ℂ) / 2) *
        ∑' k : Fin r → ℤ, R.readout () ()
          (-Real.pi / b * (quadratic A⁻¹ (fun i => (k i : ℝ)) : ℂ))

theorem poisson_bridge : (type_of% (@poisson_gaussian)) ↔ poissonArena.Law actual := Iff.rfl

end
end Reg.D5.S3.Fourier.MatrixGaussianPoisson
