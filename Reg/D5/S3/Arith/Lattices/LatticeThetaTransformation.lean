import Reg.D5.S3.Fourier.MatrixGaussianTheta
import D5.S3.Arith.Lattices.LatticeThetaTransformation

open Matrix
open scoped BigOperators
open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.Arith.Lattices.LatticeThetaTransformation
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.Lattices.LatticeThetaTransformation
noncomputable section
open Reg.D5.S3.Fourier.MatrixGaussianTheta

def reindexArena : Arena where
  signature := thetaSignature
  Law R := ∀ {r : ℕ} (G : Matrix (Fin r) (Fin r) ℤ),
    (G.map (Int.castRingHom ℝ)).PosDef → IsUnit G.det → ∀ τ : ℂ,
      R.readout () ⟨r, (G.map (Int.castRingHom ℝ))⁻¹⟩ τ =
        R.readout () ⟨r, G.map (Int.castRingHom ℝ)⟩ τ

theorem reindex_bridge : (type_of% (@theta_inverse_integer_reindex)) ↔
    reindexArena.Law thetaActual := Iff.rfl

abbrev latticeSignature : Signature where
  Params := LatticeData
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def latticeActual : Realization latticeSignature :=
  realize latticeSignature (fun _ D τ => latticeTheta D τ) (fun e => nomatch e)

def latticeArena : Arena where
  signature := latticeSignature
  Law R := ∀ (D : LatticeData), (D.G.map (Int.castRingHom ℝ)).PosDef →
    IsUnit D.G.det → ∀ m : ℕ, D.rank = m + m → ∀ τ : ℂ, 0 < τ.im →
      Summable (fun a : Charge D =>
        ‖Complex.exp (Real.pi * Complex.I * τ * (bilinear D a a : ℂ))‖) ∧
      R.readout () D (-1 / τ) = (-Complex.I * τ) ^ m * R.readout () D τ

theorem lattice_bridge : (type_of% (@lattice_theta_S)) ↔
    latticeArena.Law latticeActual := Iff.rfl

end
end Reg.D5.S3.Arith.Lattices.LatticeThetaTransformation
