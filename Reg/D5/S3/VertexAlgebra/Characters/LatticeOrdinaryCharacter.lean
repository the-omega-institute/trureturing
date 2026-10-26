import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Characters.LatticeOrdinaryCharacter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
open LeanInformationAudit Complex
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.LatticeOrdinaryCharacter
open _root_.D5.S3.Arith.Lattices.LatticeThetaTransformation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.VertexAlgebra.LatticeOrdinaryCharacter

/-- Actual label energies, with their original dependent charge/occupation domain. -/
abbrev energySignature : Signature where
  Params := LatticeData
  State D := Label D
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualEnergy : Realization energySignature :=
  realize energySignature (fun _ D a => energy D a) (fun e => nomatch e)

/-- Literal Sugawara eigenspaces, rather than a Boolean encoding of their properties. -/
abbrev gradeSignature : Signature where
  Params := LatticeData
  State D := Matrix (Fin D.rank) (Fin D.rank) ℂ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ D := Submodule ℂ (Carrier D)
  Anchor := Empty
  finiteAnchor := inferInstance

def actualGrade : Realization gradeSignature :=
  realize gradeSignature
    (fun _ D p => (sugawaraMode D p.1 0).eigenspace (p.2 : ℂ))
    (fun e => nomatch e)

namespace NaturalFiber
abbrev arena : Arena where
  signature := energySignature
  Law R := ∀ (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (N : ℕ),
    Finite {a : Label D // (R.readout () D a).toNat = N}

theorem source_bridge : (type_of% (@naturalEnergyFiber_finite)) ↔
    arena.Law actualEnergy := Iff.rfl
end NaturalFiber

namespace FiniteGrade
abbrev arena : Arena where
  signature := gradeSignature
  Law R := ∀ (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (N : ℕ),
    FiniteDimensional ℂ (R.readout () D (H, N))

theorem source_bridge : (type_of% (@actualOrdinaryGrade_finiteDimensional)) ↔
    arena.Law actualGrade := Iff.rfl
end FiniteGrade

namespace Coefficient
abbrev arena : Arena where
  signature := gradeSignature
  Law R := ∀ (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (N : ℕ),
    Module.finrank ℂ (R.readout () D (H, N)) = Nat.card (EnergyFiber D (N : ℤ))

theorem source_bridge : (type_of% (@actualOrdinaryCoefficient_eq_card)) ↔
    arena.Law actualGrade := Iff.rfl
end Coefficient

namespace LabelSeries
abbrev arena : Arena where
  signature := energySignature
  Law R := ∀ (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (τ : ℂ) (hτ : 0 < τ.im),
    Summable (fun a : Label D =>
      ‖exp (2 * Real.pi * I * τ) ^ (R.readout () D a).toNat‖) ∧
    (∑' a : Label D, exp (2 * Real.pi * I * τ) ^ (R.readout () D a).toNat) =
      latticeTheta D τ *
        (∑' d : Exponent D, exp (2 * Real.pi * I * τ) ^ oscillatorEnergy d)

theorem source_bridge : (type_of% (@ordinary_label_series)) ↔
    arena.Law actualEnergy := Iff.rfl
end LabelSeries

namespace DimensionSeries
abbrev arena : Arena where
  signature := gradeSignature
  Law R := ∀ (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (τ : ℂ) (hτ : 0 < τ.im),
    Summable (fun N : ℕ =>
      ‖(Module.finrank ℂ (R.readout () D (H, N)) : ℂ) *
        exp (2 * Real.pi * I * τ) ^ N‖) ∧
    HasSum (fun N : ℕ =>
      (Module.finrank ℂ (R.readout () D (H, N)) : ℂ) *
        exp (2 * Real.pi * I * τ) ^ N)
      (latticeTheta D τ *
        (∑' d : Exponent D, exp (2 * Real.pi * I * τ) ^ oscillatorEnergy d))

theorem source_bridge : (type_of% (@actual_ordinary_series)) ↔
    arena.Law actualGrade := Iff.rfl
end DimensionSeries

namespace Character
abbrev arena : Arena where
  signature := gradeSignature
  Law R := ∀ (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (τ : ℂ) (hτ : 0 < τ.im),
    Summable (fun N : ℕ =>
      ‖exp (-2 * Real.pi * I * τ * D.rank / 24) *
        ((Module.finrank ℂ (R.readout () D (H, N)) : ℂ) *
          exp (2 * Real.pi * I * τ) ^ N)‖) ∧
    HasSum (fun N : ℕ =>
      exp (-2 * Real.pi * I * τ * D.rank / 24) *
        ((Module.finrank ℂ (R.readout () D (H, N)) : ℂ) *
          exp (2 * Real.pi * I * τ) ^ N))
      (latticeTheta D τ / (ModularForm.eta τ) ^ D.rank) ∧
    exp (-2 * Real.pi * I * τ * D.rank / 24) *
      (∑' N : ℕ, (Module.finrank ℂ (R.readout () D (H, N)) : ℂ) *
        exp (2 * Real.pi * I * τ) ^ N) =
      latticeTheta D τ / (ModularForm.eta τ) ^ D.rank

theorem source_bridge : (type_of% (@actual_ordinary_character)) ↔
    arena.Law actualGrade := Iff.rfl
end Character

end Reg.D5.S3.VertexAlgebra.LatticeOrdinaryCharacter
