import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation
open scoped BigOperators

noncomputable section

structure Parameters where
  lattice : LatticeData
  charge : Charge lattice

def signature : Signature where
  Params := Parameters
  State parameter := Oscillator parameter.lattice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := (ℕ →₀ Oscillator parameter.lattice) × (ℕ →₀ Oscillator parameter.lattice)
  Anchor := Empty
  finiteAnchor := inferInstance

def correctionReadout : Realization signature :=
  realize signature (fun _ parameter polynomial =>
    (Corr parameter.lattice parameter.charge
      (_root_.D5.S3.VertexAlgebra.LatticeSugawaraConformal.sectorTranslation
        parameter.lattice parameter.charge polynomial),
      shiftCoefficients parameter.lattice
        ((MvPolynomial.optionEquivLeft ℂ (Index parameter.lattice))
          (correctionConnection parameter.lattice parameter.charge
              (correctedSource parameter.lattice parameter.charge polynomial) +
            ∑ colour : Fin parameter.lattice.rank, (parameter.charge colour : ℂ) •
              insertion parameter.lattice parameter.charge (colour, 0)
                (correctedSource parameter.lattice parameter.charge polynomial)))))
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ parameter polynomial,
    (observation.readout () parameter polynomial).1 =
      (observation.readout () parameter polynomial).2

theorem correctionBridge : (type_of% (@Corr_sectorTranslation)) ↔
    arena.Law correctionReadout := by
  constructor
  · intro source parameter polynomial
    exact source parameter.lattice parameter.charge polynomial
  · intro law lattice charge polynomial
    exact law ⟨lattice, charge⟩ polynomial

def escapeFrom := @Corr
def continuation : Contract.Continuation Unit := .unknown

abbrev correctionRealizationObligation := Registration arena
  (type_of% (@Corr_sectorTranslation))
abbrev correctionContractObligation := Contract.Registration (@Corr_sectorTranslation)
  (type_of% correctionReadout) (type_of% escapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation
