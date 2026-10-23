import Reg.D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection
import D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace SectorTranslation

abbrev signature := _root_.Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.UnitCorrection.signature
abbrev actual := _root_.Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.UnitCorrection.actual

def rejected : Realization signature := realize signature (fun _ _ _ => Finsupp.single 0 1)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (charge : Charge D) (polynomial : Oscillator D),
    readout.readout () ⟨D, charge⟩
        (_root_.D5.S3.VertexAlgebra.LatticeSugawaraConformal.sectorTranslation D charge polynomial) =
      shiftCoefficients D ((MvPolynomial.optionEquivLeft ℂ (Index D))
        (correctionConnection D charge (correctedSource D charge polynomial) +
          ∑ colour : Fin D.rank, (charge colour : ℂ) •
            insertion D charge (colour, 0) (correctedSource D charge polynomial)))

theorem source_bridge : (type_of% (@Corr_sectorTranslation)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨parameter, first, second, different⟩ :=
    _root_.Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.MonomialEnumeration.familyRegistration.dependence ()
  have contradiction := law parameter.1 parameter.2 0
  have value := congrArg (fun coefficients : ℕ →₀ Oscillator parameter.1 => coefficients 0) contradiction
  simpa [rejected, realize] using value

def familyRegistration : Registration arena (type_of% (@Corr_sectorTranslation)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp Corr_sectorTranslation, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := _root_.Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.MonomialEnumeration.familyRegistration.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Corr_sectorTranslation) (type_of% (realize signature actual.readout actual.anchor))
    (type_of% (@Corr)) Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation.Corr_sectorTranslation "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation.SectorTranslation.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end SectorTranslation
end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockCorrectionTranslation
