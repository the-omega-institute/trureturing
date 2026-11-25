import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.AURICOmega.RationalGramCospectralFourCoordinates

/-! Parameter dependence in the four-coordinate criterion. -/

namespace Reg.D5.S3.Quantum.AURICOmega.RationalGramCospectralFourCoordinates

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.AURICOmega.RationalGramCospectral
open _root_.D5.S3.Quantum.AURICOmega.RationalGramCospectralFourCoordinates
open LeanInformationAudit

set_option autoImplicit false

noncomputable section

private abbrev fourCoordinateSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℚ) (fun _ => ℚ)

private def fourCoordinateActual : Realization fourCoordinateSignature :=
  realize fourCoordinateSignature (fun _ _ t => t) (fun e => nomatch e)

private def fourCoordinateRejected : Realization fourCoordinateSignature :=
  realize fourCoordinateSignature (fun _ _ t => t + 1 / 6) (fun e => nomatch e)

private abbrev fourCoordinateArena : Arena where
  signature := fourCoordinateSignature
  Law R := ∀ t : ℚ,
    (RealizableIn (pairedEdges (R.readout () () t)) 4 ↔
      t = 1/2 ∨ ∃ s x y : ℚ, 1 + 4*t = s^2 ∧ 2*(1-2*t) = x^2+y^2) ∧
    (RealizableIn (triangleBlock t) 4 ↔
      t = 1/2 ∨ ∃ s x y : ℚ, 1 + 4*t = s^2 ∧ 2*(1-2*t) = x^2+y^2)

private theorem four_coordinate_rejected_law : ¬ fourCoordinateArena.Law fourCoordinateRejected := by
  intro h
  have candidate := (h 0).1.mpr (Or.inr ⟨1, 1, 1, by norm_num, by norm_num⟩)
  change RealizableIn (pairedEdges (0 + 1/6)) 4 at candidate
  rw [zero_add] at candidate
  have known := (five_seven_on_conic 1 1 (by norm_num) (by norm_num) 4).1
  norm_num at known
  exact known candidate

def fourCoordinateFamily : Registration fourCoordinateArena (type_of% @four_coordinate_criterion) where
  actual := fourCoordinateActual
  bridge := Iff.rfl
  variation := ⟨@four_coordinate_criterion, fourCoordinateRejected, four_coordinate_rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity fourCoordinateArena.Law
      fourCoordinateActual fourCoordinateRejected four_coordinate_rejected_law
  dependence := fun _ => ⟨(), 0, 1, by
    change (0 : ℚ) ≠ 1
    norm_num⟩

def fourCoordinateAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@four_coordinate_criterion) (Realization fourCoordinateSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.AURICOmega.RationalGramCospectralFourCoordinates.fourCoordinateUnit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.RationalGramCospectralFourCoordinates.fourCoordinateFamily
  realizationSource := none
  generated := false
  arena := .source ⟨fourCoordinateArena⟩
  objectArena := .source ⟨fourCoordinateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fourCoordinateArena ⟨fourCoordinateFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fourCoordinateSignature (fun _ _ t => t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.RationalGramCospectralFourCoordinates
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.AURICOmega.RationalGramCospectralFourCoordinates
