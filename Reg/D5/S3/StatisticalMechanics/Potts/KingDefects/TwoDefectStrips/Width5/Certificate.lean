import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Certificate
import Reg.Support.UniverseSingleReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The successor list is the varying observed value. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Certificate
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Certificate
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
set_option maxRecDepth 100000
noncomputable section
abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => Fin 43 × Fin 43) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ s => T s.1 s.2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ s => T s.1 s.2 + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Row) (d : ℕ), Valid p d → ∀ s : Fin 43,
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d ∧
      cl r (d - (bondDefects between p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = R.readout () () (cl p d,s)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let p : Row := ![0,1,0,1,0]
  have hp : Valid p 0 := by decide +kernel
  have hb := h p 0 hp 0
  have ha := transition_counts p 0 hp 0
  change _ = T (cl p 0) 0 + 1 at hb
  linarith only [hb,ha]
def family : Registration arena (type_of% @transition_counts) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨transition_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro ⟨⟩
    refine ⟨(), (0,0), (0,1), ?_⟩
    change T 0 0 ≠ T 0 1
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts) (Realization signature) Type Unit where
  unitName := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Certificate.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Certificate
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "arg"]
                    stateBinder := 3
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Certificate
