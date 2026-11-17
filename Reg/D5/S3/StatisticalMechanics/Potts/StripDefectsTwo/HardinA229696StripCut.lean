import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripCut
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripCut
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripCut
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229588Strip (Row horizontal between)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
attribute [local irreducible] T initial terminal W cl
namespace LeadingCounts
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature (Fin 15) (fun _ => Fin 15) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ s r => T r s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ s r => T r s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Row) (d : Fin 3) (j : Fin 10),
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = j.castAdd 5
      then (1 : ℤ) else 0) = (fun r s => R.readout () s r) (cl p d.val) (j.castAdd 5)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 0, 0] 0 0
  have ha := leading_counts ![0, 0, 0] 0 0
  change _ = T (cl ![0, 0, 0] 0) ((0 : Fin 10).castAdd 5) + 1 at hb
  simp only [Fin.val_zero] at ha hb
  linarith
def family : Registration arena (type_of% @leading_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨leading_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change T 0 0 ≠ T 1 0
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@leading_counts) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229696Strip.leading_counts.auditUnit
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
  readout := some (realize signature (fun _ s r => T r s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripCut
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LeadingCounts

namespace TailCounts
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature (Fin 15) (fun _ => Fin 15) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ s r => T r s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ s r => T r s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Row) (d : Fin 2) (j : Fin 5),
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = j.natAdd 10
      then (1 : ℤ) else 0) = (fun r s => R.readout () s r) (cl p d.val) (j.natAdd 10)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 0, 0] 0 0
  have ha := tail_counts ![0, 0, 0] 0 0
  change _ = T (cl ![0, 0, 0] 0) ((0 : Fin 5).natAdd 10) + 1 at hb
  simp only [Fin.val_zero] at ha hb
  linarith
def family : Registration arena (type_of% @tail_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨tail_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change T 0 0 ≠ T 1 0
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@tail_counts) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229696Strip.tail_counts.auditUnit
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
  readout := some (realize signature (fun _ s r => T r s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripCut
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TailCounts

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229696StripCut
