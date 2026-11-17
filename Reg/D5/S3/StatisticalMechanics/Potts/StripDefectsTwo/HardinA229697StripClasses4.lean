import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripClasses4
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripClasses4
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripClasses4
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripData (Row horizontal between)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
attribute [local irreducible] T initial terminal W cl
namespace TransitionCounts
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature (Fin 42) (fun _ => Fin 42) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ s r => T r s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ s r => T r s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (j : Fin 14), 8 ≤ j.val ∧ j.val < 10 →
    ∀ p : Row,
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ 2 ∧
        cl r (2 - (bondDefects between p r + bondDefects horizontal r r)) = j.natAdd 28
        then (1 : ℤ) else 0) = (fun r s => R.readout () s r) (cl p 2) (j.natAdd 28)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 8 (by decide) ![0, 0, 0, 0]
  have ha := transition_counts 8 (by decide) ![0, 0, 0, 0]
  change _ = T (cl ![0, 0, 0, 0] 2) ((8 : Fin 14).natAdd 28) + 1 at hb
  simp only [Fin.val_zero] at ha hb
  linarith
def family : Registration arena (type_of% @transition_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨36, 0, 1, ?_⟩
    change T 0 36 ≠ T 1 36
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229697Strip.transition_counts.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripClasses4
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TransitionCounts

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripClasses4
