import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripClasses5
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripClasses5
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripClasses5
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripData (Row horizontal between)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
attribute [local irreducible] T initial terminal W cl
namespace TransitionCounts
/- signature: proof_shape=bind-only; consumers=readout,rejected,arena,family,audit -/
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 42) (fun _ => Fin 42 → ℤ)
/- readout: proof_shape=bind-only; consumers=family,audit -/
def readout : Realization signature := realize signature (fun _ _ r s => T r s) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=rejected_law,family -/
def rejected : Realization signature := realize signature (fun _ _ r s => T r s + 1) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=rejected_law,family,audit -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (j : Fin 14), 10 ≤ j.val ∧ j.val < 12 →
    ∀ p : Row,
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ 2 ∧
        cl r (2 - (bondDefects between p r + bondDefects horizontal r r)) = j.natAdd 28
        then (1 : ℤ) else 0) = (fun r s => R.readout () () r s) (cl p 2) (j.natAdd 28)
/- rejected_law: proof_shape=bind-only; consumers=family -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 10 (by decide) ![0, 0, 0, 0]
  have ha := transition_counts 10 (by decide) ![0, 0, 0, 0]
  change _ = T (cl ![0, 0, 0, 0] 2) ((10 : Fin 14).natAdd 28) + 1 at hb
  linarith
/- family: proof_shape=bind-only; consumers=audit -/
def family : Registration arena (type_of% @transition_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have he := congrFun h 38
    exact (by decide +kernel : T 0 38 ≠ T 1 38) he
/- audit: proof_shape=bind-only; consumers=LeanInformationAudit registration extraction -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229697StripClasses5.transition_counts.auditUnit
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
  readout := some (realize signature (fun _ _ r s => T r s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripClasses5
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TransitionCounts

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripClasses5
