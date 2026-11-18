import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripClasses3
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripClasses3
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripClasses3
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature (Fin 28) (fun _ => Fin 28) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ s r => T r s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ s r => T r s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (s : Fin 28) , 6 ≤ s.val ∧ s.val < 8 →
    ∀ p (d : Fin 2), Valid p d.val →
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = (fun x y => R.readout () y x) (cl p d.val) s
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 6 (by decide) ![0, 0, 0, 0] ⟨1, by decide⟩ (by decide +kernel)
  have ha := transition_counts 6 (by decide) ![0, 0, 0, 0] ⟨1, by decide⟩ (by decide +kernel)
  change _ = T (cl ![0, 0, 0, 0] 1) 6 + 1 at hb
  linarith
def family : Registration arena (type_of% @transition_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨6, 0, 1, ?_⟩
    change T 0 6 ≠ T 1 6
    unfold T
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229589StripClasses3.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripClasses3
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripClasses3
