import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass27
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass27
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass27
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 72) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ _ r => T r 27) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ r => T r 27 + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p : Boundary, Valid p 1 → Canonical p →
      (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ 1 ∧
        cl (boundary r) (1 - (cross p r + bondDefects horizontal r r)) = (27 : Fin 72)
        then (1 : ℤ) else 0) = (fun x => R.readout () () x) (cl p 1)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 1, 0, 1, 0, 1] (by decide +kernel) (by unfold Canonical; decide +kernel)
  have ha := transition_counts ![0, 1, 0, 1, 0, 1] (by decide +kernel) (by unfold Canonical; decide +kernel)
  change _ = T (cl ![0, 1, 0, 1, 0, 1] 1) 27 + 1 at hb
  linarith
def family : Registration arena (type_of% @transition_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 2, ?_⟩
    change T 0 27 ≠ T 2 27
    unfold T
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass27.auditUnit
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
  readout := some (realize signature (fun _ _ r => T r 27) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass27
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Budget1.Block1.HardinA229585StripClass27
