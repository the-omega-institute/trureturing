import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbitCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option profiler true

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbitCertificate
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbitCertificate
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
attribute [local irreducible] T
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 72) (fun _ => Fin 72) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ u x => T x u) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ u x => T x u + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p : Boundary, ∀ d : Fin 2, Valid p d.val → Canonical p → ∀ s : Fin 72,
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
      cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = R.readout () s (cl p d.val)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 1, 0, 1, 0, 1] 1 (by decide +kernel)
    (by unfold Canonical; decide +kernel) 0
  have ha := transition_counts ![0, 1, 0, 1, 0, 1] 1 (by decide +kernel)
    (by unfold Canonical; decide +kernel) 0
  change _ = T (cl ![0, 1, 0, 1, 0, 1] 1) 0 + 1 at hb
  have he : T (cl ![0, 1, 0, 1, 0, 1] 1) 0 =
      T (cl ![0, 1, 0, 1, 0, 1] 1) 0 + 1 := ha.symm.trans hb
  omega
def family : Registration arena (type_of% @transition_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change T 0 0 ≠ T 1 0
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbitCertificate.auditUnit
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
  readout := some (realize signature (fun _ u x => T x u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbitCertificate
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbitCertificate
