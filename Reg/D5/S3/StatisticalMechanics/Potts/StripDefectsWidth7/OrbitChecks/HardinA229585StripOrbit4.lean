import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.OrbitChecks.HardinA229585StripOrbit4
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbit
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option profiler true

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.OrbitChecks.HardinA229585StripOrbit4
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.OrbitChecks.HardinA229585StripOrbit4
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbit
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
attribute [local irreducible] T images nextClasses
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 72) (fun _ => Multiset (Fin 72))
def readout : Realization signature := realize signature (fun _ u x => images x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ u x => images x + {(0 : Fin 72)}) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p : Boundary, ∀ d : Fin 2, Valid p d.val → Canonical p →
      32 ≤ (cl p d.val).val ∧ (cl p d.val).val < 40 →
      nextClasses p d.val = R.readout () () (cl p d.val)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 1, 0, 1, 1, 2] 0 (by decide +kernel) (by unfold Canonical; decide +kernel) (by decide +kernel)
  have ha := canonical_next ![0, 1, 0, 1, 1, 2] 0 (by decide +kernel) (by unfold Canonical; decide +kernel) (by decide +kernel)
  change _ = images (cl ![0, 1, 0, 1, 1, 2] 0) + {(0 : Fin 72)} at hb
  have he : images (cl ![0, 1, 0, 1, 1, 2] 0) =
      images (cl ![0, 1, 0, 1, 1, 2] 0) + {(0 : Fin 72)} := ha.symm.trans hb
  have hc := congrArg Multiset.card he
  simp only [Multiset.card_add, Multiset.card_singleton] at hc
  omega
def family : Registration arena (type_of% @canonical_next) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨canonical_next, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 32, 33, ?_⟩
    change images 32 ≠ images 33
    unfold images
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@canonical_next) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.OrbitChecks.HardinA229585StripOrbit4.auditUnit
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
  readout := some (realize signature (fun _ u x => images x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.OrbitChecks.HardinA229585StripOrbit4
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.OrbitChecks.HardinA229585StripOrbit4
