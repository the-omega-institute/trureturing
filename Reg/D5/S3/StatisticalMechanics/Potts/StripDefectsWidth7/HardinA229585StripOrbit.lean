import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbit
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option profiler true

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbit
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbit
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbit
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
attribute [local irreducible] T images nextClasses
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 72) (fun _ => Multiset (Fin 72)) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ u x => (x.count u : ℤ)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ u x => (x.count u : ℤ) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p : Boundary, ∀ d : ℕ, ∀ s : Fin 72,
    (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d ∧
      cl (boundary r) (d - (cross p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = R.readout () s (nextClasses p d)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 1, 0, 1, 0, 1] 1 0
  have ha := sum_count ![0, 1, 0, 1, 0, 1] 1 0
  change _ = ((nextClasses ![0, 1, 0, 1, 0, 1] 1).count 0 : ℤ) + 1 at hb
  linarith
def family : Registration arena (type_of% @sum_count) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨sum_count, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, nextClasses ![0, 1, 0, 1, 0, 1] 1,
      nextClasses ![0, 1, 0, 1, 0, 1] 0, ?_⟩
    change ((nextClasses ![0, 1, 0, 1, 0, 1] 1).count 0 : ℤ) ≠
      ((nextClasses ![0, 1, 0, 1, 0, 1] 0).count 0 : ℤ)
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@sum_count) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbit.auditUnit
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
  readout := some (realize signature (fun _ u x => (x.count u : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbit
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripOrbit
