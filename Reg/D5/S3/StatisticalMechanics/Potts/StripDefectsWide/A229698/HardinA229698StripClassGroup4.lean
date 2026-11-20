import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripClassGroup4
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripData
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripClassGroup4
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripClassGroup4

noncomputable section
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 41) (fun _ => Fin 41 → ℤ)
def readout : Realization signature := realize signature (fun _ _ k => S k) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ k => S k + Pi.single 0 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (k : Fin 6) (s : Fin 41),
    (∑ c : Col, if HardinA229590StripData.cross (representatives ⟨24+k.val, by omega⟩)
      (column c) = 2 ∧ cls c = s then (1 : ℤ) else 0) = A.readout () () (⟨24+k.val, by omega⟩ : Fin 41) s
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 0
  have ha := representative_rows 0 0
  change (∑ c : Col, if HardinA229590StripData.cross (representatives ⟨24, by omega⟩)
      (column c) = 2 ∧ cls c = 0 then (1 : ℤ) else 0) = S ⟨24, by omega⟩ 0 at ha
  change (∑ c : Col, if HardinA229590StripData.cross (representatives ⟨24, by omega⟩)
      (column c) = 2 ∧ cls c = 0 then (1 : ℤ) else 0) = S ⟨24, by omega⟩ 0 + 1 at hb
  linarith
def family : Registration arena (type_of% @representative_rows) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨representative_rows, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 24, 25, ?_⟩
    intro he
    have hh := congrFun he 0
    exact (by decide +kernel : S 24 0 ≠ S 25 0) hh
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@representative_rows) (Realization signature) Type Unit where
  unitName := `Reg.A229698HardinA229698StripClassGroup4.auditUnit
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
  readout := some (realize signature (fun _ _ k => S k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripClassGroup4
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripClassGroup4
