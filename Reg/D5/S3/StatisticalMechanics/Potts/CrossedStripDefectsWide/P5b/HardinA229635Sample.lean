import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sample
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Observations of the tabulated successors at the three selected fresh indices. -/

namespace Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sample

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sample
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows


noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Row0

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fresh) (fun _ => List State)

private def observation : ∀ role p, signature.State p → signature.Output role p :=
  (fun _ _ k => weights k)

private def actual : Realization signature :=
  realize signature observation (fun e => nomatch e)

private def altered : Realization signature :=
  realize signature (fun _ p k => 0 :: observation () p k) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := outgoing (rep 0) (budget 0) = R.readout () () 0

private theorem rejected : ¬ arena.Law altered := by
  intro wrong
  change outgoing (rep 0) (budget 0) = 0 :: weights 0 at wrong
  rw [row_0] at wrong
  have lengths := congrArg List.length wrong
  simp at lengths

def family : Registration arena (type_of% @row_0) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨row_0, altered, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual altered rejected
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change weights 0 ≠ weights 1
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@row_0) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229635Sample.row_0.auditUnit
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
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sample
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Row0

namespace Row40

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fresh) (fun _ => List State)

private def observation : ∀ role p, signature.State p → signature.Output role p :=
  (fun _ _ k => weights k)

private def actual : Realization signature :=
  realize signature observation (fun e => nomatch e)

private def altered : Realization signature :=
  realize signature (fun _ p k => 0 :: observation () p k) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := outgoing (rep 40) (budget 40) = R.readout () () 40

private theorem rejected : ¬ arena.Law altered := by
  intro wrong
  change outgoing (rep 40) (budget 40) = 0 :: weights 40 at wrong
  rw [row_40] at wrong
  have lengths := congrArg List.length wrong
  simp at lengths

def family : Registration arena (type_of% @row_40) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨row_40, altered, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual altered rejected
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change weights 0 ≠ weights 1
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@row_40) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229635Sample.row_40.auditUnit
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
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sample
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Row40

namespace Row80

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fresh) (fun _ => List State)

private def observation : ∀ role p, signature.State p → signature.Output role p :=
  (fun _ _ k => weights k)

private def actual : Realization signature :=
  realize signature observation (fun e => nomatch e)

private def altered : Realization signature :=
  realize signature (fun _ p k => 0 :: observation () p k) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := outgoing (rep 80) (budget 80) = R.readout () () 80

private theorem rejected : ¬ arena.Law altered := by
  intro wrong
  change outgoing (rep 80) (budget 80) = 0 :: weights 80 at wrong
  rw [row_80] at wrong
  have lengths := congrArg List.length wrong
  simp at lengths

def family : Registration arena (type_of% @row_80) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨row_80, altered, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual altered rejected
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change weights 0 ≠ weights 1
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@row_80) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229635Sample.row_80.auditUnit
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
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sample
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Row80


end

end Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sample
