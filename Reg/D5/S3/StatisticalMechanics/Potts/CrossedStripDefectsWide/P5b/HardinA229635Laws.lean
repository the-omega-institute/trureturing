import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Laws
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Observations of canonical representatives and inherited terminal weights. -/

namespace Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Laws

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Laws
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix

noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 0

local instance (p : Row) : Decidable (Canonical p) := by
  unfold Canonical
  infer_instance

namespace RepresentativesComplete

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Row) (fun _ => Row)

private def observation : ∀ role p, signature.State p → signature.Output role p :=
  (fun _ _ p => rep (fresh p))

private def actual : Realization signature :=
  realize signature observation (fun e => nomatch e)

private def altered : Realization signature :=
  realize signature (fun _ _ _ => (![0, 0, 0, 0, 0, 0] : Row)) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Row), Canonical p → h p ≤ 2 → R.readout () () p = p

private theorem rejected : ¬ arena.Law altered := by
  intro hfalse
  have wrong := hfalse (![0, 1, 0, 1, 0, 1] : Row) (by decide +kernel) (by decide +kernel)
  exact (by decide +kernel : (![0, 0, 0, 0, 0, 0] : Row) ≠ (![0, 1, 0, 1, 0, 1] : Row)) wrong

def family : Registration arena (type_of% @representatives_complete) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨representatives_complete, altered, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual altered rejected
  dependence := by
    intro role
    refine ⟨(), (![0, 1, 0, 1, 0, 1] : Row), (![0, 0, 0, 1, 0, 1] : Row), ?_⟩
    change rep (fresh (![0, 1, 0, 1, 0, 1] : Row)) ≠ rep (fresh (![0, 0, 0, 1, 0, 1] : Row))
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@representatives_complete) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229635Laws.representatives_complete.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Laws
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RepresentativesComplete


end

end Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Laws
