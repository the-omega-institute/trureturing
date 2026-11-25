import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Literal
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Observation of the literal labelled count entering the six-to-one identity. -/

namespace Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Literal

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Literal
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (literalCount)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (horizontal)
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.WidthSix.HardinA229532StripData (between)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects

noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem labelled_zero : literalCount (q := 3) horizontal between 2 0 = 0 := by
  decide +kernel

private theorem canonical_positive : 0 < HardinA229637RowColumn.T 1 6 := by
  unfold HardinA229637RowColumn.T
  apply Finset.card_pos.mpr
  refine ⟨(fun x => ![0, 0, 0, 1, 0, 1] x.2), ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, by decide +kernel⟩

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

private def observation : ∀ role p, signature.State p → signature.Output role p :=
  (fun _ _ n => literalCount (q := 3) horizontal between 2 n)

private def actual : Realization signature :=
  realize signature observation (fun e => nomatch e)

private def altered : Realization signature :=
  realize signature (fun _ _ n => literalCount (q := 3) horizontal between 2 n + 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ), R.readout () () (m + 1) = 6 * HardinA229637RowColumn.T (m + 1) 6

private theorem rejected : ¬ arena.Law altered := by
  intro h
  have wrong := h 0
  have right := six_labellings 0
  change literalCount (q := 3) horizontal between 2 1 + 1 = _ at wrong
  change literalCount (q := 3) horizontal between 2 1 = _ at right
  omega

def family : Registration arena (type_of% @six_labellings) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨six_labellings, altered, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual altered rejected
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change literalCount (q := 3) horizontal between 2 0 ≠
      literalCount (q := 3) horizontal between 2 1
    rw [labelled_zero, six_labellings 0]
    exact Nat.ne_of_lt (Nat.mul_pos (by decide) canonical_positive)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@six_labellings) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229635Literal.six_labellings.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Literal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Literal
