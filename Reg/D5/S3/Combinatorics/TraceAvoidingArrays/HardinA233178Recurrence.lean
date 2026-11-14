import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Recurrence
import Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Complete source count and recurrence telescopes as dependent-family laws. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Recurrence
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Recurrence
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Chromatic (Column v)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def chromaticActual : Realization signature :=
  realize signature (fun _ _ n => chromaticCount n) (fun e => nomatch e)
private theorem chromatic_dependence :
    chromaticActual.readout () () 0 ≠ chromaticActual.readout () () 1 := by
  change chromaticCount 0 ≠ chromaticCount 1
  have h0 : chromaticCount 0 = 1 := by
    simp [chromaticCount, Proper,
      _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal.Array]
  have h1 := count_transfer 0
  norm_num [v, Matrix.one_mulVec, dotProduct] at h1
  rw [h0,h1]
  norm_num

namespace Transfer
def rejected : Realization signature :=
  realize signature (fun _ _ n => chromaticCount n + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () (n+1) = dotProduct (1 : Column → ℤ) (v n)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := count_transfer 0
  have hb := h 0
  dsimp only [rejected, realize] at hb
  norm_num only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceEqDiff, ite_true, ite_false] at hb
  linarith
def family : Registration arena (type_of% @count_transfer) where
  actual := chromaticActual
  bridge := Iff.rfl
  variation := ⟨count_transfer, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law chromaticActual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 0, 1, chromatic_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@count_transfer) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Recurrence.Transfer.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Recurrence.Transfer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => chromaticCount n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Recurrence
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
end Transfer

namespace Chromatic
def rejected : Realization signature :=
  realize signature (fun _ _ n => chromaticCount n + if n = 12 then 1 else 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () (n+12) = 6 * R.readout () () (n+11) + 31 * R.readout () () (n+10) - 97 * R.readout () () (n+9) - 163 * R.readout () () (n+8) + 417 * R.readout () () (n+7) + 93 * R.readout () () (n+6) - 514 * R.readout () () (n+5) + 192 * R.readout () () (n+4) + 72 * R.readout () () (n+3) - 36 * R.readout () () (n+2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := chromatic_recurrence 0
  have hb := h 0
  dsimp only [rejected, realize] at hb
  norm_num only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceEqDiff, ite_true, ite_false] at hb
  linarith
def family : Registration arena (type_of% @chromatic_recurrence) where
  actual := chromaticActual
  bridge := Iff.rfl
  variation := ⟨chromatic_recurrence, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law chromaticActual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 0, 1, chromatic_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@chromatic_recurrence) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Recurrence.Chromatic.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Recurrence.Chromatic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => chromaticCount n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Recurrence
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
end Chromatic

namespace Literal
def rejected : Realization signature :=
  realize signature (fun _ _ n => (a n : ℤ) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (_ : n > 11), R.readout () () n = 192 * R.readout () () (n-1) + 31744 * R.readout () () (n-2) - 3178496 * R.readout () () (n-3) - 170917888 * R.readout () () (n-4) + 13992198144 * R.readout () () (n-5) + 99857989632 * R.readout () () (n-6) - 17660905521152 * R.readout () () (n-7) + 211106232532992 * R.readout () () (n-8) + 2533274790395904 * R.readout () () (n-9) - 40532396646334464 * R.readout () () (n-10)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := result 12 (by decide)
  have hb := h 12 (by decide)
  dsimp only [rejected, realize] at hb
  norm_num only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceEqDiff, ite_true, ite_false] at hb
  linarith
def family : Registration arena (type_of% @result) where
  actual := _root_.Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal.actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law _root_.Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal.actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 2, 10, _root_.Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal.actual_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Recurrence.Literal.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Recurrence.Literal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Recurrence
    definition := some {
      owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal
      name := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Literal.FullE
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Literal

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Recurrence
