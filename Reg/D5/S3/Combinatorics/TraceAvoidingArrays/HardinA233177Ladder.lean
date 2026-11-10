import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact sequence readouts for the literal ladder count and its pair-label transfer. -/
namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer (L initial_values)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
attribute [local irreducible] a L

namespace Bridge
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (a n : ℤ) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 2 ≤ n → 48 * R.readout () () n =
      (16 : ℤ)^n * ((L n : ℤ) + 6)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := counting_bridge (n := 2) (by decide)
  have hb := h (n := 2) (by decide)
  change 48 * ((a 2 : ℤ) + 1) = (16 : ℤ)^2 * ((L 2 : ℤ) + 6) at hb
  linarith only [ha, hb]
private theorem actual_dependence :
    actual.readout () () 2 ≠ actual.readout () () 3 := by
  have h2 := counting_bridge (n := 2) (by decide)
  have h3 := counting_bridge (n := 3) (by decide)
  have hL2 : (L 2 : ℤ) = 162 := initial_values 0
  have hL3 : (L 3 : ℤ) = 1122 := initial_values 1
  rw [hL2] at h2
  rw [hL3] at h3
  change 48 * (a 2 : ℤ) = 43008 at h2
  change 48 * (a 3 : ℤ) = 4620288 at h3
  change (a 2 : ℤ) ≠ (a 3 : ℤ)
  omega
def family : Registration arena (type_of% @counting_bridge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@counting_bridge, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 2, 3, actual_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@counting_bridge) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder.Bridge.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder.Bridge.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Bridge

namespace Base
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (a n : ℤ) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (0+9) =
      64 * R.readout () () (0+8) + 3328 * R.readout () () (0+7) -
        77824 * R.readout () () (0+6) - 1441792 * R.readout () () (0+5) +
        28311552 * R.readout () () (0+4) + 33554432 * R.readout () () (0+3) -
        1073741824 * R.readout () () (0+2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := finite_certificate
  change (fun n => (a n : ℤ) + 1) (0+9) =
      64 * (fun n => (a n : ℤ) + 1) (0+8) + 3328 * (fun n => (a n : ℤ) + 1) (0+7) -
        77824 * (fun n => (a n : ℤ) + 1) (0+6) - 1441792 * (fun n => (a n : ℤ) + 1) (0+5) +
        28311552 * (fun n => (a n : ℤ) + 1) (0+4) + 33554432 * (fun n => (a n : ℤ) + 1) (0+3) -
        1073741824 * (fun n => (a n : ℤ) + 1) (0+2) at h
  norm_num only [Nat.reduceAdd] at h
  linarith only [ha, h]
private theorem actual_dependence :
    actual.readout () () 2 ≠ actual.readout () () 3 := by
  have h2 := counting_bridge (n := 2) (by decide)
  have h3 := counting_bridge (n := 3) (by decide)
  have hL2 : (L 2 : ℤ) = 162 := initial_values 0
  have hL3 : (L 3 : ℤ) = 1122 := initial_values 1
  rw [hL2] at h2
  rw [hL3] at h3
  change 48 * (a 2 : ℤ) = 43008 at h2
  change 48 * (a 3 : ℤ) = 4620288 at h3
  change (a 2 : ℤ) ≠ (a 3 : ℤ)
  omega
def family : Registration arena (type_of% @finite_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 2, 3, actual_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder.Base.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder.Base.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Base

namespace Recurrence
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (a n : ℤ) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () (n+9) =
      64 * R.readout () () (n+8) + 3328 * R.readout () () (n+7) -
        77824 * R.readout () () (n+6) - 1441792 * R.readout () () (n+5) +
        28311552 * R.readout () () (n+4) + 33554432 * R.readout () () (n+3) -
        1073741824 * R.readout () () (n+2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := result 0
  have hb := h 0
  change (fun n => (a n : ℤ) + 1) (0+9) =
      64 * (fun n => (a n : ℤ) + 1) (0+8) + 3328 * (fun n => (a n : ℤ) + 1) (0+7) -
        77824 * (fun n => (a n : ℤ) + 1) (0+6) - 1441792 * (fun n => (a n : ℤ) + 1) (0+5) +
        28311552 * (fun n => (a n : ℤ) + 1) (0+4) + 33554432 * (fun n => (a n : ℤ) + 1) (0+3) -
        1073741824 * (fun n => (a n : ℤ) + 1) (0+2) at hb
  norm_num only [Nat.reduceAdd] at hb
  linarith only [ha, hb]
private theorem actual_dependence :
    actual.readout () () 2 ≠ actual.readout () () 3 := by
  have h2 := counting_bridge (n := 2) (by decide)
  have h3 := counting_bridge (n := 3) (by decide)
  have hL2 : (L 2 : ℤ) = 162 := initial_values 0
  have hL3 : (L 3 : ℤ) = 1122 := initial_values 1
  rw [hL2] at h2
  rw [hL3] at h3
  change 48 * (a 2 : ℤ) = 43008 at h2
  change 48 * (a 3 : ℤ) = 4620288 at h3
  change (a 2 : ℤ) ≠ (a 3 : ℤ)
  omega
def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 2, 3, actual_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder.Recurrence.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder.Recurrence.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Recurrence
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder
