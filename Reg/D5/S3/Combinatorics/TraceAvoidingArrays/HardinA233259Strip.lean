/- Declaration classifications for the retained registration evidence.
Bridge.signature: proof_shape=bind-only; consumers=Bridge.actual, Bridge.rejected, Bridge.arena, Bridge.family, Bridge.audit
Bridge.actual: proof_shape=bind-only; consumers=Bridge.actual_dependence, Bridge.family
Bridge.rejected: proof_shape=bind-only; consumers=Bridge.rejected_law, Bridge.family
Bridge.arena: proof_shape=bind-only; consumers=Bridge.rejected_law, Bridge.family, Bridge.audit
Bridge.rejected_law: proof_shape=bind-only; consumers=Bridge.family
Bridge.actual_dependence: proof_shape=bind-only; consumers=Bridge.family
Bridge.family: proof_shape=bind-only; consumers=Bridge.audit
Bridge.audit: proof_shape=bind-only; consumers=compiled-registration-reader
Base.signature: proof_shape=bind-only; consumers=Base.actual, Base.rejected, Base.arena, Base.family, Base.audit
Base.actual: proof_shape=bind-only; consumers=Base.actual_dependence, Base.family
Base.rejected: proof_shape=bind-only; consumers=Base.rejected_law, Base.family
Base.arena: proof_shape=bind-only; consumers=Base.rejected_law, Base.family, Base.audit
Base.rejected_law: proof_shape=bind-only; consumers=Base.family
Base.actual_dependence: proof_shape=bind-only; consumers=Base.family
Base.family: proof_shape=bind-only; consumers=Base.audit
Base.audit: proof_shape=bind-only; consumers=compiled-registration-reader
Recurrence.signature: proof_shape=bind-only; consumers=Recurrence.actual, Recurrence.rejected, Recurrence.arena, Recurrence.family, Recurrence.audit
Recurrence.actual: proof_shape=bind-only; consumers=Recurrence.actual_dependence, Recurrence.family
Recurrence.rejected: proof_shape=bind-only; consumers=Recurrence.rejected_law, Recurrence.family
Recurrence.arena: proof_shape=bind-only; consumers=Recurrence.rejected_law, Recurrence.family, Recurrence.audit
Recurrence.rejected_law: proof_shape=bind-only; consumers=Recurrence.family
Recurrence.actual_dependence: proof_shape=bind-only; consumers=Recurrence.family
Recurrence.family: proof_shape=bind-only; consumers=Recurrence.audit
Recurrence.audit: proof_shape=bind-only; consumers=compiled-registration-reader
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferBase
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259Strip
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259Strip
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259Strip
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore (L)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferBase (initial_values)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
attribute [local irreducible] a L

namespace Bridge
abbrev signature : Signature.{0, 0, 0, 0, 0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature := realize signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ n => (a n : ℤ) + 1) (fun e => nomatch e)
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
private theorem actual_dependence : actual.readout () () 2 ≠ actual.readout () () 3 := by
  have h2 := counting_bridge (n := 2) (by decide)
  have h3 := counting_bridge (n := 3) (by decide)
  have l2 : (L 2 : ℤ) = 384 := initial_values 0
  have l3 : (L 3 : ℤ) = 2592 := initial_values 1
  rw [l2] at h2
  rw [l3] at h3
  change (a 2 : ℤ) ≠ (a 3 : ℤ)
  omega
def family : Registration arena (type_of% @counting_bridge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@counting_bridge, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by intro i; exact ⟨(), 2, 3, actual_dependence⟩
def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@counting_bridge) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259Strip.Bridge.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259Strip.Bridge.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259Strip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Bridge

namespace Base
abbrev signature : Signature.{0, 0, 0, 0, 0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature := realize signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ n => (a n : ℤ) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () 9 = 160 * R.readout () () 8 - 6144 * R.readout () () 7 +
      86016 * R.readout () () 6 - 393216 * R.readout () () 5
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := finite_certificate
  change (a 9 : ℤ) + 1 = 160 * ((a 8 : ℤ) + 1) - 6144 * ((a 7 : ℤ) + 1) +
      86016 * ((a 6 : ℤ) + 1) - 393216 * ((a 5 : ℤ) + 1) at h
  linarith only [ha, h]
private theorem actual_dependence : actual.readout () () 2 ≠ actual.readout () () 3 := by
  have h2 := counting_bridge (n := 2) (by decide)
  have h3 := counting_bridge (n := 3) (by decide)
  have l2 : (L 2 : ℤ) = 384 := initial_values 0
  have l3 : (L 3 : ℤ) = 2592 := initial_values 1
  rw [l2] at h2
  rw [l3] at h3
  change (a 2 : ℤ) ≠ (a 3 : ℤ)
  omega
def family : Registration arena (type_of% @finite_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by intro i; exact ⟨(), 2, 3, actual_dependence⟩
def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259Strip.Base.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259Strip.Base.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259Strip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Base

namespace Recurrence
abbrev signature : Signature.{0, 0, 0, 0, 0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature := realize signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ n => (a n : ℤ) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () (n+9) =
      160 * R.readout () () (n+8) - 6144 * R.readout () () (n+7) +
        86016 * R.readout () () (n+6) - 393216 * R.readout () () (n+5)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := result 0
  have hb := h 0
  change (a 9 : ℤ) + 1 = 160 * ((a 8 : ℤ) + 1) - 6144 * ((a 7 : ℤ) + 1) +
      86016 * ((a 6 : ℤ) + 1) - 393216 * ((a 5 : ℤ) + 1) at hb
  linarith only [ha, hb]
private theorem actual_dependence : actual.readout () () 2 ≠ actual.readout () () 3 := by
  have h2 := counting_bridge (n := 2) (by decide)
  have h3 := counting_bridge (n := 3) (by decide)
  have l2 : (L 2 : ℤ) = 384 := initial_values 0
  have l3 : (L 3 : ℤ) = 2592 := initial_values 1
  rw [l2] at h2
  rw [l3] at h3
  change (a 2 : ℤ) ≠ (a 3 : ℤ)
  omega
def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by intro i; exact ⟨(), 2, 3, actual_dependence⟩
def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259Strip.Recurrence.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259Strip.Recurrence.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259Strip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false
    }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Recurrence
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259Strip
