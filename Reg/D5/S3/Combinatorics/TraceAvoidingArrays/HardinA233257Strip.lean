import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233257Strip
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact sequence readouts, with explicit rejected families and observational dependence. -/
namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233257Strip
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233257Strip
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries
noncomputable section
attribute [local irreducible] a

private theorem sequence_varies : a 2 ≠ a 3 := by
  have h2 := closed_form 0
  have h3 := closed_form 1
  norm_num at h2 h3
  omega

namespace Initial
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () 0 = 0 ∧ R.readout () () 1 = 3
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.1
  change a 0 + 1 = 0 at hb
  omega
def family : Registration arena (type_of% @finite_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    rw [finite_certificate.1, finite_certificate.2]
    decide
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233257Strip.Initial.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233257Strip.Initial.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233257Strip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Initial

namespace Closed
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 9 * R.readout () () (n+2) = 2 ^ (2*n+1) * (4 * 3 ^ (n+2) + 9)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change 9 * (a (0+2) + 1) = _ at hb
  have ha := closed_form 0
  omega
def family : Registration arena (type_of% @closed_form) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@closed_form, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 2, 3, sequence_varies⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@closed_form) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233257Strip.Closed.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233257Strip.Closed.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233257Strip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Closed

namespace Recurrence
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (a n : ℤ) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () (n+4) =
    16 * R.readout () () (n+3) - 48 * R.readout () () (n+2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change (a (0+4) : ℤ) + 1 =
    16 * ((a (0+3) : ℤ) + 1) - 48 * ((a (0+2) : ℤ) + 1) at hb
  have ha := recurrence 0
  linarith only [ha, hb]
def family : Registration arena (type_of% @recurrence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@recurrence, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 2, 3, ?_⟩
    change (a 2 : ℤ) ≠ (a 3 : ℤ)
    exact_mod_cast sequence_varies
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@recurrence) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233257Strip.Recurrence.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233257Strip.Recurrence.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233257Strip
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

namespace Result
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ((1-4*X)*(1-12*X)*(PowerSeries.mk fun n => (R.readout () () n : ℤ)) =
      X*(3-38*X+88*X^2)) ∧
    (∀ n : ℕ, 9 * R.readout () () (n+2) = 2 ^ (2*n+1) * (4 * 3 ^ (n+2) + 9)) ∧
    (∀ n : ℕ, (R.readout () () (n+4) : ℤ) =
      16 * (R.readout () () (n+3) : ℤ) - 48 * (R.readout () () (n+2) : ℤ))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.2.1 0
  change 9 * (a (0+2) + 1) = _ at hb
  have ha := closed_form 0
  omega
def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 2, 3, sequence_varies⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233257Strip.Result.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233257Strip.Result.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233257Strip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg", "arg", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Result

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233257Strip
