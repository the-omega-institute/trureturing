import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact sequence readouts for the literal ladder count and its pair-label transfer. -/
namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer (L initial_values)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
attribute [local irreducible] L

namespace Initial
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (L n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (L n : ℤ) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : Fin 6, R.readout () () (k.val+2) =
      ![96,432,1944,8856,40392,184248] k
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := initial_values 0
  have hb := h 0
  change (L 2 : ℤ) + 1 = 96 at hb
  norm_num at ha
  linarith
private theorem actual_dependence :
    actual.readout () () 2 ≠ actual.readout () () 3 := by
  have h2 := initial_values 0
  have h3 := initial_values 1
  norm_num at h2 h3
  change (L 2 : ℤ) ≠ (L 3 : ℤ)
  omega
def family : Registration arena (type_of% @initial_values) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@initial_values, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 2, 3, actual_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@initial_values) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer.Initial.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer.Initial.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (L n : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer
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
end Initial

namespace Recurrence
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (L n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (L n : ℤ) + if n = 6 then 1 else 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () (n+6) + 6 =
      6 * (R.readout () () (n+5) + 6) - 7 * (R.readout () () (n+4) + 6) +
        2 * (R.readout () () (n+3) + 6)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := recurrence 0
  have hb := h 0
  change ((L 6 : ℤ) + 1) + 6 =
    6 * ((L 5 : ℤ) + 0 + 6) - 7 * ((L 4 : ℤ) + 0 + 6) +
      2 * ((L 3 : ℤ) + 0 + 6) at hb
  linarith
private theorem actual_dependence :
    actual.readout () () 2 ≠ actual.readout () () 3 := by
  have h2 := initial_values 0
  have h3 := initial_values 1
  norm_num at h2 h3
  change (L 2 : ℤ) ≠ (L 3 : ℤ)
  omega
def family : Registration arena (type_of% @recurrence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@recurrence, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 2, 3, actual_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@recurrence) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer.Recurrence.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer.Recurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (L n : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Recurrence
namespace Transfer
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (L n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (L n : ℤ) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () (n+2) =
    dotProduct weights ((Q^n).mulVec (1 : Fin 5 → ℤ))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := count_transfer 0
  have hb := h 0
  change (L 2 : ℤ) + 1 = _ at hb
  change (L 2 : ℤ) = _ at ha
  linarith only [ha, hb]
private theorem actual_dependence :
    actual.readout () () 2 ≠ actual.readout () () 3 := by
  have h2 := initial_values 0
  have h3 := initial_values 1
  norm_num at h2 h3
  change (L 2 : ℤ) ≠ (L 3 : ℤ)
  omega
def family : Registration arena (type_of% @count_transfer) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@count_transfer, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 2, 3, actual_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@count_transfer) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer.Transfer.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer.Transfer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (L n : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer
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
end Transfer

namespace PowersTable
abbrev signature : Signature.{0, 0, 0, 0, 0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 6) (fun _ => Fin 5 → ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ k => W k) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ k => W k + (1 : Fin 5 → ℤ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : Fin 6, (Q^k.val).mulVec (1 : Fin 5 → ℤ) = R.readout () () k
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := congrFun (powers_table 0) (0 : Fin 5)
  have hb := congrFun (h 0) (0 : Fin 5)
  change ((Q^0).mulVec (1 : Fin 5 → ℤ)) 0 = W 0 0 at ha
  change ((Q^0).mulVec (1 : Fin 5 → ℤ)) 0 = W 0 0 + 1 at hb
  linarith only [ha, hb]
def family : Registration arena (type_of% @powers_table) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@powers_table, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro he
    have hh := congrFun he (0 : Fin 5)
    change (1 : ℤ) = 8 at hh
    norm_num at hh
def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@powers_table) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer.PowersTable.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer.PowersTable.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => W k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end PowersTable
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258PairTransfer
