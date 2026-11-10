import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact sequence readouts for the literal ladder count and its pair-label transfer. -/
namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer (L initial_values)
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
  Law R := ∀ k : Fin 26, R.readout () () (k.val+2) =
  ![1458, 23346, 235824, 2986152, 33994188, 409408542, 4791504648, 56948232390, 671408641884,
    7950212281224, 93923210426688, 1110971521842576, 13132515793768920, 155290791915166218,
    1835954950424998884, 21708106678579996182, 256660237490505696204, 3034643594159596884672,
    35879810376487028900160, 424224888649277811420648, 5015800426651629427544760,
    59304188625218088516497046, 701180686835907546543927912, 8290387169164139913131170926,
    98021089474277074253102673060, 1158948987790395127011466558572] k
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := initial_values 0
  have hb := h 0
  change (L 2 : ℤ) + 1 = 1458 at hb
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
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer.Initial.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer.Initial.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer
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
  realize signature (fun _ _ n => (L n : ℤ) + if n = 27 then 1 else 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () (n+27) + 6 =
    7 * (R.readout () () (n+26) + 6) + 103 * (R.readout () () (n+25) + 6) - 365 * (R.readout () ()
      (n+24) + 6) - 2896 * (R.readout () () (n+23) + 6) + 7168 * (R.readout () () (n+22) + 6) +
      32291 * (R.readout () () (n+21) + 6) - 75471 * (R.readout () () (n+20) + 6) - 161805 *
      (R.readout () () (n+19) + 6) + 426135 * (R.readout () () (n+18) + 6) + 333692 * (R.readout ()
      () (n+17) + 6) - 1225001 * (R.readout () () (n+16) + 6) - 155206 * (R.readout () () (n+15) +
      6) + 1850161 * (R.readout () () (n+14) + 6) - 363389 * (R.readout () () (n+13) + 6) - 1524689
      * (R.readout () () (n+12) + 6) + 557502 * (R.readout () () (n+11) + 6) + 690388 * (R.readout
      () () (n+10) + 6) - 312941 * (R.readout () () (n+9) + 6) - 166928 * (R.readout () () (n+8) +
      6) + 81406 * (R.readout () () (n+7) + 6) + 19997 * (R.readout () () (n+6) + 6) - 9672 *
      (R.readout () () (n+5) + 6) - 906 * (R.readout () () (n+4) + 6) + 420 * (R.readout () () (n+3)
      + 6)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := recurrence 0
  have hb := h 0
  change ((L 27 : ℤ) + 1) + 6 =
    7 * (((L 26 : ℤ) + 0) + 6) + 103 * (((L 25 : ℤ) + 0) + 6) - 365 * (((L 24 : ℤ) + 0) + 6) - 2896
      * (((L 23 : ℤ) + 0) + 6) + 7168 * (((L 22 : ℤ) + 0) + 6) + 32291 * (((L 21 : ℤ) + 0) + 6) -
      75471 * (((L 20 : ℤ) + 0) + 6) - 161805 * (((L 19 : ℤ) + 0) + 6) + 426135 * (((L 18 : ℤ) + 0)
      + 6) + 333692 * (((L 17 : ℤ) + 0) + 6) - 1225001 * (((L 16 : ℤ) + 0) + 6) - 155206 * (((L 15 :
      ℤ) + 0) + 6) + 1850161 * (((L 14 : ℤ) + 0) + 6) - 363389 * (((L 13 : ℤ) + 0) + 6) - 1524689 *
      (((L 12 : ℤ) + 0) + 6) + 557502 * (((L 11 : ℤ) + 0) + 6) + 690388 * (((L 10 : ℤ) + 0) + 6) -
      312941 * (((L 9 : ℤ) + 0) + 6) - 166928 * (((L 8 : ℤ) + 0) + 6) + 81406 * (((L 7 : ℤ) + 0) +
      6) + 19997 * (((L 6 : ℤ) + 0) + 6) - 9672 * (((L 5 : ℤ) + 0) + 6) - 906 * (((L 4 : ℤ) + 0) +
      6) + 420 * (((L 3 : ℤ) + 0) + 6) at hb
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
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer.Recurrence.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer.Recurrence.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer
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
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer
