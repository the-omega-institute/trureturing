import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233157Row
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact readout laws preserve the complete telescopes of the strip identities. -/
namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233157Row
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233157Row
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
set_option maxRecDepth 100000
namespace Certificate
abbrev signature : Signature.{0, 0, 0, 0, 0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 3) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ j => (![6, -15, 9] : Fin 3 → ℤ) j) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℤ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := (Q^(4+3)).mulVec (1 : Fin 14 → ℤ) =
      ∑ j : Fin 3, R.readout () () j • (Q^(4+j.val)).mulVec (1 : Fin 14 → ℤ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun h (0 : Fin 14)
  simp only [rejected, realize, zero_smul, Finset.sum_const_zero, Pi.zero_apply] at hb
  rw [show 4+3 = (7 : Fin 9).val from rfl, powers_table] at hb
  change (1893060 : ℤ) = 0 at hb
  norm_num at hb
def family : Registration arena (type_of% @finite_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (6 : ℤ) ≠ -15
    norm_num
def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233157Row.Certificate.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233157Row.Certificate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ j => (![6, -15, 9] : Fin 3 → ℤ) j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233157Row
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Certificate

namespace Recurrence
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (U4 n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (U4 n : ℤ) + if n = 8 then 1 else 0)
    (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () (n+8) = 9 * R.readout () () (n+7) - 15 * R.readout () () (n+6) + 6 * R.readout () () (n+5)
private theorem rejected_law : ¬ arena.Law rejected := by
  have obstruction (u : ℕ → ℤ)
      (hu : ∀ n, u (n+8) = 9 * u (n+7) - 15 * u (n+6) + 6 * u (n+5))
      (hb : ∀ n, (u (n+8) + if n+8 = 8 then 1 else 0) = 9 * (u (n+7) + if n+7 = 8 then 1 else 0) - 15 * (u (n+6) + if n+6 = 8 then 1 else 0) + 6 * (u (n+5) + if n+5 = 8 then 1 else 0)) : False := by
    have h0 := hu 0
    have h1 := hb 0
    norm_num at h0 h1
    linarith only [h0, h1]
  exact obstruction (fun n => (U4 n : ℤ)) result
def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    have h0 : U4 0 = 1 := by decide +kernel
    have h1 : U4 1 = 81 := by decide +kernel
    change (U4 0 : ℤ) ≠ (U4 1 : ℤ)
    rw [h0, h1]
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233157Row.Recurrence.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233157Row.Recurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (U4 n : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233157Row
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
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233157Row
