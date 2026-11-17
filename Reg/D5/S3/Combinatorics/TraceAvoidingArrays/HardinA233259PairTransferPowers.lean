import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound four-slot registrations with literal unknown residuals. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

namespace TableZero
abbrev signature : Signature.{0, 0, 0, 0, 0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 9) (fun _ => Fin 14 → ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ k => W k) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : Fin 14 → ℤ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () 0 = (1 : Fin 14 → ℤ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun h (0 : Fin 14)
  change (0 : ℤ) = 1 at hb
  norm_num at hb
def family : Registration arena (type_of% @table_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@table_zero, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro he
    have hh := congrFun he (0 : Fin 14)
    change (1 : ℤ) = 16 at hh
    norm_num at hh
def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@table_zero) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers.TableZero.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers.TableZero.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end TableZero

namespace TableSteps
abbrev signature : Signature.{0, 0, 0, 0, 0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 9) (fun _ => Fin 14 → ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ k => W k) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ k => W k + if k = 1 then (1 : Fin 14 → ℤ) else 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : Fin 8, R.readout () () k.succ =
      Q.mulVec (R.readout () () k.castSucc)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := congrFun (table_steps 0) (0 : Fin 14)
  have hb := congrFun (h 0) (0 : Fin 14)
  change W 1 0 = (Q.mulVec (W 0)) 0 at ha
  change W 1 0 + 1 = (Q.mulVec (W 0)) 0 at hb
  linarith only [ha, hb]
def family : Registration arena (type_of% @table_steps) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@table_steps, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro he
    have hh := congrFun he (0 : Fin 14)
    change (1 : ℤ) = 16 at hh
    norm_num at hh
def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@table_steps) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers.TableSteps.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers.TableSteps.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers
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
end TableSteps

namespace PowersTable
abbrev signature : Signature.{0, 0, 0, 0, 0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 9) (fun _ => Fin 14 → ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ k => W k) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ k => W k + (1 : Fin 14 → ℤ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : Fin 9, (Q^k.val).mulVec (1 : Fin 14 → ℤ) = R.readout () () k
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := congrFun (powers_table 0) (0 : Fin 14)
  have hb := congrFun (h 0) (0 : Fin 14)
  change ((Q^0).mulVec (1 : Fin 14 → ℤ)) 0 = W 0 0 at ha
  change ((Q^0).mulVec (1 : Fin 14 → ℤ)) 0 = W 0 0 + 1 at hb
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
    have hh := congrFun he (0 : Fin 14)
    change (1 : ℤ) = 16 at hh
    norm_num at hh
def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@powers_table) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers.PowersTable.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers.PowersTable.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers
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

namespace PowerPolynomial
abbrev signature : Signature.{0, 0, 0, 0, 0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 4) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ j => coefficients j) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℤ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := (Q^(4+4)).mulVec (1 : Fin 14 → ℤ) =
      ∑ j : Fin 4, R.readout () () j • (Q^(4+j.val)).mulVec (1 : Fin 14 → ℤ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun h (0 : Fin 14)
  simp only [rejected, realize, zero_smul, Finset.sum_const_zero, Pi.zero_apply] at hb
  rw [show 4+4 = (8 : Fin 9).val from rfl, powers_table] at hb
  change (13198824 : ℤ) = 0 at hb
  norm_num at hb
def family : Registration arena (type_of% @power_polynomial) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@power_polynomial, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (-6 : ℤ) ≠ 21
    norm_num
def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@power_polynomial) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers.PowerPolynomial.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers.PowerPolynomial.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ j => coefficients j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers
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
end PowerPolynomial

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers
