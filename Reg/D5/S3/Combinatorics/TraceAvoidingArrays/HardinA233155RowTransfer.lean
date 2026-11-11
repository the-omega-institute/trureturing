import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact readout laws preserve the complete telescopes of the strip identities. -/
namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
set_option maxRecDepth 100000

namespace RowSum
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun k => Row k → ℤ) (fun _ => ℤ)
def actual : Realization signature := by
  classical
  exact realize signature (fun _ k F => ∑ r : Row k, if rowLegal r then F r else 0)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ k F => actual.readout () k F + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (F : Row k → ℤ), R.readout () k F =
    ((legalCodes k).map (fun c => F (decode k c))).sum
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 (fun _ => 0)
  simp [rejected, actual, realize, legalCodes] at hb
def family : Registration arena (type_of% @row_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@row_sum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
    simp [actual, realize, Row, rowLegal]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@row_sum) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer.RowSum.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer.RowSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (by
    classical
    exact realize signature (fun _ k F => ∑ r : Row k, if rowLegal r then F r else 0)
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end RowSum

namespace Sequence
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ k n => T k (n+1)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ k n => T k (n+1) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ k n, R.readout () k n = Nat.card {r : Fin (n+1) → Row k //
    (∀ i, rowLegal (r i)) ∧
    (∀ (i : Fin (n+1)) (h : i.val + 1 < n+1),
      compatible (r i) (r ⟨i.val + 1, h⟩))}
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 0
  have ha := row_sequence_bridge 0 0
  change T 0 1 + 1 = _ at hb
  have hc : T 0 1 + 1 = T 0 1 := hb.trans ha.symm
  exact Nat.succ_ne_self _ hc
def family : Registration arena (type_of% @row_sequence_bridge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@row_sequence_bridge, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    change T 1 1 ≠ T 1 2
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@row_sequence_bridge) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer.Sequence.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer.Sequence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k n => T k (n+1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Sequence

namespace Transfer
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ k n => (T k (n+2) : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ k n => (T k (n+2) : ℤ) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k q : ℕ) (cls : Row k → Fin q)
    (Q : Matrix (Fin q) (Fin q) ℤ) (w : Fin q → ℤ),
    (∀ r, rowLegal r → ∀ s,
      (∑ c : Row k, if rowLegal c ∧ compatible r c ∧ cls c = s then (1 : ℤ) else 0) =
        Q (cls r) s) →
    (∀ s, (∑ r : Row k, if rowLegal r ∧ cls r = s then (1 : ℤ) else 0) = w s) →
    ∀ n, R.readout () k n = dotProduct w ((Q^(n+1)).mulVec (1 : Fin q → ℤ))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hQ : ∀ r : Row 0, rowLegal r → ∀ s : Fin 1,
      (∑ c : Row 0, if rowLegal c ∧ compatible r c ∧ (0 : Fin 1) = s
        then (1 : ℤ) else 0) = 1 := by decide +kernel
  have hw : ∀ s : Fin 1,
      (∑ r : Row 0, if rowLegal r ∧ (0 : Fin 1) = s then (1 : ℤ) else 0) = 1 := by
    decide +kernel
  have hb := h 0 1 (fun _ => 0) (fun _ _ => 1) (fun _ => 1) hQ hw 0
  have ha := count_transfer 0 1 (fun _ => 0) (fun _ _ => 1) (fun _ => 1) hQ hw 0
  change (T 0 2 : ℤ) + 1 = _ at hb
  have hc : (T 0 2 : ℤ) + 1 = (T 0 2 : ℤ) := hb.trans ha.symm
  exact (by omega : ∀ z : ℤ, z + 1 ≠ z) _ hc
def family : Registration arena (type_of% @count_transfer) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@count_transfer, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    change (T 1 2 : ℤ) ≠ (T 1 3 : ℤ)
    norm_cast

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@count_transfer) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer.Transfer.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer.Transfer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k n => (T k (n+2) : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Transfer
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
