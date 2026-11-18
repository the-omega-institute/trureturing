import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact readout laws preserve the complete telescopes of the strip identities. -/
namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155RowTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
set_option maxRecDepth 100000

namespace Quotient
abbrev Coordinates := Σ k : ℕ, Σ q : ℕ, Σ _ : Row k → Fin q, Row k
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Coordinates
    (fun p => Fin p.2.1) (fun _ => ℤ)
-- The readout counts successors in one observed class.
def actual : Realization signature :=
  realize signature (fun _ p s =>
    ∑ c : Row p.1, if columnCompatible p.2.2.2 c ∧ p.2.2.1 c = s then (1 : ℤ) else 0)
      (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p r => actual.readout () p r + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k q : ℕ) (cls : Row k → Fin q) (rep : Fin q → Row k)
    (Q : Matrix (Fin q) (Fin q) ℤ),
    (∀ (e : Equiv.Perm (Fin 3)) r, cls (relabel e r) = cls r) →
    (∀ r, ∃ e : Equiv.Perm (Fin 3), relabel e r = rep (cls r)) →
    (∀ i s, ((successorClasses cls (rep i)).map
      (fun j => if j = s then (1 : ℤ) else 0)).sum = Q i s) →
    ∀ (r : Row k) (s : Fin q), R.readout () ⟨k, q, cls, r⟩ s = Q (cls r) s
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hcls : ∀ (e : Equiv.Perm (Fin 3)) (r : Row 0),
      (0 : Fin 1) = (0 : Fin 1) := by intros; rfl
  have hrep : ∀ r : Row 0, ∃ e : Equiv.Perm (Fin 3),
      relabel e r = (fun _ => (0 : Fin 3)) := by
    intro r
    refine ⟨Equiv.refl _, ?_⟩
    funext i
    exact i.elim0
  have ht : ∀ i s : Fin 1,
      ((successorClasses (fun _ : Row 0 => (0 : Fin 1)) (fun _ => (0 : Fin 3))).map
        (fun j => if j = s then (1 : ℤ) else 0)).sum = 1 := by decide +kernel
  have hb := h 0 1 (fun _ => 0) (fun _ _ => 0) (fun _ _ => 1) hcls hrep ht
    (fun _ => 0) 0
  have ha := quotient_rows 0 1 (fun _ => 0) (fun _ _ => 0) (fun _ _ => 1)
    hcls hrep ht (fun _ => 0) 0
  change actual.readout () ⟨0, 1, (fun _ => 0), (fun _ => 0)⟩ 0 + 1 = _ at hb
  change actual.readout () ⟨0, 1, (fun _ => 0), (fun _ => 0)⟩ 0 = _ at ha
  have hc := hb.trans ha.symm
  exact (by omega : ∀ z : ℤ, z + 1 ≠ z) _ hc
def family : Registration arena (type_of% @quotient_rows) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quotient_rows, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨⟨1, 2, (fun r => if r 0 = 2 then 0 else 1), (fun _ => 0)⟩, 0, 1, ?_⟩
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@quotient_rows) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer.Quotient.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer.Quotient.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p s =>
      ∑ c : Row p.1, if columnCompatible p.2.2.2 c ∧ p.2.2.1 c = s then (1 : ℤ) else 0)
        (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
    definition := none
    coordinates := #[0, 1, 2, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Quotient

namespace Transfer
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ k n => (T (n+2) k : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ k n => (T (n+2) k : ℤ) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k q : ℕ) (cls : Row k → Fin q)
    (Q : Matrix (Fin q) (Fin q) ℤ) (w : Fin q → ℤ),
    (∀ r, ∀ s,
      (∑ c : Row k, if columnCompatible r c ∧ cls c = s then (1 : ℤ) else 0) =
        Q (cls r) s) →
    (∀ s, (∑ r : Row k, if cls r = s then (1 : ℤ) else 0) = w s) →
    ∀ n, R.readout () k n = dotProduct w ((Q^(n+1)).mulVec (1 : Fin q → ℤ))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hQ : ∀ r : Row 0, ∀ s : Fin 1,
      (∑ c : Row 0, if columnCompatible r c ∧ (0 : Fin 1) = s
        then (1 : ℤ) else 0) = 1 := by decide +kernel
  have hw : ∀ s : Fin 1,
      (∑ r : Row 0, if (0 : Fin 1) = s then (1 : ℤ) else 0) = 1 := by
    decide +kernel
  have hb := h 0 1 (fun _ => 0) (fun _ _ => 1) (fun _ => 1) hQ hw 0
  have ha := count_transfer 0 1 (fun _ => 0) (fun _ _ => 1) (fun _ => 1) hQ hw 0
  change (T 2 0 : ℤ) + 1 = _ at hb
  have hc : (T 2 0 : ℤ) + 1 = (T 2 0 : ℤ) := hb.trans ha.symm
  exact (by omega : ∀ z : ℤ, z + 1 ≠ z) _ hc
def family : Registration arena (type_of% @_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer.count_transfer) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer.count_transfer, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    change (T 2 1 : ℤ) ≠ (T 3 1 : ℤ)
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer.count_transfer) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer.Transfer.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer.Transfer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k n => (T (n+2) k : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
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
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233155ColumnTransfer
