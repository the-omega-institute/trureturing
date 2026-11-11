import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127Certificate
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127CertificateZero
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import Lean.Elab.Tactic.Omega

/-! Four-slot registration of the exact valid-boundary transition counts. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127CertificateZero

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip (Seen)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer (Boundary)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
  (rowWeight rowFinish)

open scoped BigOperators

noncomputable section

attribute [local irreducible] classCount

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Seen × Boundary)
    (fun _ => Fin 11) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ sp k => classCount sp.1 sp.2 k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ sp k => classCount sp.1 sp.2 k + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ s p, Valid s p → p 0 = 0 → ∀ k,
    R.readout () (s, p) k = transfer (boundaryClass s p) k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : Valid (true, true) ![0, 1, 0, 1, 0, 1] := by
    unfold Valid
    decide +kernel
  have hb := h (true, true) ![0, 1, 0, 1, 0, 1] hp rfl 0
  have ha := row_counts (true, true) ![0, 1, 0, 1, 0, 1] hp 0
  change classCount (true, true) ![0, 1, 0, 1, 0, 1] 0 + 1 =
    transfer (boundaryClass (true, true) ![0, 1, 0, 1, 0, 1]) 0 at hb
  omega

def family : Registration arena (type_of% @row_counts_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨row_counts_zero, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨((true, true), ![0, 1, 0, 1, 0, 1]), 0, 1, ?_⟩
    change classCount (true, true) ![0, 1, 0, 1, 0, 1] 0 ≠
      classCount (true, true) ![0, 1, 0, 1, 0, 1] 1
    have hp : Valid (true, true) ![0, 1, 0, 1, 0, 1] := by
      unfold Valid
      decide +kernel
    rw [row_counts _ _ hp 0, row_counts _ _ hp 1]
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@row_counts_zero) (Realization signature) Type Unit where
  unitName := `Reg.A233127RowsZero.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ sp k => classCount sp.1 sp.2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127CertificateZero
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

namespace Fibres

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Seen × Boundary)
    (fun _ => Fin 11) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ sp k => classCount sp.1 sp.2 k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ sp k => classCount sp.1 sp.2 k + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ s p k,
    R.readout () (s, p) k =
      ∑ q0 : Fin 3, ∑ q1 : Fin 3, ∑ q2 : Fin 3, ∑ q3 : Fin 3,
      ∑ q4 : Fin 3, ∑ q5 : Fin 3,
      rowWeight s ![q0, q1, q2, q3, q4, q5] *
      if (∀ j : Fin 5, (![q0, q1, q2, q3, q4, q5] : Boundary) j.castSucc ≠
        (![q0, q1, q2, q3, q4, q5] : Boundary) j.succ) ∧
        (∀ j : Fin 6, p j ≠ (![q0, q1, q2, q3, q4, q5] : Boundary) j) ∧
        boundaryClass (rowFinish s ![q0, q1, q2, q3, q4, q5])
          ![q0, q1, q2, q3, q4, q5] = k then 1 else 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (true, true) ![0, 1, 0, 1, 0, 1] 0
  have ha := class_fibres_normalized (true, true) ![0, 1, 0, 1, 0, 1] 0
  change classCount (true, true) ![0, 1, 0, 1, 0, 1] 0 + 1 = _ at hb
  omega

def family : Registration arena (type_of% @class_fibres_normalized) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨class_fibres_normalized, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨((true, true), ![0, 1, 0, 1, 0, 1]), 0, 1, ?_⟩
    change classCount (true, true) ![0, 1, 0, 1, 0, 1] 0 ≠
      classCount (true, true) ![0, 1, 0, 1, 0, 1] 1
    have hp : Valid (true, true) ![0, 1, 0, 1, 0, 1] := by
      unfold Valid
      decide +kernel
    rw [row_counts _ _ hp 0, row_counts _ _ hp 1]
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@class_fibres_normalized) (Realization signature) Type Unit where
  unitName := `Reg.A233127NormalizedFibres.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ sp k => classCount sp.1 sp.2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127CertificateZero
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Fibres

end

end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127CertificateZero
