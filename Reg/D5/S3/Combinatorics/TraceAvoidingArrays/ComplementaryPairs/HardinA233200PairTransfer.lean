import D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200PairTransfer
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Complete-law readouts for the literal and continuation pair correspondences. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200PairTransfer

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200PairTransfer
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200LiteralBridge (rowWeight rowFinish)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip (Seen)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip (widthV)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
local instance decidableProp (P : Prop) : Decidable P := Classical.propDecidable P
namespace Continuation

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Seen × Boundary) (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ p n => pairV n p.1 p.2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p n => pairV n p.1 p.2 + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (s : Seen) (p : Boundary),
    widthV rowLegal pairs compatible n s p = R.readout () (s, p) n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 0 (false, false, false) (fun _ => 0)
  norm_num [rejected, realize, pairV, widthV] at h0

set_option maxRecDepth 20000 in
def family : Registration arena (type_of% @continuation_pair_bridge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨continuation_pair_bridge, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨((true, true, true), fun _ => 0), 0, 1, ?_⟩
    change (1 : ℤ) ≠ pairV 1 (true, true, true) (fun _ => 0)
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@continuation_pair_bridge) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200PairTransfer.Continuation.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200PairTransfer.Continuation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p n => pairV n p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200PairTransfer
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Continuation

namespace Literal
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => Fin 5 → Fin 4) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ q => rowWeight (false, false, false) q) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ q => rowWeight (false, false, false) q + 1) (fun e => nomatch e)
abbrev arena : Arena := by
  classical
  exact {
    signature := signature
    Law := fun R => ∀ n : ℕ, (a ⟨n + 1, Nat.succ_pos n⟩ : ℤ) =
      ∑ q : Fin 5 → Fin 4, if rowProper (Fin.cons 0 q) then
        R.readout () n q *
          pairV n (rowFinish (false, false, false) q) (Fin.cons 0 q) else 0 }

set_option maxRecDepth 10000 in
private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  have hb := h 0
  have ha := literal_pair_bridge 0
  have hsum : (∑ q : Fin 5 → Fin 4, if rowProper (Fin.cons 0 q) then
      rowWeight (false, false, false) q + 1 else 0) =
      (∑ q : Fin 5 → Fin 4, if rowProper (Fin.cons 0 q) then rowWeight (false, false, false) q else 0) + 243 := by
    have hx : ∀ q : Fin 5 → Fin 4, (if rowProper (Fin.cons 0 q) then
        rowWeight (false, false, false) q + 1 else 0) =
        (if rowProper (Fin.cons 0 q) then rowWeight (false, false, false) q else 0) +
          (if rowProper (Fin.cons 0 q) then 1 else 0) := by
      intro q
      split_ifs <;> simp
    simp_rw [hx]
    rw [Finset.sum_add_distrib]
    congr 1
  change (a ⟨1, by omega⟩ : ℤ) = _ at hb ha
  simp only [rejected, realize, pairV, mul_one] at hb
  simp only [pairV, mul_one] at ha
  rw [hsum] at hb
  linarith

def family : Registration arena (type_of% @literal_pair_bridge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨literal_pair_bridge, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, ![1, 0, 1, 0, 1], ![1, 2, 1, 2, 1], ?_⟩
    change rowWeight (false, false, false) ![1, 0, 1, 0, 1] ≠
      rowWeight (false, false, false) ![1, 2, 1, 2, 1]
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@literal_pair_bridge) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200PairTransfer.Literal.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200PairTransfer.Literal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q => rowWeight (false, false, false) q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200PairTransfer
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Literal

namespace NativeLinear
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => Fin 58) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ i => nativeInitial i) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ i => nativeInitial i + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, (a ⟨n+1, Nat.succ_pos n⟩ : ℤ) =
    dotProduct (fun i => R.readout () n i) ((nativeT^n).mulVec (1 : Fin 58 → ℤ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  have ha := native_linear_bridge 0
  simp only [rejected, realize, pow_zero, Matrix.one_mulVec, dotProduct, Pi.one_apply,
    mul_one, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hb
  simp only [pow_zero, Matrix.one_mulVec, dotProduct, Pi.one_apply, mul_one] at ha
  norm_num only at hb
  linarith

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- Two exact nativeInitial fibres witness dependence of the full-law readout.
def family : Registration arena (type_of% @native_linear_bridge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_linear_bridge, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change nativeInitial 0 ≠ nativeInitial 1
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@native_linear_bridge) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200PairTransfer.NativeLinear.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200PairTransfer.NativeLinear.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ i => nativeInitial i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200PairTransfer
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end NativeLinear
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233200PairTransfer
