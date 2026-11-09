import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Complete-law readouts for the literal and continuation pair correspondences. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge (rowWeight rowFinish)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip (Seen)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip (widthV)
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
  have h0 := h 0 (false, false) (fun _ => 0)
  norm_num [rejected, realize, pairV, widthV] at h0

def family : Registration arena (type_of% @continuation_pair_bridge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨continuation_pair_bridge, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨((true, true), fun _ => 0), 0, 1, ?_⟩
    change (1 : ℤ) ≠ pairV 1 (true, true) (fun _ => 0)
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@continuation_pair_bridge) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer.Continuation.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer.Continuation.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
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
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => Boundary) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ q => rowWeight (false, false) q) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ q => rowWeight (false, false) q + 1) (fun e => nomatch e)
abbrev arena : Arena := by
  classical
  exact {
    signature := signature
    Law := fun R => ∀ n : ℕ, (a ⟨n + 1, Nat.succ_pos n⟩ : ℤ) =
      ∑ q : Boundary, if rowProper (Fin.cons 0 q) then
        R.readout () n q * pairV n (rowFinish (false, false) q) q else 0 }

set_option maxRecDepth 10000 in
private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  have hb := h 0
  have ha := literal_pair_bridge 0
  have hsum : (∑ q : Boundary, if rowProper (Fin.cons 0 q) then
      rowWeight (false, false) q + 1 else 0) =
      (∑ q : Boundary, if rowProper (Fin.cons 0 q) then rowWeight (false, false) q else 0) + 64 := by
    have hx : ∀ q : Boundary, (if rowProper (Fin.cons 0 q) then
        rowWeight (false, false) q + 1 else 0) =
        (if rowProper (Fin.cons 0 q) then rowWeight (false, false) q else 0) +
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
    refine ⟨0, ![1, 0, 1, 0, 1, 0], ![1, 2, 1, 2, 1, 2], ?_⟩
    change rowWeight (false, false) ![1, 0, 1, 0, 1, 0] ≠
      rowWeight (false, false) ![1, 2, 1, 2, 1, 2]
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@literal_pair_bridge) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer.Literal.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer.Literal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q => rowWeight (false, false) q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
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
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
