import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The original canonical correspondence as a complete dependent-family law. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
  (labelAdvance labelWeight rowFinish rowWeight)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer (Boundary pairV)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => Boundary) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ n p => pairV n (true, true) p) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ n p => pairV n (true, true) p + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (p : Boundary) (hp : proper p),
    pairV n (true, true) (canonical p hp).val = R.readout () n p
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : proper ![0, 1, 0, 1, 0, 1] := by decide +kernel
  have h0 := h 0 ![0, 1, 0, 1, 0, 1] hp
  norm_num [rejected, realize, pairV] at h0
def family : Registration arena (type_of% @completed_canonical_bridge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨completed_canonical_bridge, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, (fun _ => 0), ![0, 1, 0, 1, 0, 1], ?_⟩
    change pairV 1 (true, true) (fun _ => 0) ≠ pairV 1 (true, true) ![0, 1, 0, 1, 0, 1]
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@completed_canonical_bridge) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n p => pairV n (true, true) p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
namespace Transfer
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => Boundary) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ n p => pairV n (true, true) p) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ n p => pairV n (true, true) p + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (p : Boundary) (_hp : proper p),
    R.readout () n p = F n (classOf p)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : proper ![0, 1, 0, 1, 0, 1] := by decide +kernel
  have h0 := h 0 ![0, 1, 0, 1, 0, 1] hp
  norm_num [rejected, realize, pairV, F, Matrix.one_mulVec] at h0
def family : Registration arena (type_of% @completed_transfer_bridge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨completed_transfer_bridge, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, ![0, 1, 0, 1, 0, 1], ![0, 1, 0, 1, 0, 2], ?_⟩
    change pairV 1 (true, true) ![0, 1, 0, 1, 0, 1] ≠
      pairV 1 (true, true) ![0, 1, 0, 1, 0, 2]
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@completed_transfer_bridge) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry.Transfer.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry.Transfer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n p => pairV n (true, true) p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Transfer

namespace Literal
open scoped BigOperators
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer (a)
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => Fin 16) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ n i => F n i) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ n i => F n i + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, (a ⟨n + 1, Nat.succ_pos n⟩ : ℤ) =
    (16 : ℤ) * 128^n + 32 * ∑ i : Fin 16, R.readout () n i
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := literal_canonical_bridge 0
  have hb := h 0
  change (a ⟨1, Nat.succ_pos 0⟩ : ℤ) =
    (16 : ℤ) * 128^0 + 32 * ∑ i : Fin 16, (F 0 i + 1) at hb
  rw [Finset.sum_add_distrib] at hb
  norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hb
  linarith
def family : Registration arena (type_of% @literal_canonical_bridge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨literal_canonical_bridge, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    change F 1 0 ≠ F 1 1
    have h0 := completed_transfer_bridge 1 ![0, 1, 0, 1, 0, 1] (by decide +kernel)
    have h1 := completed_transfer_bridge 1 ![0, 1, 0, 1, 0, 2] (by decide +kernel)
    have hc0 : classOf ![0, 1, 0, 1, 0, 1] = 0 := by decide +kernel
    have hc1 : classOf ![0, 1, 0, 1, 0, 2] = 1 := by decide +kernel
    rw [hc0] at h0
    rw [hc1] at h1
    rw [← h0, ← h1]
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@literal_canonical_bridge) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry.Literal.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry.Literal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n i => F n i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "arg", "arg", "arg", "body"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Literal

namespace FullRow
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ k => (2 : ℤ)^k) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ k => (2 : ℤ)^k + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (q : Fin k → Fin 3),
    rowFinish (true, true) q = (true, true) ∧
      rowWeight (true, true) q = R.readout () () k
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 0 (fun j => Fin.elim0 j)
  norm_num [rejected, realize, rowFinish, rowWeight] at h0
def family : Registration arena (type_of% @full_row) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨full_row, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@full_row) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry.FullRow.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry.FullRow.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => (2 : ℤ)^k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end FullRow

namespace FullCell
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 3) (fun _ => Bool × Bool) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ q s => labelWeight s q) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ q s => labelWeight s q + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ q : Fin 3,
    labelAdvance (true, true) q = (true, true) ∧
      R.readout () q (true, true) = 2
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := (h 0).2
  norm_num [rejected, realize, labelWeight] at h0
def family : Registration arena (type_of% @full_cell) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨full_cell, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, (true, true), (false, false), ?_⟩
    norm_num [actual, realize, labelWeight]
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@full_cell) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry.FullCell.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry.FullCell.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q s => labelWeight s q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end FullCell

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
