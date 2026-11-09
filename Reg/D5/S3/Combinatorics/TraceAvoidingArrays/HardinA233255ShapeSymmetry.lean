import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The original canonical correspondence as a complete dependent-family law. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
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
    readouts := #[{ path := #["body", "body", "body", "arg"], stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
