import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Jacobi.EndpointMomentTruncation
import Reg.Support.SingleDependentReadout

/-! The order of the full endpoint moment matters at the first Jacobi cutoff discrepancy. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Jacobi.EndpointMomentTruncation
open LeanInformationAudit Finset
namespace Reg.D5.S3.Quantum.Jacobi.EndpointMomentTruncation
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature := realize signature (fun _ _ x => 2 * x) (fun e => nomatch e)
def discarded : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (a b : ℕ → ℝ) (n : ℕ),
    (∀ k < 2 * n, amplitude a b none k 0 = amplitude a b (some n) k 0) ∧
    amplitude a b none (R.readout () () n) 0 - amplitude a b (some n) (2 * n) 0 =
      ∏ j ∈ range n, (b j) ^ 2

private theorem discarded_fails : ¬arena.Law discarded := by
  intro law
  have h := (law (fun _ => 0) (fun _ => 0) 1).2
  change amplitude (fun _ => 0) (fun _ => 0) none 0 0 -
      amplitude (fun _ => 0) (fun _ => 0) (some 1) 2 0 = ∏ _ ∈ range 1, (0 : ℝ) ^ 2 at h
  norm_num [amplitude] at h

def family : Registration arena (type_of% @first_omitted_moment) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨first_omitted_moment, discarded, discarded_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual discarded discarded_fails
  dependence := by
    intro i
    exact ⟨(), (0 : ℕ), (1 : ℕ), by change 0 ≠ (2 : ℕ); decide⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Jacobi.EndpointMomentTruncation.first_omitted_moment)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Jacobi.EndpointMomentTruncation.unit
  realizationName := `Reg.D5.S3.Quantum.Jacobi.EndpointMomentTruncation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 2 * x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Jacobi.EndpointMomentTruncation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Jacobi.EndpointMomentTruncation
