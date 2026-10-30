import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoLinearSpan
import Reg.Support.DependentFamily

/-! Source-bound audit of the exact binary bond-two uniform MPS span dimension. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoLinearSpan
open _root_.D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoLinearSpan
open _root_.D5.S3.Quantum.TensorNetworks.UniformMPSExpectedDimensionRefutation (uMPS)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the equality relation on the two rational dimension operands. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- Preserve the positive-length domain and both branches of the parity formula. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 1 ≤ n →
    R.readout () () (Module.finrank ℂ (Submodule.span ℂ (uMPS 2 2 n)) : ℚ)
      (if Even n then ((n : ℚ) ^ 4 - 4 * n ^ 2 + 192 * n + 192) / 192
       else ((n : ℚ) ^ 4 - 10 * n ^ 2 + 192 * n + 201) / 192)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by decide)

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), (0 : ℚ), 1, ?_⟩
    intro he
    have hbad : (1 : ℚ) = 0 := Eq.mp (congrFun he 0) rfl
    norm_num at hbad

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoLinearSpan.result)
      (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoLinearSpan.result.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoLinearSpan.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoLinearSpan
    definition := some {
      owner := `D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoLinearSpan
      name := `D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoLinearSpan.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoLinearSpan
