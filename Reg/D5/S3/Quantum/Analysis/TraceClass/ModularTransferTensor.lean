import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Analysis.TraceClass.ModularTransferTensor

open scoped InnerProductSpace TensorProduct
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)

noncomputable section

namespace Reg.D5.S3.Quantum.Analysis.TraceClass.ModularTransferTensor

universe u

private abbrev observation := signature Unit (fun _ => ℂ) (fun _ => ℝ)
private def actual : Realization observation :=
  realize observation (fun _ _ z => z.re) (fun e => nomatch e)
private def rejected : Realization observation :=
  realize observation (fun _ _ _ => -1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := observation
  Law R := ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hT : HilbertSchmidt.IsHilbertSchmidt T) (reflect : H → H)
    (_hiso : ∀ x, ‖reflect x‖ = ‖x‖)
    (_hsymm : ∀ x y, inner ℂ (reflect x) y = inner ℂ (reflect y) x),
    ∃ vector : UniformSpace.Completion (H ⊗[ℂ] H),
      ‖vector‖ ^ 2 =
        R.readout () ()
          (trace (star T * T) (HilbertSchmidt.isTraceClass_star_mul_self_of_isHilbertSchmidt hT)) ∧
      ∀ x y : H, inner ℂ vector
        ((x ⊗ₜ[ℂ] y : H ⊗[ℂ] H) : UniformSpace.Completion (H ⊗[ℂ] H)) =
          inner ℂ (reflect x) (T y)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let H := EuclideanSpace ℂ (ULift.{u} Empty)
  have hs (x y : H) : inner ℂ x y = inner ℂ y x := by
    rw [Subsingleton.elim x y]
  obtain ⟨v, hv, _⟩ := h (H := H) 0 HilbertSchmidt.isHilbertSchmidt_zero id (fun _ => rfl) hs
  change ‖v‖ ^ 2 = -1 at hv
  linarith [sq_nonneg ‖v‖]

def family : Registration arena.{u}
    (type_of% (@_root_.ModularTransferTensor.transfer_tensor.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.ModularTransferTensor.transfer_tensor.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity arena.{u}.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.ModularTransferTensor.transfer_tensor.{u}) (Realization observation) Unit Unit where
  unitName := `ModularTransferTensor.transfer_tensor.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.ModularTransferTensor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize observation (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.TraceClass.ModularTransferTensor
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Analysis.TraceClass.ModularTransferTensor
