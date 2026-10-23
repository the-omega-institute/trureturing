import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumBounds.NonlocalityDepthQuantumBound
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.QuantumBounds.NonlocalityDepthQuantumBound
open _root_.D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Tensor
open _root_.D5.S3.Quantum.Recovery
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- Observe the family of local matrices entering the tensor product. -/
abbrev signature : Signature where
  Params := Σ n : ℕ, Fin n → Type u
  State p := ∀ j, Matrix (p.2 j) (p.2 j) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ∀ j, Matrix (p.2 j) (p.2 j) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ M => M) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : ℕ} {σ : Fin n → Type u}
    [∀ j, Fintype (σ j)] [∀ j, DecidableEq (σ j)]
    (M : ∀ j, Matrix (σ j) (σ j) ℂ),
    ProductPrefixRigidity.productMap σ (fun j => (M j)ᴴ) =
      (ProductPrefixRigidity.productMap σ (R.readout () ⟨n, σ⟩ M))ᴴ

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have he := h (n := 1) (σ := fun _ => ULift.{u} Unit) (fun _ => 1)
  have hc := congrArg (fun X : Matrix (Fin 1 → ULift.{u} Unit)
    (Fin 1 → ULift.{u} Unit) ℂ => X (fun _ => ⟨()⟩) (fun _ => ⟨()⟩)) he
  norm_num [rejected, realize, ProductPrefixRigidity.productMap,
    Matrix.conjTranspose_apply] at hc
  change (1 : ℂ) = star (0 : ℂ) at hc
  exact one_ne_zero (hc.trans (star_zero ℂ))

theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro i
  refine ⟨⟨1, fun _ => ULift.{u} Unit⟩, 0, 1, ?_⟩
  intro he
  have hc := congrArg (fun M : ∀ _ : Fin 1,
    Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ => M 0 ⟨()⟩ ⟨()⟩) he
  change (0 : ℂ) = 1 at hc
  exact zero_ne_one hc

def source_registration : Registration arena.{u} (type_of% @tensor_star.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tensor_star, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@tensor_star.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.unit
  realizationName := `Reg.D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.NonlocalityDepthQuantumBound
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.QuantumBounds.NonlocalityDepthQuantumBound
