import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumBounds.NonlocalityDepthQuantumBound
import Reg.Support.SingleDependentReadout

/-! Source-bound audits of tensor adjoints and binary Hermitian involutions. -/

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

namespace Reg.D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.InvolutionBinary
open LeanInformationAudit Matrix
open _root_.D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.Upper
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u_1

/-- Observe the subtraction in the positivity conclusion at its identity operand. -/
abbrev signature : Signature where
  Params := Σ m : Type u_1, Matrix m m ℂ
  State p := Matrix p.1 p.1 ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.1 p.1 ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u_1} :=
  realize signature (fun _ p X => X - p.2) (fun e => nomatch e)

def rejected : Realization signature.{u_1} := by
  classical
  exact realize signature (fun _ p _ => (-1 : Matrix p.1 p.1 ℂ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u_1}
  Law R := ∀ {m : Type u_1} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ), A.IsHermitian → A ^ 2 = 1 →
      (R.readout () ⟨m, A⟩ 1).PosSemidef ∧ (1 + A).PosSemidef

theorem rejected_law : ¬ arena.{u_1}.Law rejected.{u_1} := by
  intro h
  have he := (h (m := ULift.{u_1} Unit) 1 (by simp) (by simp)).1
  have hd := he.diag_nonneg (i := (⟨()⟩ : ULift.{u_1} Unit))
  norm_num [rejected, realize, Matrix.neg_apply, Matrix.one_apply, Complex.le_def] at hd

def source_registration : Registration arena.{u_1} (type_of% @involution_binary.{u_1}) where
  actual := realize signature (fun _ p X => X - p.2) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨involution_binary, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u_1} Unit, 0⟩, 0, 1, ?_⟩
    intro h
    have he := congrArg (fun X : Matrix (ULift.{u_1} Unit) (ULift.{u_1} Unit) ℂ =>
      X ⟨()⟩ ⟨()⟩) h
    norm_num [actual, realize, Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply] at he
    exact zero_ne_one he

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@involution_binary.{u_1}) (Realization signature.{u_1}) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.InvolutionBinary.unit
  realizationName :=
    `Reg.D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.InvolutionBinary.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p X => X - p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.NonlocalityDepthQuantumBound
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.InvolutionBinary

namespace Reg.D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.ExpectationUpper
open _root_.D5.S3.QuantumBounds.NonlocalityDepthQuantumBound (expectation_upper)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- Observe the order relation between the expectation and its upper bound. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : Type u} [Fintype m] [DecidableEq m]
    (rho B : Matrix m m ℂ) (q : ℝ)
    (_hr : rho.PosSemidef ∧ Matrix.trace rho = 1)
    (_hp : (q • (1 : Matrix m m ℂ) - B).PosSemidef),
    R.readout () () (Matrix.trace (rho * B)).re q

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) 0 0
    ⟨Matrix.PosSemidef.one, by simp [Matrix.trace]⟩
    (by simpa using (Matrix.PosSemidef.zero :
      (0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ).PosSemidef))

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  exact (show ¬ (1 : ℝ) ≤ 0 by norm_num) (Eq.mp he (le_refl 0))

def source_registration : Registration arena.{u} (type_of% @expectation_upper.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@expectation_upper, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@expectation_upper.{u}) (Realization signature) Unit Unit := {
  unitName := .str
    `D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.expectation_upper "__information_unit"
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.NonlocalityDepthQuantumBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
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
end Reg.D5.S3.QuantumBounds.NonlocalityDepthQuantumBound.ExpectationUpper
