import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.PBPolynomialZero
import Reg.Support.DependentFamily

/-! The complete source telescope with an equality observation on its original carrier. -/

namespace Reg.D5.S3.Quantum.Algebra.PBPolynomialZero
open _root_.D5.S3.Quantum.Algebra.PBPolynomialZero
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial
set_option autoImplicit false
noncomputable section
universe u

abbrev signature : Signature where
  Params := Type u
  State E := E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ E := E → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ a b => a = b) (fun e => Empty.elim e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => Empty.elim e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (unit : E)
    (_A : _root_.D5.S3.Topology.JBAlgebra.Data E J unit) (D : E → E → E)
    (_pb : _root_.D5.S3.Quantum.Algebra.PBActualOuterBudget.PB J D)
    (_rot : ∀ a b θ, D (Real.cos θ • a - Real.sin θ • b)
      (Real.sin θ • a + Real.cos θ • b) = D a b)
    (_hl : ∀ a b, D (-a) b = -D a b)
    (_hr : ∀ a b, D a (-b) = -D a b)
    (_aff : ∀ (a : E) (s t r v : ℝ), D (s • unit + r • a) (t • unit + v • a) = 0)
    (x : E) (p q : ℝ[X]),
    R.readout () E (D (eval J unit x p) (eval J unit x q)) 0

private abbrev Witness := ULift.{u} PUnit.{1}
private theorem witnessJB : _root_.D5.S3.Topology.JBAlgebra.Data Witness.{u} 0 0 where
  symm _ _ := Subsingleton.elim _ _
  unit_mul _ := Subsingleton.elim _ _
  jordan _ _ := Subsingleton.elim _ _
  product_norm x y := by simp [Subsingleton.elim x 0, Subsingleton.elim y 0]
  square_norm x := by simp [Subsingleton.elim x 0]
  square_mono x y := by simp [Subsingleton.elim x 0, Subsingleton.elim y 0]

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hp : _root_.D5.S3.Quantum.Algebra.PBActualOuterBudget.PB
      (0 : Witness.{u} →ₗ[ℝ] Witness.{u} →ₗ[ℝ] Witness.{u}) (fun _ _ => 0) := by
    intro a b c
    exact Subsingleton.elim _ _
  exact @h Witness.{u} inferInstance inferInstance 0 0 witnessJB (fun _ _ => 0) hp
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ _ => Subsingleton.elim _ _)
    (fun _ _ => Subsingleton.elim _ _) (fun _ _ _ _ _ => Subsingleton.elim _ _) 0 0 0

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Bool, ⟨false⟩, ⟨true⟩, ?_⟩
  intro he
  have he' := congrFun he ⟨false⟩
  have ht : (ULift.up true : ULift.{u} Bool) = ULift.up false := Eq.mp he' rfl
  cases congrArg ULift.down ht

def source_registration : Registration arena.{u} (type_of% @polynomial_zero.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@polynomial_zero.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, u, 0, 0}
    (@polynomial_zero.{u}) (Realization signature.{u}) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Algebra.PBPolynomialZero.unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.PBPolynomialZero.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a = b) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.PBPolynomialZero
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.Quantum.Algebra.PBPolynomialZero
