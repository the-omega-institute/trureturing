import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.FinitePositiveKernelQuotient
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Algebra.FinitePositiveKernelQuotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped InnerProductSpace Matrix ComplexOrder

namespace Reg.D5.S3.Quantum.Algebra.FinitePositiveKernelQuotient
noncomputable section
universe u v

structure Params where
  carrier : Type u
  finite : Fintype carrier
  matrix : Matrix carrier carrier ℂ
  positive : letI := finite; matrix.PosSemidef
  right : carrier → ℂ

abbrev signature : Signature where
  Params := Params.{u}
  State p := p.carrier → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p c =>
    letI := p.finite
    inner ℂ (mk p.matrix p.positive c) (mk p.matrix p.positive p.right))
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev innerArena : Arena where
  signature := signature.{u}
  Law r := ∀ {M : Type u} [fin : Fintype M] (D : Matrix M M ℂ) (hD : D.PosSemidef)
    (c d : M → ℂ), r.readout () ⟨M, fin, D, hD, d⟩ c = star c ⬝ᵥ D *ᵥ d

abbrev mainArena : Arena where
  signature := signature.{u}
  Law r := ∀ {M : Type u} [fin : Fintype M] (D : Matrix M M ℂ) (hD : D.PosSemidef)
    [DecidableEq M],
    (∀ c d : M → ℂ, r.readout () ⟨M, fin, D, hD, d⟩ c = star c ⬝ᵥ D *ᵥ d) ∧
    Module.finrank ℂ (Space D hD) = D.rank ∧
    (∀ i j, inner ℂ (label D hD i) (label D hD j) = D i j) ∧
    Submodule.span ℂ (Set.range (label D hD)) = ⊤ ∧
    (∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (w : M → E), (∀ i j, inner ℂ (w i) (w j) = D i j) →
      Submodule.span ℂ (Set.range w) = ⊤ →
      ∃! U : Space D hD ≃ₗᵢ[ℂ] E, ∀ i, U (label D hD i) = w i)

private theorem rejected_inner : ¬ innerArena.{u}.Law rejected := by
  intro h
  let M := ULift.{u} (Fin 1)
  have hh := @h M inferInstance 1 Matrix.PosSemidef.one 1 1
  norm_num [rejected, realize, Matrix.mulVec, dotProduct, M] at hh

private theorem rejected_main : ¬ mainArena.{u,v}.Law rejected := by
  intro h
  apply rejected_inner
  intro M fin D hD c d
  exact (@h M fin D hD (Classical.decEq M)).1 c d

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let M := ULift.{u} (Fin 1)
  refine ⟨⟨M, inferInstance, 1, Matrix.PosSemidef.one, 1⟩, 0, 1, ?_⟩
  simp [actual, realize, inner_mk, Matrix.mulVec, dotProduct, M]

def inner_source_registration : Registration innerArena (type_of% @inner_mk.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@inner_mk, rejected, rejected_inner⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_inner⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := actual_dependence

def main_source_registration :
    Registration mainArena.{u,v} (type_of% @finite_positive_kernel_quotient.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_positive_kernel_quotient, rejected, rejected_main⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_main⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := actual_dependence

def inner_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@inner_mk.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.FinitePositiveKernelQuotient.inner_mk.audit
  realizationName := `Reg.D5.S3.Quantum.Algebra.FinitePositiveKernelQuotient.inner_source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨innerArena⟩
  objectArena := .source ⟨innerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source innerArena ⟨inner_source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p c =>
    letI := p.finite
    inner ℂ (mk p.matrix p.positive c) (mk p.matrix p.positive p.right))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.FinitePositiveKernelQuotient
    definition := none
    coordinates := #[0, 1, 2, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def main_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@finite_positive_kernel_quotient.{u,v}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.FinitePositiveKernelQuotient.finite_positive_kernel_quotient.audit
  realizationName := `Reg.D5.S3.Quantum.Algebra.FinitePositiveKernelQuotient.main_source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨mainArena.{u,v}⟩
  objectArena := .source ⟨mainArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source mainArena.{u,v} ⟨main_source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p c =>
    letI := p.finite
    inner ℂ (mk p.matrix p.positive c) (mk p.matrix p.positive p.right))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.FinitePositiveKernelQuotient
    definition := none
    coordinates := #[0, 1, 2, 3, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Reg.D5.S3.Quantum.Algebra.FinitePositiveKernelQuotient
