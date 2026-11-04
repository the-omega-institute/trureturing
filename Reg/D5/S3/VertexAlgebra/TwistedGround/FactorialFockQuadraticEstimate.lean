import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate
import Reg.Support.DependentFamily
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate
open _root_.D5.S3.VertexAlgebra.FactorialFockMetric (weight)

universe u
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate

structure Modes where
  carrier : Type u
  finite : Fintype carrier
  decidable : DecidableEq carrier
attribute [instance] Modes.finite Modes.decidable

abbrev signature : Signature where
  Params := Modes.{u} × ℝ
  State p := Matrix p.1.carrier p.1.carrier ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize _ (fun _ p A => Real.exp ((∑ i, ∑ j, ‖A i j‖ ^ 2) /
    (2 * (1 - p.2 ^ 2)))) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize _ (fun _ _ _ => -1) (fun e => nomatch e)
private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨(⟨PUnit.{u+1}, inferInstance, inferInstance⟩, 1 / 2),
    (fun _ _ => 0), (fun _ _ => 1 / 2), ?_⟩
  intro h
  have hh := congrArg Real.log h
  norm_num [actual, realize, Real.log_exp] at hh

namespace Partial
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hsym : ∀ i j, A i j = A j i)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ ≤ q) (N : ℕ),
    (∑ n ∈ Finset.range (N + 1), mass (gaussianPiece A n)) ≤
      R.readout () (⟨I, inferInstance, inferInstance⟩, q) A
private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h PUnit.{u+1} inferInstance inferInstance 0
    (fun _ _ => rfl) 0 (by norm_num) (by norm_num)
    (by simp) 0
  norm_num [rejected, realize, gaussianPiece, mass_eq_sum, weight] at hh

def evidence : Registration arena.{u} (type_of% (@all_degree_partial_bound.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@all_degree_partial_bound.{u}, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      change Unit at i j
      exact (hj (@Subsingleton.elim Unit inferInstance j i)).elim
    · intro e
      cases e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@all_degree_partial_bound.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate.Partial.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate.Partial.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate
    definition := none
    coordinates := #[0, 1, 2, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Partial

namespace Occupations
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hsym : ∀ i j, A i j = A j i)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ ≤ q) (S : Finset (I →₀ ℕ)),
    (∑ d ∈ S, (weight d : ℝ) * ‖gaussianCoefficient A d‖ ^ 2) ≤
      R.readout () (⟨I, inferInstance, inferInstance⟩, q) A
private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h PUnit.{u+1} inferInstance inferInstance 0
    (fun _ _ => rfl) 0 (by norm_num) (by norm_num)
    (by simp) ∅
  norm_num [rejected, realize, gaussianPiece, mass_eq_sum, weight] at hh

def evidence : Registration arena.{u} (type_of% (@finite_occupation_bound.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_occupation_bound.{u}, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      change Unit at i j
      exact (hj (@Subsingleton.elim Unit inferInstance j i)).elim
    · intro e
      cases e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_occupation_bound.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate.Occupations.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate.Occupations.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate
    definition := none
    coordinates := #[0, 1, 2, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Occupations

namespace Recurrence
abbrev signature : Signature where
  Params := Modes.{u} × ℕ
  State p := Matrix p.1.carrier p.1.carrier ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize _ (fun _ p A => mass (gaussianPiece A (p.2 + 1))) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize _ (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hsym : ∀ i j, A i j = A j i)
    {q : ℝ} (hq : 0 ≤ q)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ ≤ q) (n : ℕ),
    (n + 1 : ℝ) * R.readout () (⟨I, inferInstance, inferInstance⟩, n) A ≤
      ((∑ i, ∑ j, ‖A i j‖ ^ 2) / 2 + q ^ 2 * n) * mass (gaussianPiece A n)
private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h PUnit.{u+1} inferInstance inferInstance 0
    (fun _ _ => rfl) 0 (by norm_num) (by simp) 0
  norm_num [rejected, realize] at hh
private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨(⟨PUnit.{u+1}, inferInstance, inferInstance⟩, 0),
    (fun _ _ => 0), (fun _ _ => 1), ?_⟩
  intro h
  norm_num [actual, realize, mass_eq_sum, gaussianPiece, quadratic, MvPolynomial.X,
    MvPolynomial.smul_monomial, MvPolynomial.monomial_mul_monomial, MvPolynomial.support_monomial,
    Finsupp.prod_single_index, weight,
    ← Finsupp.single_add] at h

def evidence : Registration arena.{u} (type_of% (@degree_mass_recurrence.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@degree_mass_recurrence.{u}, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      change Unit at i j
      exact (hj (@Subsingleton.elim Unit inferInstance j i)).elim
    · intro e
      cases e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@degree_mass_recurrence.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate.Recurrence.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate.Recurrence.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate
    definition := none
    coordinates := #[0, 1, 2, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Recurrence

end Reg.D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate
