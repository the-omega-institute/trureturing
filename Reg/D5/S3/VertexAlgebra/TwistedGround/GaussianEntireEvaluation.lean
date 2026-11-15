import D5.S3.VertexAlgebra.TwistedGround.GaussianEntireEvaluation
import Reg.Support.FactorialFockMetric

/-! Typed whole-family witnesses for native Gaussian summability and evaluation. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate
open D5.S3.VertexAlgebra.TwistedGround.GaussianEntireEvaluation

universe u
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.GaussianEntireEvaluation

namespace NormSummable

structure Modes where
  carrier : Type u
  finite : Fintype carrier
attribute [instance] Modes.finite

abbrev signature : Signature where
  Params := Modes.{u}
  State m := Matrix m.carrier m.carrier ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ m := (m.carrier →₀ ℕ) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize _ (fun _ _ E d => ‖gaussianCoefficient E d‖) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize _ (fun _ _ _ _ => 1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨PUnit.{u+1}, inferInstance⟩, (fun _ _ => 0), (fun _ _ => 2), ?_⟩
  intro h
  have hh := congrFun h (Finsupp.single PUnit.unit 2)
  norm_num [actual, realize, gaussianCoefficient, gaussianPiece, quadratic,
    MvPolynomial.X, MvPolynomial.smul_monomial, MvPolynomial.monomial_mul_monomial,
    ← Finsupp.single_add] at hh

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {I : Type u} [Fintype I] (E : Matrix I I ℂ),
    Summable (r.readout () ⟨I, inferInstance⟩ E)

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h PUnit.{u+1} inferInstance 0
  change Summable (fun _ : PUnit.{u+1} →₀ ℕ => (1 : ℝ)) at hh
  simp only [summable_const_iff, one_ne_zero] at hh

def family : Registration arena.{u} (type_of% (@gaussianCoefficient_norm_summable.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@gaussianCoefficient_norm_summable.{u}, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gaussianCoefficient_norm_summable.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.GaussianEntireEvaluation.NormSummable.unit
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.TwistedGround.GaussianEntireEvaluation.NormSummable.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.GaussianEntireEvaluation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NormSummable

namespace Evaluation
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ {I : Type u} [Fintype I] (E : Matrix I I ℂ),
    r.readout () () (∑' d, gaussianCoefficient E d)
      (Complex.exp ((1 / 2 : ℂ) * ∑ i, ∑ j, E i j))

private theorem rejected_fails : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact @h PUnit.{u+1} inferInstance 0

def family : Registration arena.{u} (type_of% (@gaussianCoefficient_tsum.{u})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@gaussianCoefficient_tsum.{u}, complexFalse, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨complexFalse, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gaussianCoefficient_tsum.{u}) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.GaussianEntireEvaluation.Evaluation.unit
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.TwistedGround.GaussianEntireEvaluation.Evaluation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.GaussianEntireEvaluation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Evaluation
end Reg.D5.S3.VertexAlgebra.TwistedGround.GaussianEntireEvaluation
