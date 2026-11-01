import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum
import Reg.Support.DependentFamily
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum
open _root_.D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate
open _root_.D5.S3.VertexAlgebra.FactorialFockMetric (weight)

universe u
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum

abbrev signature : Signature where
  Params := Σ I : Type u, I →₀ ℕ
  State p := (p.1 →₀ ℕ) → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize _ (fun _ p f => f p.2) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize _ (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1),
    Summable (fun d : I →₀ ℕ =>
      ‖(weight d : ℂ) * gaussianCoefficient A d * gaussianCoefficient B d‖) ∧
    Summable (fun n : ℕ => Matrix.trace ((A * B) ^ (n + 1)) / (n + 1 : ℂ)) ∧
      (∑' d : I →₀ ℕ, (weight d : ℂ) *
        R.readout () ⟨I, d⟩ (gaussianCoefficient A) * gaussianCoefficient B d) =
        Complex.exp ((1 / 2 : ℂ) *
          ∑' n : ℕ, Matrix.trace ((A * B) ^ (n + 1)) / (n + 1 : ℂ))

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h PUnit.{u+1} inferInstance inferInstance 0 0
    (fun _ _ => rfl) (fun _ _ => rfl) (by simp) (by simp)
  simpa [rejected, realize] using hh.2.2

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨PUnit.{u+1}, 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize]

def evidence : Registration arena.{u} (type_of% (@vacuum_trace_log.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@vacuum_trace_log.{u}, rejected, rejected_fails⟩
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
    (@vacuum_trace_log.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum.evidence
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum
    definition := none
    coordinates := #[0, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg", "fn", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum
