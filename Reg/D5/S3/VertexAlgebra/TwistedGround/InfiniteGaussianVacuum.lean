import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianVacuum
import Reg.Support.DependentFamily
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock
open _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianVacuum
open _root_.D5.S3.VertexAlgebra.TwistedGround.CountableGaussianCutoff
open _root_.D5.S3.VertexAlgebra.FactorialFockMetric (Occupation weight)

universe u
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianVacuum

abbrev signature : Signature where
  Params := Σ I : Type u, Occupation I
  State p := Occupation p.1 → ℂ
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
  Law R := ∀ {I : Type u} [DecidableEq I] (A B : Data I),
    Summable (fun d : Occupation I =>
      ‖(weight d : ℂ) * coefficient A.kernel d * coefficient B.kernel d‖) ∧
    Summable (fun m : ℕ => ‖TraceClassPowerSeries.logTerm (product A B) m‖) ∧
      (∑' d : Occupation I, (weight d : ℂ) *
        R.readout () ⟨I, d⟩ (coefficient A.kernel) * coefficient B.kernel d) =
        Complex.exp (TraceClassPowerSeries.traceLog (product A B))

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  let Z : Data PUnit.{u+1} := {
    oneParticle := 0
    q := 0
    massBound := 0
    q_nonneg := le_rfl
    q_lt_one := zero_lt_one
    opNorm_le := by simp
    symmetric := by simp
    square_summable := by simp
    square_sum_le := by simp }
  have hh := (@h PUnit.{u+1} inferInstance Z Z).2.2
  have hz : (0 : ℂ) = Complex.exp (TraceClassPowerSeries.traceLog (product Z Z)) := by
    simpa [rejected, realize] using hh
  exact Complex.exp_ne_zero _ hz.symm

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
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianVacuum.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianVacuum.evidence
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianVacuum
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "fn", "arg",
        "fn", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianVacuum
