import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianSewing
import Reg.Support.DependentFamily
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators lp
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock
open _root_.D5.S3.VertexAlgebra.TwistedGround.GaussianExternalBlock
open _root_.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianSewing
open _root_.D5.S3.VertexAlgebra.TwistedGround.CountableGaussianCutoff
open _root_.D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate
open _root_.D5.S3.VertexAlgebra.FactorialFockMetric (Occupation weight)
universe u v w
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianSewing

abbrev signature : Signature where
  Params := Σ I : Type v, Occupation I
  State p := Occupation p.1 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize _ (fun _ p f => f p.2) (fun e => nomatch e)

def rejected : Realization signature.{v} :=
  realize _ (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{v}
  Law V := ∀ {X : Type u} {I : Type v} {Y : Type w}
    [Fintype X] [DecidableEq X] [DecidableEq I] [Fintype Y] [DecidableEq Y]
    (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ) (A B : Data I)
    (R : X → ℓ²(I, ℂ)) (S : Y → ℓ²(I, ℂ))
    (hP : ∀ x y, P x y = P y x) (hQ : ∀ x y, Q x y = Q y x)
    (d : Occupation X) (e : Occupation Y),
    Summable (fun n : Occupation I => ‖(weight n : ℂ) *
      coefficient (kernel P A R) (d.sumElim n) *
      coefficient (rightKernel Q B S) (n.sumElim e)‖) ∧
    (∑' n : Occupation I, (weight n : ℂ) *
      V.readout () ⟨I,n⟩ (fun m => coefficient (kernel P A R) (d.sumElim m)) *
      coefficient (rightKernel Q B S) (n.sumElim e)) =
      Complex.exp (TraceClassPowerSeries.traceLog (product A B)) *
        coefficient (effectiveKernel P Q A B R S) (d.sumElim e)

private theorem rejected_fails : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let Z : Data PUnit.{v+1} := {
    oneParticle := 0
    q := 0
    massBound := 0
    q_nonneg := le_rfl
    q_lt_one := zero_lt_one
    opNorm_le := by simp
    symmetric := by simp
    square_summable := by simp
    square_sum_le := by simp }
  have hh := (@h PUnit.{u+1} PUnit.{v+1} PUnit.{w+1}
    inferInstance inferInstance inferInstance inferInstance inferInstance
    0 0 Z Z (fun _ => 0) (fun _ => 0) (by simp) (by simp) 0 0).2
  have hz : (0 : ℂ) = Complex.exp (TraceClassPowerSeries.traceLog (product Z Z)) := by
    simpa [rejected, realize, coefficient, restrictOccupation, gaussianCoefficient_zero] using hh
  exact Complex.exp_ne_zero _ hz.symm

private theorem actual_dependence : ObservationalDependence signature.{v} actual := by
  intro i
  refine ⟨⟨PUnit.{v+1}, 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [actual, realize]

def evidence : Registration arena.{u,v,w} (type_of% (@sewing.{u,v,w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sewing.{u,v,w}, rejected, rejected_fails⟩
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
    (@sewing.{u,v,w}) (Realization signature.{v}) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianSewing.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianSewing.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianSewing
