import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.TwistedGround.ElementaryGaussianContraction

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.TwistedGround.ElementaryGaussianContraction
open _root_.D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate
open _root_.D5.S3.VertexAlgebra.FactorialFockMetric (weight)

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.ElementaryGaussianContraction

universe u v w
structure Modes where
  carrier : Type u
  finite : Fintype carrier
  decidable : DecidableEq carrier
attribute [instance] Modes.finite Modes.decidable

structure Parameters where
  external : Modes.{u}
  shared : Modes.{v}
  output : Modes.{w}
  P : Matrix external.carrier external.carrier ℂ
  Q : Matrix output.carrier output.carrier ℂ
  R : Matrix external.carrier shared.carrier ℂ
  S : Matrix shared.carrier output.carrier ℂ
  symmetricP : ∀ i j, P i j = P j i
  symmetricQ : ∀ i j, Q i j = Q j i
  occupation : output.carrier →₀ ℕ

abbrev signature : Signature where
  Params := Parameters.{u,v,w}
  State p := p.external.carrier →₀ ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v,w} := realize _
  (fun _ p d => gaussianCoefficient (effectiveKernel p.P p.Q p.R p.S)
    (d.sumElim p.occupation)) (fun e => nomatch e)

def rejected : Realization signature.{u,v,w} := realize _ (fun _ _ _ => 0)
  (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v,w}
  Law X := ∀ (p : Parameters.{u,v,w}) (d : p.external.carrier →₀ ℕ),
    (∑ n ∈ (Finsupp.finite_of_degree_le (σ := p.shared.carrier)
        (min d.degree p.occupation.degree)).toFinset,
      (weight n : ℂ) * gaussianCoefficient (leftKernel p.P p.R) (d.sumElim n) *
        gaussianCoefficient (rightKernel p.Q p.S) (n.sumElim p.occupation)) =
      X.readout () p d

private theorem bridge : (type_of% (@coefficient_contraction.{u,v,w})) ↔
    arena.{u,v,w}.Law actual := by
  constructor
  · intro h p d
    exact h p.P p.Q p.R p.S p.symmetricP p.symmetricQ d p.occupation
  · intro h I J E _ _ _ _ _ _ P Q R S hP hQ d e
    exact h ⟨⟨I, inferInstance, inferInstance⟩, ⟨J, inferInstance, inferInstance⟩,
      ⟨E, inferInstance, inferInstance⟩, P, Q, R, S, hP, hQ, e⟩ d

private def zeroParameters : Parameters.{u,v,w} where
  external := ⟨PUnit.{u+1}, inferInstance, inferInstance⟩
  shared := ⟨PUnit.{v+1}, inferInstance, inferInstance⟩
  output := ⟨PUnit.{w+1}, inferInstance, inferInstance⟩
  P := 0
  Q := 0
  R := 0
  S := 0
  symmetricP := by intros; rfl
  symmetricQ := by intros; rfl
  occupation := 0

private theorem rejected_fails : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  have hh := h zeroParameters 0
  have hv := (bridge.mp (@coefficient_contraction.{u,v,w})) zeroParameters 0
  change _ = (0 : ℂ) at hh
  rw [hv] at hh
  dsimp only [zeroParameters] at hh
  change gaussianCoefficient _ ((0 : PUnit.{u+1} →₀ ℕ).sumElim 0) = 0 at hh
  simpa only [Finsupp.sumElim_zero_zero, gaussianCoefficient_zero, one_ne_zero] using hh

private theorem dependence : ObservationalDependence signature.{u,v,w} actual := by
  intro role
  refine ⟨zeroParameters, 0, Finsupp.single PUnit.unit 1, ?_⟩
  intro h
  dsimp only [zeroParameters] at h
  change gaussianCoefficient _ ((0 : PUnit.{u+1} →₀ ℕ).sumElim 0) =
    gaussianCoefficient _ ((Finsupp.single PUnit.unit 1 : PUnit.{u+1} →₀ ℕ).sumElim 0) at h
  rw [Finsupp.sumElim_zero_zero, gaussianCoefficient_zero,
    Finsupp.sumElim_single_zero, gaussianCoefficient_odd _ _ (by simp)] at h
  exact one_ne_zero h

def evidence : Registration arena.{u,v,w} (type_of% (@coefficient_contraction.{u,v,w})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp coefficient_contraction, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      change Unit at i j
      exact (hj (@Subsingleton.elim Unit inferInstance j i)).elim
    · intro e
      cases e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@coefficient_contraction.{u,v,w}) (Realization signature.{u,v,w}) Type Unit where
  unitName := `D5.S3.VertexAlgebra.TwistedGround.ElementaryGaussianContraction.coefficient_contraction.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ElementaryGaussianContraction.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w}⟩
  objectArena := .source ⟨arena.{u,v,w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w} ⟨evidence.{u,v,w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v,w} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.ElementaryGaussianContraction
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 15
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Reg.D5.S3.VertexAlgebra.TwistedGround.ElementaryGaussianContraction
