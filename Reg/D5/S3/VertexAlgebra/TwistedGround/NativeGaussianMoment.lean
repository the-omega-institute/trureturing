import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.TwistedGround.NativeGaussianMoment

/-! Dependent-family evidence for the full finite-mode Gaussian insertion equation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.TwistedGround.NativeGaussianMoment
open _root_.D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate
open _root_.D5.S3.VertexAlgebra.FactorialFockMetric (weight)

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.NativeGaussianMoment

universe u
structure Modes where
  carrier : Type u
  finite : Fintype carrier
  decidable : DecidableEq carrier
attribute [instance] Modes.finite Modes.decidable

structure Parameters where
  modes : Modes.{u}
  matrix : Matrix modes.carrier modes.carrier ℂ
  symmetric : ∀ i j, matrix i j = matrix j i
  inserted : modes.carrier

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.modes.carrier →₀ ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize _
  (fun _ p r => ∑ j, (r j : ℂ) * p.matrix p.inserted j *
    nativeMoment p.matrix (r - Finsupp.single j 1)) (fun e => nomatch e)

def rejected : Realization signature.{u} := realize _ (fun _ _ _ => 1)
  (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law X := ∀ (p : Parameters.{u}) (r : p.modes.carrier →₀ ℕ),
    nativeMoment p.matrix (r + Finsupp.single p.inserted 1) = X.readout () p r

private theorem bridge : (type_of% (@nativeMoment_step.{u})) ↔
    arena.{u}.Law actual := by
  constructor
  · intro h p r
    exact h p.matrix p.symmetric r p.inserted
  · intro h I _ _ A hs r i
    exact h ⟨⟨I, inferInstance, inferInstance⟩, A, hs, i⟩ r

private def unitParameters : Parameters.{u} where
  modes := ⟨PUnit.{u+1}, inferInstance, inferInstance⟩
  matrix := fun _ _ => 1
  symmetric := by intros; rfl
  inserted := PUnit.unit

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h unitParameters 0
  dsimp only [unitParameters] at hh
  change nativeMoment (fun _ _ : PUnit.{u+1} => 1)
    ((0 : PUnit.{u+1} →₀ ℕ) + Finsupp.single PUnit.unit 1) = 1 at hh
  rw [zero_add, nativeMoment, gaussianCoefficient_odd _ _ (by simp), mul_zero] at hh
  exact zero_ne_one hh

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨unitParameters, 0, Finsupp.single PUnit.unit 1, ?_⟩
  intro h
  dsimp only [actual, unitParameters] at h
  change (∑ j : PUnit.{u+1}, ((0 : PUnit.{u+1} →₀ ℕ) j : ℂ) * 1 *
      nativeMoment (fun _ _ : PUnit.{u+1} => 1)
        ((0 : PUnit.{u+1} →₀ ℕ) - Finsupp.single j 1)) =
    ∑ j : PUnit.{u+1}, ((Finsupp.single PUnit.unit 1 : PUnit.{u+1} →₀ ℕ) j : ℂ) * 1 *
      nativeMoment (fun _ _ : PUnit.{u+1} => 1)
        (Finsupp.single PUnit.unit 1 - Finsupp.single j 1) at h
  norm_num [nativeMoment, gaussianCoefficient_zero, weight] at h

def evidence : Registration arena.{u} (type_of% (@nativeMoment_step.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp nativeMoment_step, rejected, rejected_fails⟩
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
    (@nativeMoment_step.{u}) (Realization signature.{u}) Type Unit where
  unitName :=
    `D5.S3.VertexAlgebra.TwistedGround.NativeGaussianMoment.nativeMoment_step.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.NativeGaussianMoment.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.NativeGaussianMoment
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Reg.D5.S3.VertexAlgebra.TwistedGround.NativeGaussianMoment
