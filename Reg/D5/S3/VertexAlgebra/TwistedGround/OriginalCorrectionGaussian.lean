import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectionGaussian

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectionGaussian
open _root_.D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectionGaussian

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intros; rfl
  even_diagonal := by intro i; exact Fin.elim0 i

universe u
structure Modes where
  carrier : Type u
  finite : Fintype carrier
  decidable : DecidableEq carrier
attribute [instance] Modes.finite Modes.decidable

namespace LinearForms

structure Parameters where
  modes : Modes.{u}
  lattice : LatticeData
  shift : ℂ
  coefficients : modes.carrier → Index lattice →₀ ℂ

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
  (fun _ p d =>
    (_root_.D5.S3.VertexAlgebra.FactorialFockMetric.weight d : ℂ) *
      gaussianCoefficient (covarianceMatrix p.lattice p.shift p.coefficients) d)
  (fun e => nomatch e)

def rejected : Realization signature.{u} := realize _ (fun _ _ _ => 0)
  (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ p d,
    sourceVacuum p.lattice p.shift (∏ i, linearForm p.lattice (p.coefficients i) ^ d i) =
      R.readout () p d

private theorem bridge : (type_of% (@sourceVacuum_linearForms.{u})) ↔
    arena.{u}.Law actual := by
  constructor
  · intro h p d
    exact h p.lattice p.shift p.coefficients d
  · intro h I _ _ D z c d
    exact h ⟨⟨I, inferInstance, inferInstance⟩, D, z, c⟩ d

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  let p : Parameters.{u} :=
    ⟨⟨PUnit.{u+1}, inferInstance, inferInstance⟩, emptyLattice, 0, 0⟩
  have hh := h p 0
  have hv := sourceVacuum_linearForms emptyLattice 0
    (0 : PUnit.{u+1} → Index emptyLattice →₀ ℂ) 0
  change sourceVacuum emptyLattice 0 _ = 0 at hh
  rw [hv] at hh
  norm_num [gaussianCoefficient_zero, _root_.D5.S3.VertexAlgebra.FactorialFockMetric.weight] at hh

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  let p : Parameters.{u} :=
    ⟨⟨PUnit.{u+1}, inferInstance, inferInstance⟩, emptyLattice, 0, 0⟩
  refine ⟨p, 0, Finsupp.single PUnit.unit 1, ?_⟩
  intro h
  change (_root_.D5.S3.VertexAlgebra.FactorialFockMetric.weight (0 : PUnit.{u+1} →₀ ℕ) : ℂ) *
      gaussianCoefficient (covarianceMatrix emptyLattice 0 0) 0 =
    (_root_.D5.S3.VertexAlgebra.FactorialFockMetric.weight
      (Finsupp.single PUnit.unit 1 : PUnit.{u+1} →₀ ℕ) : ℂ) *
      gaussianCoefficient (covarianceMatrix emptyLattice 0 0) (Finsupp.single PUnit.unit 1) at h
  rw [gaussianCoefficient_zero, gaussianCoefficient_odd _ _ (by simp)] at h
  norm_num [_root_.D5.S3.VertexAlgebra.FactorialFockMetric.weight] at h

def evidence : Registration arena.{u} (type_of% (@sourceVacuum_linearForms.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp sourceVacuum_linearForms, rejected, rejected_fails⟩
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
    (@sourceVacuum_linearForms.{u}) (Realization signature.{u})
    Type Unit where
  unitName := `D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectionGaussian.sourceVacuum_linearForms.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectionGaussian.LinearForms.evidence
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectionGaussian
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end LinearForms
namespace Evaluation

abbrev signature : Signature where
  Params := LatticeData × ℂ
  State p := Oscillator p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _
  (fun _ p s =>
    MvPolynomial.eval (fun a : Option (Index p.1) => a.elim p.2 (fun _ => 0))
      (correctionLift p.1 0 s)) (fun e => nomatch e)

def rejected : Realization signature := realize _ (fun _ _ _ => 1)
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ p s, sourceVacuum p.1 p.2 s = R.readout () p s

private theorem bridge : (type_of% (@sourceVacuum_eq_evaluation)) ↔ arena.Law actual := by
  constructor
  · intro h p s; exact h p.1 p.2 s
  · intro h D z p; exact h (D, z) p

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := h (emptyLattice, 0) 0
  change sourceVacuum emptyLattice 0 0 = 1 at hh
  simpa only [map_zero, zero_ne_one] using hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(emptyLattice, 0), MvPolynomial.C 0, MvPolynomial.C 1, ?_⟩
  intro h
  change MvPolynomial.eval _ (correctionLift emptyLattice 0 (MvPolynomial.C 0)) =
    MvPolynomial.eval _ (correctionLift emptyLattice 0 (MvPolynomial.C 1)) at h
  simp only [correctionLift_C, MvPolynomial.eval_C] at h
  exact zero_ne_one h

def evidence : Registration arena (type_of% (@sourceVacuum_eq_evaluation)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp sourceVacuum_eq_evaluation, rejected, rejected_fails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_fails
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sourceVacuum_eq_evaluation) (Realization signature)
    Type Unit where
  unitName := `D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectionGaussian.sourceVacuum_eq_evaluation.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectionGaussian.Evaluation.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectionGaussian
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Evaluation
end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectionGaussian
