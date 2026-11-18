import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFinitePositiveGerm

/-! Faithful source equations and germ equality observations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology
open _root_.D5.S3.VertexAlgebra.TwistedGround
open _root_.D5.S3.VertexAlgebra.TwistedGround.FiniteMode
open OriginalGaussianFiniteCandidateModes
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes

namespace positive_t_mode_equations
abbrev arena : Arena where
  signature := complexSignature
  Law obs := ∀ (p q : ℕ) {r : ℝ} (_hr : 0<r) (_hr1 : r<1),
    let U := fun e k => OriginalGaussianExternalDisplacement.modeFrequency e k
      (fun f l => OriginalGaussianSourceEvaluation.sourceAmplitude f l (r : ℂ))
    let V := fun e k =>
      2*(r : ℂ)*deriv (fun u : ℝ => OriginalGaussianSourceEvaluation.sourceAmplitude e k (u : ℂ)) r-U e k-
        2*(r : ℂ)*OriginalGaussianSourceEvaluation.sourceAmplitude e k r*
          OriginalGaussianAllIndexResolvent.shiftedCentralDerivative r 0/
            _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod.period r
    let L := (p+1/2 : ℂ)*(t p q r-
      (if p=0 then negativeZeroT q r else t (p-1) q r))
    let R := (q+1/2 : ℂ)*(t p q r-
      (if q=0 then negativeZeroT p r else t p (q-1) r))
    (obs.readout () () (L-R) ((1-(r : ℂ))*(U true p*V true q-V true p*U true q)/2)) ∧
    (2*(r : ℂ)*tPrime p q r-L-R =
      (1-(r : ℂ))/2*(V true p*V true q-U true p*U true q))

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact (h 0 0 (r := 1/2) (by norm_num) (by norm_num)).1

def family : Registration arena (type_of% (@positive_t_mode_equations)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@positive_t_mode_equations, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_t_mode_equations) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.positive_t_mode_equations.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.positive_t_mode_equations.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFinitePositiveGerm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end positive_t_mode_equations

namespace externalT_positive_finite_germ
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ p q, ∀ᶠ z in nhds (0 : ℂ),
    R.readout () () (OriginalGaussianExternalResolvent.externalT true p true q z)
      (candidateT p q z)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact (h 0 0).self_of_nhds

def family : Registration arena (type_of% (@externalT_positive_finite_germ)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@externalT_positive_finite_germ, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@externalT_positive_finite_germ) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.externalT_positive_finite_germ.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.externalT_positive_finite_germ.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFinitePositiveGerm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end externalT_positive_finite_germ

end Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes
