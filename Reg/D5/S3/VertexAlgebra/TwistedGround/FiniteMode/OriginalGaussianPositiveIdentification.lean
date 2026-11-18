import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianPositiveIdentification

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology
open _root_.D5.S3.VertexAlgebra.TwistedGround
open _root_.D5.S3.VertexAlgebra.TwistedGround.FiniteMode
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes
open OriginalGaussianFiniteCandidateModes

namespace externalT_positive_finite_eq
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (p q : ℕ) {z : ℂ} (_hz : ‖z‖ < 1),
    R.readout () () (OriginalGaussianExternalResolvent.externalT true p true q z)
      (candidateT p q z)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h 0 0 (z := 0) (by simp)

def family : Registration arena (type_of% (@externalT_positive_finite_eq)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@externalT_positive_finite_eq, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@externalT_positive_finite_eq) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.externalT_positive_finite_eq.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.externalT_positive_finite_eq.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianPositiveIdentification
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end externalT_positive_finite_eq
end Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianPositiveIdentification
open OriginalGaussianExternalGeneratedSource OriginalGaussianExternalAnalyticCandidate

namespace positiveJ_eq_candidateJ
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ {u v : ℂ} {r : ℝ} (_hr : 0 < r) (_hr1 : r < 1)
    (_hu : ‖u‖ + Real.sqrt r < 1) (_hv : ‖v‖ + Real.sqrt r < 1),
    R.readout () () (kernelMode false true true u v (Real.sqrt r : ℂ))
      (candidateJ u v (r : ℂ))
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  have hs : Real.sqrt (1/4 : ℝ) < 1 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1/4 by norm_num),
      Real.sqrt_nonneg (1/4 : ℝ)]
  exact @h 0 0 (1/4) (by norm_num) (by norm_num)
    (by simpa using hs) (by simpa using hs)
def family : Registration arena (type_of% (@positiveJ_eq_candidateJ)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@positiveJ_eq_candidateJ, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positiveJ_eq_candidateJ) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianPositiveIdentification.positiveJ_eq_candidateJ.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianPositiveIdentification.positiveJ_eq_candidateJ.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianPositiveIdentification
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end positiveJ_eq_candidateJ
end Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianPositiveIdentification
