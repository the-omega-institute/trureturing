import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications

noncomputable section
open _root_.D5.S3.VertexAlgebra.TwistedGround
open OriginalGaussianComplexRadialContinuation OriginalGaussianExternalGeneratedSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications

namespace positiveJ_eq_candidateJ_complex
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ {u v z : ℂ}
      (_hu : ‖u‖ + ‖z‖ < 1) (_hv : ‖v‖ + ‖z‖ < 1),
    R.readout () () (kernelMode false true true u v z)
      (OriginalGaussianExternalSignedCandidate.candidateJ true true u v (z ^ 2))
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh (u := 0) (v := 0) (z := 0) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@positiveJ_eq_candidateJ_complex)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@positiveJ_eq_candidateJ_complex, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positiveJ_eq_candidateJ_complex) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications.positiveJ_eq_candidateJ_complex.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications.positiveJ_eq_candidateJ_complex.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end positiveJ_eq_candidateJ_complex

namespace signedJ_eq_candidateJ_complex
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (e f : Bool) {u v z : ℂ}
      (_hu : ‖u‖ + ‖z‖ < 1) (_hv : ‖v‖ + ‖z‖ < 1)
      (_hneg : e = false ∨ f = false),
    R.readout () () (kernelMode false e f u v z)
      (OriginalGaussianExternalSignedCandidate.candidateJ e f u v (z ^ 2))
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh false false (u := 0) (v := 0) (z := 0) (by norm_num) (by norm_num) (Or.inl rfl)
def family : Registration arena (type_of% (@signedJ_eq_candidateJ_complex)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@signedJ_eq_candidateJ_complex, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@signedJ_eq_candidateJ_complex) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications.signedJ_eq_candidateJ_complex.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications.signedJ_eq_candidateJ_complex.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end signedJ_eq_candidateJ_complex

namespace allSignsJ_eq_candidateJ_complex
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (e f : Bool) {u v z : ℂ}
      (_hu : ‖u‖ + ‖z‖ < 1) (_hv : ‖v‖ + ‖z‖ < 1),
    R.readout () () (kernelMode false e f u v z)
      (OriginalGaussianExternalSignedCandidate.candidateJ e f u v (z ^ 2))
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh false false (u := 0) (v := 0) (z := 0) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@allSignsJ_eq_candidateJ_complex)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@allSignsJ_eq_candidateJ_complex, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@allSignsJ_eq_candidateJ_complex) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications.allSignsJ_eq_candidateJ_complex.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications.allSignsJ_eq_candidateJ_complex.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications
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
end allSignsJ_eq_candidateJ_complex

namespace signedT_eq_candidateT_complex
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (e f : Bool) {u v z : ℂ}
      (_hu : ‖u‖ + ‖z‖ < 1) (_hv : ‖v‖ + ‖z‖ < 1)
      (_hneg : e = false ∨ f = false),
    R.readout () () (kernelMode true e f u v z)
      (OriginalGaussianExternalSignedCandidate.candidateT e f u v (z ^ 2))
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh false false (u := 0) (v := 0) (z := 0) (by norm_num) (by norm_num) (Or.inl rfl)
def family : Registration arena (type_of% (@signedT_eq_candidateT_complex)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@signedT_eq_candidateT_complex, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@signedT_eq_candidateT_complex) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications.signedT_eq_candidateT_complex.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications.signedT_eq_candidateT_complex.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end signedT_eq_candidateT_complex

namespace positiveT_eq_candidateT_complex
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ {u v z : ℂ}
      (_hu : ‖u‖ + ‖z‖ < 1) (_hv : ‖v‖ + ‖z‖ < 1),
    R.readout () () (kernelMode true true true u v z)
      (OriginalGaussianExternalSignedCandidate.candidateT true true u v (z ^ 2))
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh (u := 0) (v := 0) (z := 0) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@positiveT_eq_candidateT_complex)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@positiveT_eq_candidateT_complex, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positiveT_eq_candidateT_complex) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications.positiveT_eq_candidateT_complex.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications.positiveT_eq_candidateT_complex.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end positiveT_eq_candidateT_complex

namespace allSignsT_eq_candidateT_complex
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (e f : Bool) {u v z : ℂ}
      (_hu : ‖u‖ + ‖z‖ < 1) (_hv : ‖v‖ + ‖z‖ < 1),
    R.readout () () (kernelMode true e f u v z)
      (OriginalGaussianExternalSignedCandidate.candidateT e f u v (z ^ 2))
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh false false (u := 0) (v := 0) (z := 0) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@allSignsT_eq_candidateT_complex)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@allSignsT_eq_candidateT_complex, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@allSignsT_eq_candidateT_complex) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications.allSignsT_eq_candidateT_complex.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications.allSignsT_eq_candidateT_complex.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications
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
end allSignsT_eq_candidateT_complex

namespace allSignsJT_eq_candidates_complex
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (e f : Bool) {u v z : ℂ}
      (_hu : ‖u‖ + ‖z‖ < 1) (_hv : ‖v‖ + ‖z‖ < 1),
    R.readout () () (kernelMode false e f u v z)
      (OriginalGaussianExternalSignedCandidate.candidateJ e f u v (z ^ 2)) ∧
    kernelMode true e f u v z =
      OriginalGaussianExternalSignedCandidate.candidateT e f u v (z ^ 2)
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact (hh false false (u := 0) (v := 0) (z := 0) (by norm_num) (by norm_num)).1
def family : Registration arena (type_of% (@allSignsJT_eq_candidates_complex)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@allSignsJT_eq_candidates_complex, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@allSignsJT_eq_candidates_complex) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications.allSignsJT_eq_candidates_complex.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications.allSignsJT_eq_candidates_complex.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end allSignsJT_eq_candidates_complex

namespace allSignsJT_eq_candidates_complex_T
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (e f : Bool) {u v z : ℂ}
      (_hu : ‖u‖ + ‖z‖ < 1) (_hv : ‖v‖ + ‖z‖ < 1),
    kernelMode false e f u v z =
      OriginalGaussianExternalSignedCandidate.candidateJ e f u v (z ^ 2) ∧
    R.readout () () (kernelMode true e f u v z)
      (OriginalGaussianExternalSignedCandidate.candidateT e f u v (z ^ 2))
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact (hh false false (u := 0) (v := 0) (z := 0) (by norm_num) (by norm_num)).2
def family : Registration arena (type_of% (@allSignsJT_eq_candidates_complex)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@allSignsJT_eq_candidates_complex, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@allSignsJT_eq_candidates_complex) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications.allSignsJT_eq_candidates_complex_T.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications.allSignsJT_eq_candidates_complex_T.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end allSignsJT_eq_candidates_complex_T

end Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications
