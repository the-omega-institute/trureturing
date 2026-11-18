import Reg.Support.FactorialFockMetric
import Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate
noncomputable section
open scoped Topology
open _root_.D5.S3.VertexAlgebra.TwistedGround
open OriginalGaussianExternalGenerators OriginalGaussianExternalGeneratedSource
open OriginalGaussianExternalAnalyticCandidate
open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate

namespace candidateT_differential
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {u v r : ℂ} (_hu : ‖u‖ + ‖r‖ < 1) (_hv : ‖v‖ + ‖r‖ < 1)
    (_he : E u v r ≠ 0),
    let lam := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative r 0 / period r
    R.readout () _
      (L (fun w => candidateT w v r) u - L (fun w => candidateT u w r) v)
      ((1-r)*sourceMode true u r*sourceMode true v r*
        (modeA true u r*modeH true v r lam-modeH true u r lam*modeA true v r)/2) ∧
    R.readout () _
      (2*r*deriv (fun w => candidateT u v w) r-
        L (fun w => candidateT w v r) u-L (fun w => candidateT u w r) v)
      ((1-r)*sourceMode true u r*sourceMode true v r*
        (modeH true u r lam*modeH true v r lam-modeA true u r*modeA true v r)/2)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact (@h 0 0 0 (by norm_num) (by norm_num) (by norm_num [E])).1
def family : Registration arena (type_of% (@candidateT_differential)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@candidateT_differential, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@candidateT_differential) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate.candidateT_differential.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate.candidateT_differential.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false },
    {
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end candidateT_differential

namespace candidateJ_regular
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {u v r : ℂ} (_hu : ‖u‖ + ‖r‖ < 1) (_hv : ‖v‖ + ‖r‖ < 1),
    DifferentiableAt ℂ (fun w => candidateJ w v r) u ∧
    DifferentiableAt ℂ (fun w => candidateJ u w r) v ∧
    (u-v ≠ 0 → R.readout () _ (candidateJ u v r)
      (sourceMode true u r*sourceMode true v r*(rationalJ u v r-correction r)-cauchy u v))
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact (@h 0 (1/4) 0 (by norm_num) (by norm_num)).2.2 (by norm_num)
def family : Registration arena (type_of% (@candidateJ_regular)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@candidateJ_regular, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@candidateJ_regular) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate.candidateJ_regular.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate.candidateJ_regular.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end candidateJ_regular

namespace candidateJ_differential
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {u v r : ℂ} (_hu : ‖u‖ + ‖r‖ < 1) (_hv : ‖v‖ + ‖r‖ < 1),
    let lam := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative r 0 / period r
    R.readout () _
      (L (fun w => candidateJ w v r) u + L (fun w => candidateJ u w r) v)
      ((1-r)*sourceMode true u r*sourceMode true v r*
        (modeA true u r*modeH true v r lam+modeH true u r lam*modeA true v r)/2+1/4)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact @h 0 (1/4) 0 (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@candidateJ_differential)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@candidateJ_differential, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@candidateJ_differential) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate.candidateJ_differential.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate.candidateJ_differential.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end candidateJ_differential

namespace candidateT_original_differential
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {u v : ℂ} {r : ℝ} (_hr : 0 ≤ r) (_hr1 : r < 1)
    (_hu : ‖u‖ + Real.sqrt r < 1) (_hv : ‖v‖ + Real.sqrt r < 1),
    let x : ℂ := r
    let lam := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative x 0 / period x
    R.readout () _
      (L (fun w => candidateT w v x) u - L (fun w => candidateT u w x) v)
      ((1-x)*sourceMode true u x*sourceMode true v x*
        (modeA true u x*modeH true v x lam-modeH true u x lam*modeA true v x)/2) ∧
    R.readout () _
      (2*x*deriv (fun t : ℝ => candidateT u v (t : ℂ)) r-
        L (fun w => candidateT w v x) u-L (fun w => candidateT u w x) v)
      ((1-x)*sourceMode true u x*sourceMode true v x*
        (modeH true u x lam*modeH true v x lam-modeA true u x*modeA true v x)/2)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact (@h 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
def family : Registration arena (type_of% (@candidateT_original_differential)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@candidateT_original_differential, eqRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨eqRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@candidateT_original_differential) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate.candidateT_original_differential.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate.candidateT_original_differential.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false },
    {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end candidateT_original_differential

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
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate.positiveJ_eq_candidateJ.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate.positiveJ_eq_candidateJ.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate
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

abbrev correctionDerivativeSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℂ × ℂ)
    (fun _ => ℂ → ℂ) (fun _ => Prop)
def correctionDerivativeActual : Realization correctionDerivativeSignature :=
  realize _ (fun _ a f => HasDerivAt f a.2 a.1) (fun e => nomatch e)
def correctionDerivativeBad : Realization correctionDerivativeSignature :=
  realize _ (fun _ _ _ => False) (fun e => nomatch e)
private theorem correctionDerivativeDependence :
    ObservationalDependence correctionDerivativeSignature correctionDerivativeActual := by
  intro i
  refine ⟨(0,0), (fun _ => 0), (fun z => z), ?_⟩
  intro h
  have hf : HasDerivAt (fun z : ℂ => z) 0 0 := Eq.mp h (hasDerivAt_const _ _)
  have hg : HasDerivAt (fun z : ℂ => z) 1 0 := hasDerivAt_id 0
  exact zero_ne_one (hf.unique hg)

namespace correction_hasDerivAt
abbrev arena : Arena where
  signature := correctionDerivativeSignature
  Law R := ∀ {r : ℂ} (_hr : ‖r‖ < 1),
    R.readout () (r, 1 / 4 - r * (1 - r) * ell r ^ 2) correction
private theorem rejected_fails : ¬ arena.Law correctionDerivativeBad := by
  intro h
  exact h (r := 0) (by norm_num)
def family : Registration arena (type_of% (@correction_hasDerivAt)) where
  actual := correctionDerivativeActual
  bridge := Iff.rfl
  variation := ⟨@correction_hasDerivAt, correctionDerivativeBad, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law correctionDerivativeActual correctionDerivativeBad rejected_fails
  dependence := correctionDerivativeDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@correction_hasDerivAt) (Realization correctionDerivativeSignature) ℂ Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate.correction_hasDerivAt.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate.correction_hasDerivAt.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize correctionDerivativeSignature correctionDerivativeActual.readout correctionDerivativeActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false } ] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end correction_hasDerivAt

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate
