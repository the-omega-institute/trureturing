import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.PositiveT.GeneratorIdentification

/-! The actual positive-T series predicate and generated-kernel equality. -/

noncomputable section
open _root_.D5.S3.VertexAlgebra.TwistedGround
open PositiveT.GeneratorIdentification
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.PositiveT.GeneratorIdentification

abbrev pairSeriesSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => (ℕ × ℕ) → ℂ) (fun _ => ℂ → SummationFilter (ℕ × ℕ) → Prop)
def pairSeriesActual : Realization pairSeriesSignature :=
  realize _ (fun _ _ f a L => HasSum f a L) (fun e => nomatch e)
def pairSeriesRejected : Realization pairSeriesSignature :=
  realize _ (fun _ _ _ _ _ => False) (fun e => nomatch e)
private theorem pairSeriesDependence : ObservationalDependence pairSeriesSignature pairSeriesActual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro hh
  have hh' : HasSum (fun _ : ℕ × ℕ => (0 : ℂ)) 0 =
      HasSum (fun _ : ℕ × ℕ => (1 : ℂ)) 0 :=
    congrFun (congrFun hh 0) (SummationFilter.unconditional (ℕ × ℕ))
  have hf : HasSum (fun _ : ℕ × ℕ => (1 : ℂ)) 0 := Eq.mp hh' hasSum_zero
  have he : (1 : ℂ) = 0 := by simpa only [summable_const_iff] using hf.summable
  exact one_ne_zero he

namespace positiveT_hasSum
abbrev arena : Arena where
  signature := pairSeriesSignature
  Law R := ∀ {r : ℝ} {u v : ℂ} (_hr : 0 < r) (_hr1 : r < 1)
      (_hu : ‖u‖ + Real.sqrt r < 1) (_hv : ‖v‖ + Real.sqrt r < 1),
    R.readout () ()
      (fun pq : ℕ × ℕ => OriginalGaussianFiniteCandidateModes.t pq.1 pq.2 (r : ℂ) *
        u ^ pq.1 * v ^ pq.2)
      (OriginalGaussianExternalAnalyticCandidate.candidateT u v (r : ℂ))
      (SummationFilter.unconditional (ℕ × ℕ))

private theorem rejected_fails : ¬ arena.Law pairSeriesRejected := by
  intro hh
  exact hh (u := 0) (v := 0) (r := 1/4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

def family : Registration arena (type_of% (@positiveT_hasSum)) where
  actual := pairSeriesActual
  bridge := Iff.rfl
  variation := ⟨@positiveT_hasSum, pairSeriesRejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law pairSeriesActual pairSeriesRejected rejected_fails
  dependence := pairSeriesDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positiveT_hasSum) (Realization pairSeriesSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.PositiveT.GeneratorIdentification.positiveT_hasSum.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.PositiveT.GeneratorIdentification.positiveT_hasSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairSeriesSignature pairSeriesActual.readout pairSeriesActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.PositiveT.GeneratorIdentification
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end positiveT_hasSum

namespace positiveT_eq_candidateT
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ {u v : ℂ} {r : ℝ} (_hr : 0 < r) (_hr1 : r < 1)
      (_hu : ‖u‖ + Real.sqrt r < 1) (_hv : ‖v‖ + Real.sqrt r < 1),
    R.readout () ()
      (OriginalGaussianExternalGeneratedSource.kernelMode true true true u v (Real.sqrt r : ℂ))
      (OriginalGaussianExternalAnalyticCandidate.candidateT u v (r : ℂ))

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh (u := 0) (v := 0) (r := 1/4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

def family : Registration arena (type_of% (@positiveT_eq_candidateT)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@positiveT_eq_candidateT, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positiveT_eq_candidateT) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.PositiveT.GeneratorIdentification.positiveT_eq_candidateT.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.PositiveT.GeneratorIdentification.positiveT_eq_candidateT.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.PositiveT.GeneratorIdentification
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
end positiveT_eq_candidateT

end Reg.D5.S3.VertexAlgebra.TwistedGround.PositiveT.GeneratorIdentification
