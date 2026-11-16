import Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators
noncomputable section
open scoped BigOperators Topology ENNReal
open _root_.D5.S3.VertexAlgebra.TwistedGround
open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianDifferentiation
open OriginalGaussianWeightedResolvent
open OriginalGaussianAllIndexResolvent OriginalGaussianExternalResolvent
open OriginalGaussianSourceMeans OriginalGaussianSourceEvaluation
open OriginalGaussianExternalFrequency OriginalGaussianExternalDisplacement
open OriginalGaussianExternalMoments OriginalGaussianExternalRadial
open OriginalGaussianExternalEvolution OriginalGaussianExternalSourceJet
open OriginalGaussianExternalNormal OriginalGaussianExternalGenerators
open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianBilinearTranspose
open OriginalGaussianExternalEvolution
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEvolution
local notation:50 a:51 " ≋[" R "] " b:51 => Realization.readout R () _ a b
local notation:50 a:51 " ≼[" R "] " b:51 => Realization.readout R () () a b

abbrev realComplexSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℝ × ℂ)
    (fun _ => ℝ → ℂ) (fun _ => Prop)
def realComplexActual : Realization realComplexSignature :=
  realize _ (fun _ a f => HasDerivAt f a.2 a.1) (fun e => nomatch e)
def realComplexRejected : Realization realComplexSignature :=
  realize _ (fun _ _ _ => False) (fun e => nomatch e)
def realComplexObserve (R : Realization realComplexSignature)
    (f : ℝ → ℂ) (d : ℂ) (x : ℝ) : Prop := R.readout () (x,d) f
private theorem realComplexDependence : ObservationalDependence realComplexSignature realComplexActual := by
  intro i
  let b : ℂ := 1
  refine ⟨(0,0), (fun _ => 0), (fun x => x • b), ?_⟩
  intro h
  have hf : HasDerivAt (fun x : ℝ => x • b) 0 0 := Eq.mp h (hasDerivAt_const _ _)
  have hg : HasDerivAt (fun x : ℝ => x • b) b 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const b
  have he := hf.unique hg
  exact zero_ne_one he

namespace externalT_radial_equation
abbrev arena : Arena where
  signature := realComplexSignature
  Law R := ∀ (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1),
    realComplexObserve R (fun u : ℝ => externalT out p out' q (Real.sqrt u : ℂ))
      ((modeFrequency out p (fun e k => externalT e k out' q (Real.sqrt r : ℂ)) +
        modeFrequency out' q (fun e k => externalT out p e k (Real.sqrt r : ℂ)) +
        (1 - (r : ℂ)) / 2 *
          (sourceJetMoment out p r * sourceJetMoment out' q r -
            sourceMoment out p r * sourceMoment out' q r)) / (2 * (r : ℂ))) r
private theorem rejected_fails : ¬ arena.Law realComplexRejected := by
  intro h
  exact h false 0 false 0 (r := 1/2) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@externalT_radial_equation)) where
  actual := realComplexActual
  bridge := Iff.rfl
  variation := ⟨@externalT_radial_equation, realComplexRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨realComplexRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := realComplexDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@externalT_radial_equation) (Realization realComplexSignature) (ℝ × ℂ) Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEvolution.externalT_radial_equation.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEvolution.externalT_radial_equation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realComplexSignature realComplexActual.readout realComplexActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEvolution
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end externalT_radial_equation


namespace external_negative_zero_boundary
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (out : Bool) (p : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1),
    externalJ false 0 out p (Real.sqrt r : ℂ) ≋[R]       (Real.sqrt (1 - r) : ℂ) *
        (sourceJetMoment out p r - sourceMoment out p r) / 2 ∧
    externalT false 0 out p (Real.sqrt r : ℂ) =
      (Real.sqrt (1 - r) : ℂ) *
        (sourceJetMoment out p r + sourceMoment out p r) / 2
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact (h false 0 (r := 1/2) (by norm_num) (by norm_num)).1
def family : Registration arena (type_of% (@external_negative_zero_boundary)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@external_negative_zero_boundary, eqRejected, rejected_fails⟩
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
    (@external_negative_zero_boundary) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEvolution.external_negative_zero_boundary.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEvolution.external_negative_zero_boundary.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEvolution
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
end external_negative_zero_boundary


namespace square_half
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {z : ℂ} (hz : ‖z‖ < 1),
    R.readout () _ (squareResolvent z) ((1 / 2 : ℂ) • (resolvent z + oppositeResolvent z))
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h (z := 0) (by simp)
def family : Registration arena (type_of% (@square_half)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@square_half, eqRejected, rejected_fails⟩
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
    (@square_half) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEvolution.square_half.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEvolution.square_half.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEvolution
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
end square_half

namespace opposite_bilinear_transpose
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ {z : ℂ} (hz : ‖z‖ < 1) (x y : H),
    R.readout () _ (sourceBilinearFunctional x (oppositeResolvent z y)) (sourceBilinearFunctional (oppositeResolvent z x) y)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h (z := 0) (by simp) (0 : H) (0 : H)
def family : Registration arena (type_of% (@opposite_bilinear_transpose)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@opposite_bilinear_transpose, eqRejected, rejected_fails⟩
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
    (@opposite_bilinear_transpose) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEvolution.opposite_bilinear_transpose.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEvolution.opposite_bilinear_transpose.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEvolution
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
end opposite_bilinear_transpose
end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEvolution
