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
open OriginalGaussianExternalRadial
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadial
local notation:50 a:51 " ≋[" R "] " b:51 => Realization.readout R () _ a b
local notation:50 a:51 " ≼[" R "] " b:51 => Realization.readout R () () a b

abbrev realVectorSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℝ × H)
    (fun _ => ℝ → H) (fun _ => Prop)
def realVectorActual : Realization realVectorSignature :=
  realize _ (fun _ a f => HasDerivAt f a.2 a.1) (fun e => nomatch e)
def realVectorRejected : Realization realVectorSignature :=
  realize _ (fun _ _ _ => False) (fun e => nomatch e)
def realVectorObserve (R : Realization realVectorSignature)
    (f : ℝ → H) (d : H) (x : ℝ) : Prop := R.readout () (x,d) f
private theorem realVectorDependence : ObservationalDependence realVectorSignature realVectorActual := by
  intro i
  let b : H := basis 0
  refine ⟨(0,0), (fun _ => 0), (fun x => x • b), ?_⟩
  intro h
  have hf : HasDerivAt (fun x : ℝ => x • b) 0 0 := Eq.mp h (hasDerivAt_const _ _)
  have hg : HasDerivAt (fun x : ℝ => x • b) b 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const b
  have he := hf.unique hg
  have hh := congrArg (fun v : H => v 0) he; simp [b, basis] at hh

abbrev complexVectorSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℂ × H)
    (fun _ => ℂ → H) (fun _ => Prop)
def complexVectorActual : Realization complexVectorSignature :=
  realize _ (fun _ a f => HasDerivAt f a.2 a.1) (fun e => nomatch e)
def complexVectorRejected : Realization complexVectorSignature :=
  realize _ (fun _ _ _ => False) (fun e => nomatch e)
def complexVectorObserve (R : Realization complexVectorSignature)
    (f : ℂ → H) (d : H) (x : ℂ) : Prop := R.readout () (x,d) f
private theorem complexVectorDependence : ObservationalDependence complexVectorSignature complexVectorActual := by
  intro i
  let b : H := basis 0
  refine ⟨(0,0), (fun _ => 0), (fun x => x • b), ?_⟩
  intro h
  have hf : HasDerivAt (fun x : ℂ => x • b) 0 0 := Eq.mp h (hasDerivAt_const _ _)
  have hg : HasDerivAt (fun x : ℂ => x • b) b 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const b
  have he := hf.unique hg
  have hh := congrArg (fun v : H => v 0) he; simp [b, basis] at hh

namespace hasDerivAt_externalVector
abbrev arena : Arena where
  signature := complexVectorSignature
  Law R := ∀ (out : Bool) (p : ℕ) {z : ℂ} (hz : ‖z‖ < 1),
    complexVectorObserve R (externalVector out p) (externalDerivative out p z) z
private theorem rejected_fails : ¬ arena.Law complexVectorRejected := by
  intro h
  exact h false 0 (z := 0) (by norm_num)
def family : Registration arena (type_of% (@hasDerivAt_externalVector)) where
  actual := complexVectorActual
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_externalVector, complexVectorRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨complexVectorRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := complexVectorDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_externalVector) (Realization complexVectorSignature) (ℂ × H) Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadial.hasDerivAt_externalVector.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadial.hasDerivAt_externalVector.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexVectorSignature complexVectorActual.readout complexVectorActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadial
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end hasDerivAt_externalVector


namespace hasDerivAt_radial_externalVector
abbrev arena : Arena where
  signature := realVectorSignature
  Law R := ∀ (out : Bool) (p : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1),
    realVectorObserve R (fun u : ℝ => externalVector out p (Real.sqrt u : ℂ))
      ((1 / (2 * (r : ℂ))) • frequencyVector out p (Real.sqrt r : ℂ)) r
private theorem rejected_fails : ¬ arena.Law realVectorRejected := by
  intro h
  exact h false 0 (r := 1/2) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@hasDerivAt_radial_externalVector)) where
  actual := realVectorActual
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_radial_externalVector, realVectorRejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨realVectorRejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := realVectorDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_radial_externalVector) (Realization realVectorSignature) (ℝ × H) Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadial.hasDerivAt_radial_externalVector.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadial.hasDerivAt_radial_externalVector.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realVectorSignature realVectorActual.readout realVectorActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadial
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end hasDerivAt_radial_externalVector

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadial
