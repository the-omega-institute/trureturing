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
open OriginalGaussianExternalSourceJet
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSourceJet
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

namespace hasDerivAt_radial_sourceExternal
abbrev arena : Arena where
  signature := realComplexSignature
  Law R := ∀ (out : Bool) (p : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1),
    realComplexObserve R (fun u : ℝ => sourceExternal out p (Real.sqrt u : ℂ))
      (-(sourceMoment out p r + sourceJetMoment out p r) /
        (2 * (r : ℂ) * period r)) r
private theorem rejected_fails : ¬ arena.Law realComplexRejected := by
  intro h
  exact h false 0 (r := 1/2) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@hasDerivAt_radial_sourceExternal)) where
  actual := realComplexActual
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_radial_sourceExternal, realComplexRejected, rejected_fails⟩
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
    (@hasDerivAt_radial_sourceExternal) (Realization realComplexSignature) (ℝ × ℂ) Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSourceJet.hasDerivAt_radial_sourceExternal.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSourceJet.hasDerivAt_radial_sourceExternal.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSourceJet
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
end hasDerivAt_radial_sourceExternal


namespace hasDerivAt_radial_sourceAmplitude
abbrev arena : Arena where
  signature := realComplexSignature
  Law R := ∀ (out : Bool) (p : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1),
    realComplexObserve R (fun u : ℝ => sourceAmplitude out p (u : ℂ))
      (shiftedCentralDerivative r 0 * sourceAmplitude out p r / period r +
        (sourceMoment out p r + sourceJetMoment out p r) / (2 * (r : ℂ))) r
private theorem rejected_fails : ¬ arena.Law realComplexRejected := by
  intro h
  exact h false 0 (r := 1/2) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@hasDerivAt_radial_sourceAmplitude)) where
  actual := realComplexActual
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_radial_sourceAmplitude, realComplexRejected, rejected_fails⟩
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
    (@hasDerivAt_radial_sourceAmplitude) (Realization realComplexSignature) (ℝ × ℂ) Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSourceJet.hasDerivAt_radial_sourceAmplitude.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSourceJet.hasDerivAt_radial_sourceAmplitude.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSourceJet
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
end hasDerivAt_radial_sourceAmplitude


namespace sourceJetMoment_eq_derivative
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (out : Bool) (p : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1),
    sourceJetMoment out p r ≋[R]       2 * (r : ℂ) * deriv (fun u : ℝ => sourceAmplitude out p (u : ℂ)) r -
        modeFrequency out p (fun e k => sourceAmplitude e k r) -
        2 * (r : ℂ) * sourceAmplitude out p r * shiftedCentralDerivative r 0 / period r
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact h false 0 (r := 1/2) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@sourceJetMoment_eq_derivative)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@sourceJetMoment_eq_derivative, eqRejected, rejected_fails⟩
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
    (@sourceJetMoment_eq_derivative) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSourceJet.sourceJetMoment_eq_derivative.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSourceJet.sourceJetMoment_eq_derivative.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSourceJet
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
end sourceJetMoment_eq_derivative


namespace external_source_equations
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1),
    let z : ℂ := Real.sqrt r
    let U := fun e k => modeFrequency e k (fun f l => sourceAmplitude f l (r : ℂ))
    let V := fun e k =>
      2 * (r : ℂ) * deriv (fun u : ℝ => sourceAmplitude e k (u : ℂ)) r - U e k -
        2 * (r : ℂ) * sourceAmplitude e k r * shiftedCentralDerivative r 0 / period r
    (modeFrequency out p (fun e k => externalJ e k out' q z) +
      modeFrequency out' q (fun e k => externalJ out p e k z) ≋[R]       (1 - (r : ℂ)) * (U out p * V out' q + V out p * U out' q) / 2) ∧
    (modeFrequency out p (fun e k => externalT e k out' q z) -
      modeFrequency out' q (fun e k => externalT out p e k z) =
      (1 - (r : ℂ)) * (U out p * V out' q - V out p * U out' q) / 2) ∧
    HasDerivAt (fun u : ℝ => externalT out p out' q (Real.sqrt u : ℂ))
      ((modeFrequency out p (fun e k => externalT e k out' q z) +
        modeFrequency out' q (fun e k => externalT out p e k z) +
        (1 - (r : ℂ)) / 2 * (V out p * V out' q - U out p * U out' q)) /
        (2 * (r : ℂ))) r
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact (h false 0 false 0 (r := 1/2) (by norm_num) (by norm_num)).1
def family : Registration arena (type_of% (@external_source_equations)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@external_source_equations, eqRejected, rejected_fails⟩
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
    (@external_source_equations) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSourceJet.external_source_equations.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSourceJet.external_source_equations.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSourceJet
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
end external_source_equations

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSourceJet
