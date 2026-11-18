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
open OriginalGaussianExternalDisplacement
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalDisplacement
local notation:50 a:51 " ≋[" R "] " b:51 => Realization.readout R () _ a b
local notation:50 a:51 " ≼[" R "] " b:51 => Realization.readout R () () a b

namespace external_displacement
abbrev arena : Arena where
  signature := eqSignature
  Law R := ∀ (out : Bool) (p : ℕ) (out' : Bool) (q : ℕ)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1),
    let z : ℂ := Real.sqrt r
    let w := weightedSource r hr hr1
    let a := fun e k => sourceBilinearFunctional (externalVector e k z)
      (oppositeResolvent z w)
    let b := fun e k => sourceBilinearFunctional (externalVector e k z) (resolvent z w)
    (modeFrequency out p (fun e k => externalJ e k out' q z) +
      modeFrequency out' q (fun e k => externalJ out p e k z) ≋[R]         (a out p * b out' q + b out p * a out' q) / 2) ∧
    (modeFrequency out p (fun e k => externalT e k out' q z) -
      modeFrequency out' q (fun e k => externalT out p e k z) =
        (a out p * b out' q - b out p * a out' q) / 2)
private theorem rejected_fails : ¬ arena.Law eqRejected := by
  intro h
  exact (h false 0 false 0 (r := 0) (by norm_num) (by norm_num)).1
def family : Registration arena (type_of% (@external_displacement)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨@external_displacement, eqRejected, rejected_fails⟩
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
    (@external_displacement) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalDisplacement.external_displacement.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalDisplacement.external_displacement.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalDisplacement
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
end external_displacement

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalDisplacement
