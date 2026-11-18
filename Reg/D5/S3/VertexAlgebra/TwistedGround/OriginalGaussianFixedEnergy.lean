import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFixedEnergy

noncomputable section
open scoped BigOperators Topology Matrix
open Filter Metric
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open TwistedGround OriginalChargedRowSource OriginalGaussianExternalBlocks
open OriginalGaussianSourceMeans OriginalGaussianSourceGerm OriginalGaussianSewnAnalytic
open NativeAffineTransport OriginalSourceInverseCoefficient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open OriginalGaussianOccupationCoefficients
open NativeAffineExternalCoefficient OriginalGaussianFixedExternalCoefficient
open OriginalGaussianSourceRestriction FactorialFockMetric
open MvPolynomial
open LatticeInvolution SignedOscillatorWick LatticeAllStateField
open SourceBPZ.OriginalSourceCoevaluation
open OriginalNormalRowSource OriginalCorrectedRowRecompositionSource
open OriginalAffineRecompositionSource OriginalFourMChargeCoset
open LatticeHalfFockChargedCoefficients LatticeHalfFockChargedTensorCoefficients

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFixedEnergy

private abbrev hyperbolic : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  even_diagonal := by intro i; fin_cases i <;> exact ⟨0, rfl⟩
private theorem hyperbolic_unit : IsUnit hyperbolic.G.det := by
  have h : hyperbolic.G.det = -1 := by decide
  rw [h]
  exact isUnit_neg_one
private def labels : Unit → External hyperbolic := fun _ => (false, (0, 0))

abbrev eqSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)
def eqActual : Realization eqSignature := realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def eqBad : Realization eqSignature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem eqDependence : ObservationalDependence eqSignature eqActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : (1 : ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero he

open OriginalGaussianFixedEnergy

namespace original_fixed_energy_coefficient
def arena : Arena where
  signature := eqSignature
  Law O := ∀  (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (betaL gammaL betaR gammaR : Exponent D) (eL eR : ℤ) (n : ℕ),
    O.readout () () ((∑ᶠ alpha : Exponent D, if oscillatorEnergy alpha = n then
      chargeScalar D a * chargeScalar D (-a) *
        wick D (monomial gammaL 1) (oscillatorCorrected D hu a eL
          (monomial alpha 1) (monomial betaL 1)) *
        wick D (monomial gammaR 1) (oscillatorCorrected D hu (-a) eR
          (dualOscillatorMonomial D alpha) (monomial betaR 1)) else 0)) (let F := fourSupport D betaL gammaL betaR gammaR
    chargeScalar D a * chargeScalar D (-a) *
      (weight betaL : ℂ) * (weight gammaL : ℂ) *
      (weight betaR : ℂ) * (weight gammaR : ℂ) *
      (if eL + chargeNorm D a = -2 * (n : ℤ) -
        Finsupp.weight (fun b => (omega D b : ℤ)) betaL +
        Finsupp.weight (fun b => (omega D b : ℤ)) gammaL then (1 : ℂ) else 0) *
      (if eR + chargeNorm D (-a) = -2 * (n : ℤ) -
        Finsupp.weight (fun b => (omega D b : ℤ)) betaR +
        Finsupp.weight (fun b => (omega D b : ℤ)) gammaR then (1 : ℂ) else 0) *
      coefficient (2 * n) (sewn D a (compactExternal D F)
        (externalOccupation D F betaL gammaL betaR gammaR)))
private theorem bad_fails : ¬ arena.Law eqBad := by
  intro h
  exact h hyperbolic hyperbolic_unit 0 0 0 0 0 0 0 0
def evidence : Registration arena (type_of% (@original_fixed_energy_coefficient)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨fun D hu a betaL gammaL betaR gammaR eL eR n => original_fixed_energy_coefficient D hu a betaL gammaL betaR gammaR eL eR n, eqBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law eqActual eqBad bad_fails
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_fixed_energy_coefficient) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFixedEnergy.original_fixed_energy_coefficient.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFixedEnergy.original_fixed_energy_coefficient.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_fixed_energy_coefficient

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFixedEnergy
