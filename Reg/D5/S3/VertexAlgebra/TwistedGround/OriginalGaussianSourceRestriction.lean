import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction

set_option maxHeartbeats 1000000
noncomputable section
universe u
open scoped BigOperators Topology Matrix
open Filter Metric
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open TwistedGround OriginalChargedRowSource OriginalGaussianExternalBlocks
open OriginalGaussianSourceMeans OriginalGaussianSourceGerm
open NativeAffineTransport OriginalSourceInverseCoefficient
open OriginalNormalRowSource OriginalCorrectedRowRecompositionSource
open OriginalAffineRecompositionSource OriginalFourMChargeCoset
open LatticeHalfFockChargedCoefficients LatticeHalfFockChargedTensorCoefficients
open SignedOscillatorWick SourceBPZ.OriginalSourceCoevaluation MvPolynomial
open FactorialFockMetric (weight)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open OriginalGaussianSourceRestriction

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction

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

namespace original_right_covariance_restrict
def arena : Arena where
  signature := eqSignature
  Law A := ∀ {X : Type u} [Fintype X] [DecidableEq X] (D : LatticeData) (N M : ℕ) (h : N ≤ M)
    (e : X → External D) (i j : Internal D N ⊕ X),
    A.readout () () (transportCovariance (sourceBlock (J := X) (inverseSubstitution D M))
      (originalRow D M e)
      ((internalInclusion D N M h).sumMap (Function.Embedding.refl X) i)
      ((internalInclusion D N M h).sumMap (Function.Embedding.refl X) j))
      (transportCovariance (sourceBlock (J := X) (inverseSubstitution D N))
      (originalRow D N e) i j)
private theorem bad_fails : ¬ arena.{u}.Law eqBad := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance hyperbolic 0 0 le_rfl (fun _ => labels ()) (.inr (ULift.up ())) (.inr (ULift.up ()))
def evidence : Registration arena.{u} (type_of% (@original_right_covariance_restrict.{u})) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨fun {X} _ _ D N M h e i j => original_right_covariance_restrict D N M h e i j, eqBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law eqActual eqBad bad_fails
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_right_covariance_restrict.{u}) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction.original_right_covariance_restrict.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction.original_right_covariance_restrict.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_right_covariance_restrict

namespace original_right_mean_restrict
def arena : Arena where
  signature := eqSignature
  Law A := ∀ {X : Type u} [Fintype X] [DecidableEq X] (D : LatticeData) (a : Charge D)
    (N M : ℕ) (h : N ≤ M) (e : X → External D) (i : Internal D N ⊕ X),
    A.readout () () (originalInverseMean D a M e
      ((internalInclusion D N M h).sumMap (Function.Embedding.refl X) i))
      (originalInverseMean D a N e i)
private theorem bad_fails : ¬ arena.{u}.Law eqBad := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance hyperbolic 0 0 0 le_rfl (fun _ => labels ()) (.inr (ULift.up ()))
def evidence : Registration arena.{u} (type_of% (@original_right_mean_restrict.{u})) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨fun {X} _ _ D a N M h e i => original_right_mean_restrict D a N M h e i, eqBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law eqActual eqBad bad_fails
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_right_mean_restrict.{u}) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction.original_right_mean_restrict.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction.original_right_mean_restrict.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eqSignature eqActual.readout eqActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end original_right_mean_restrict

namespace original_fixed_energy_common_box
def arena : Arena where
  signature := eqSignature
  Law A := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (betaL gammaL betaR gammaR : Exponent D) (eL eR : ℤ)
    (n M : ℕ) (hn : n < M)
    (hbL : ∀ b ∈ betaL.support, b.2 < M) (hgL : ∀ b ∈ gammaL.support, b.2 < M)
    (hbR : ∀ b ∈ betaR.support, b.2 < M) (hgR : ∀ b ∈ gammaR.support, b.2 < M),
    A.readout () () ((∑ᶠ alpha : Exponent D, if oscillatorEnergy alpha = n then
      chargeScalar D a * chargeScalar D (-a) *
        wick D (monomial gammaL 1) (oscillatorCorrected D hu a eL
          (monomial alpha 1) (monomial betaL 1)) *
        wick D (monomial gammaR 1) (oscillatorCorrected D hu (-a) eR
          (dualOscillatorMonomial D alpha) (monomial betaR 1)) else 0)) (let A := correctedMatrix D (boxLabel D M)
    let U := sourceBlock (J := Internal D M ⊕ Internal D M) (inverseSubstitution D M)
    chargeScalar D a * chargeScalar D (-a) *
      (weight betaL : ℂ) * (weight gammaL : ℂ) *
      (weight betaR : ℂ) * (weight gammaR : ℂ) *
      (if eL + chargeNorm D a = -2 * (n : ℤ) -
        Finsupp.weight (fun b => (omega D b : ℤ)) betaL +
        Finsupp.weight (fun b => (omega D b : ℤ)) gammaL then (1 : ℂ) else 0) *
      (if eR + chargeNorm D (-a) = -2 * (n : ℤ) -
        Finsupp.weight (fun b => (omega D b : ℤ)) betaR +
        Finsupp.weight (fun b => (omega D b : ℤ)) gammaR then (1 : ℂ) else 0) *
      ∑ᶠ d : {d : Internal D M →₀ ℕ // internalEnergy D M d = n},
        (weight d.val : ℂ) *
          OriginalChargedRowSource.affineCoefficient A
            (correctedMean D a (boxLabel D M))
            (threeOccupation d.val (boxOccupation D M betaL) (boxOccupation D M gammaL)) *
          OriginalChargedRowSource.affineCoefficient (transportCovariance U A)
            (transportMean U (correctedMean D (-a) (boxLabel D M)))
            (threeOccupation d.val (boxOccupation D M betaR) (boxOccupation D M gammaR)))
private theorem bad_fails : ¬ arena.Law eqBad := by
  intro h
  exact h hyperbolic hyperbolic_unit 0 0 0 0 0 0 0 0 1 (by norm_num) (by simp) (by simp) (by simp) (by simp)
def evidence : Registration arena (type_of% (@original_fixed_energy_common_box)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨fun D hu a betaL gammaL betaR gammaR eL eR n M hn hbL hgL hbR hgR => original_fixed_energy_common_box D hu a betaL gammaL betaR gammaR eL eR n M hn hbL hgL hbR hgR, eqBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law eqActual eqBad bad_fails
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_fixed_energy_common_box) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction.original_fixed_energy_common_box.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction.original_fixed_energy_common_box.evidence
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
end original_fixed_energy_common_box

namespace original_fixed_energy_compact
def arena : Arena where
  signature := eqSignature
  Law O := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (betaL gammaL betaR gammaR : Exponent D) (eL eR : ℤ)
    (n M : ℕ) (hn : n < M)
    (hF : ∀ b ∈ fourSupport D betaL gammaL betaR gammaR, b.2 < M),
    O.readout () () ((∑ᶠ alpha : Exponent D, if oscillatorEnergy alpha = n then
      chargeScalar D a * chargeScalar D (-a) *
        wick D (monomial gammaL 1) (oscillatorCorrected D hu a eL
          (monomial alpha 1) (monomial betaL 1)) *
        wick D (monomial gammaR 1) (oscillatorCorrected D hu (-a) eR
          (dualOscillatorMonomial D alpha) (monomial betaR 1)) else 0)) (let F := fourSupport D betaL gammaL betaR gammaR
    let e := compactExternal D F
    let h := (restricted D F betaL).sumElim (restricted D F gammaL)
    let k := (restricted D F betaR).sumElim (restricted D F gammaR)
    chargeScalar D a * chargeScalar D (-a) *
      (weight betaL : ℂ) * (weight gammaL : ℂ) *
      (weight betaR : ℂ) * (weight gammaR : ℂ) *
      (if eL + chargeNorm D a = -2 * (n : ℤ) -
        Finsupp.weight (fun b => (omega D b : ℤ)) betaL +
        Finsupp.weight (fun b => (omega D b : ℤ)) gammaL then (1 : ℂ) else 0) *
      (if eR + chargeNorm D (-a) = -2 * (n : ℤ) -
        Finsupp.weight (fun b => (omega D b : ℤ)) betaR +
        Finsupp.weight (fun b => (omega D b : ℤ)) gammaR then (1 : ℂ) else 0) *
      ∑ᶠ d : {d : Internal D M →₀ ℕ // internalEnergy D M d = n},
        (weight d.val : ℂ) *
          OriginalChargedRowSource.affineCoefficient (originalRow D M e)
            (originalMean D a M e) (d.val.sumElim h) *
          OriginalChargedRowSource.affineCoefficient
            (transportCovariance (sourceBlock (J := CompactExternal D F) (inverseSubstitution D M))
              (originalRow D M e))
            (originalInverseMean D a M e) (d.val.sumElim k))
private theorem bad_fails : ¬ arena.Law eqBad := by
  intro h
  exact h hyperbolic hyperbolic_unit 0 0 0 0 0 0 0 0 1 (by decide)
    (by simp [fourSupport])
def evidence : Registration arena (type_of% (@original_fixed_energy_compact)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨fun D hu a betaL gammaL betaR gammaR eL eR n M hn hF =>
    original_fixed_energy_compact D hu a betaL gammaL betaR gammaR eL eR n M hn hF, eqBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law eqActual eqBad bad_fails
  dependence := eqDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_fixed_energy_compact) (Realization eqSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction.original_fixed_energy_compact.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction.original_fixed_energy_compact.evidence
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
end original_fixed_energy_compact

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction
