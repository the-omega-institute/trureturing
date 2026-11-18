import D5.S3.VertexAlgebra.TwistedGround.OriginalSourceInverseCoefficient
import Reg.Support.FactorialFockMetric

set_option autoImplicit false
universe u v
noncomputable section
open scoped Matrix
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality OriginalCurrentMetric SignedOscillatorWick
open D5.S3.VertexAlgebra.TwistedGround.OriginalSourceInverseCoefficient
open D5.S3.VertexAlgebra.TwistedGround.NativeAffineTransport
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalSourceInverseCoefficient
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric

abbrev signature := complexSignature
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {D : LatticeData}
    (A : ℕ → Matrix (Fin D.rank) (Fin D.rank) ℂ) (p q : Oscillator D),
    r.readout () () (FactorialBilinear.form (Index D) (substitution A p) q)
      (FactorialBilinear.form (Index D) p (substitution (fun k => (A k)ᵀ) q))

theorem sourceBridge :
    (type_of% (@substitution_factorial_transpose)) ↔ arena.Law complexEqual := Iff.rfl

private theorem actualLaw : arena.Law complexEqual := @substitution_factorial_transpose

private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  let D : LatticeData := ⟨0, 0, by intros; rfl, by intro i; exact Fin.elim0 i⟩
  exact @h D (fun _ => 0) 0 0

def family : Registration arena (type_of% (@substitution_factorial_transpose)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, complexFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨complexFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@substitution_factorial_transpose) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalSourceInverseCoefficient.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalSourceInverseCoefficient.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalSourceInverseCoefficient
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



namespace OriginalInverseAffine
open _root_.D5.S3.VertexAlgebra.TwistedGround
open _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy
open _root_.D5.S3.VertexAlgebra.FactorialFockMetric (weight)
open MvPolynomial OriginalChargedRowSource
open LatticeHalfFock LatticeHalfFockChargedTensorCoefficients LatticeHalfFockChargedCoefficients
open OriginalFourMChargeCoset OriginalNormalRowSource OriginalCorrectedRowRecompositionSource
open SourceBPZ.OriginalSourceCoevaluation
open scoped BigOperators

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (alpha betaL gammaL betaR gammaR : Exponent D) (eL eR : ℤ)
    (n : ℕ) (ha : oscillatorEnergy alpha ≤ n),
    r.readout () () (chargeScalar D a * chargeScalar D (-a) *
      wick D (monomial gammaL 1)
        (oscillatorCorrected D hu a eL (monomial alpha 1) (monomial betaL 1)) *
      wick D (monomial gammaR 1)
        (oscillatorCorrected D hu (-a) eR
          (dualOscillatorMonomial D alpha) (monomial betaR 1))) (let K := rowSupport D alpha betaL gammaL
    let left := affineLaurent (correctedMatrix D (supportLabel D K))
      (correctedMean D a (supportLabel D K)) (normalWeight D (supportLabel D K))
      (threeOccupation (restricted D K alpha) (restricted D K betaL)
        (restricted D K gammaL)) (eL+chargeNorm D a)
    let M := n+1+betaR.support.sup Prod.snd+gammaR.support.sup Prod.snd
    let label := boxLabel D M
    let B := boxMatrix D M (fun k => (((-((k : ℂ)+1))⁻¹ • (gramComplex D)⁻¹))ᵀ)
    let U := sourceBlock (J := (Fin D.rank × Fin M) ⊕ (Fin D.rank × Fin M)) B
    chargeScalar D a * chargeScalar D (-a) *
      (weight alpha : ℂ)*(weight betaL : ℂ)*(weight gammaL : ℂ)*
      (weight betaR : ℂ)*(weight gammaR : ℂ)*left *
        affineLaurent (transportCovariance U (correctedMatrix D label))
          (transportMean U (correctedMean D (-a) label)) (normalWeight D label)
          (threeOccupation (boxOccupation D M alpha) (boxOccupation D M betaR)
            (boxOccupation D M gammaR)) (eR+chargeNorm D (-a)))

theorem sourceBridge : (type_of% (@original_two_rows_inverse_affine_coefficient)) ↔
    arena.Law complexEqual := Iff.rfl

private theorem actualLaw : arena.Law complexEqual := @original_two_rows_inverse_affine_coefficient

private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  let D : LatticeData := ⟨0, 0, by intros; rfl, by intro i; exact Fin.elim0 i⟩
  have hu : IsUnit D.G.det := by simp [D]
  exact h D hu 0 0 0 0 0 0 0 0 0 (by simp [LatticePositiveEnergy.oscillatorEnergy])

def family : Registration arena (type_of% (@original_two_rows_inverse_affine_coefficient)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨actualLaw, complexFalse, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨complexFalse, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_two_rows_inverse_affine_coefficient) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalSourceInverseCoefficient.OriginalInverseAffine.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalSourceInverseCoefficient.OriginalInverseAffine.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalSourceInverseCoefficient
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end OriginalInverseAffine

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalSourceInverseCoefficient
