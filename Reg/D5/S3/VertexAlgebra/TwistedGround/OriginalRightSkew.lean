import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.OriginalRightSkew
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators VertexOperator
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalRightSkew
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace LatticeAllStateField LatticePositiveEnergy LatticeInvolution
open _root_.D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
open LatticeSugawaraCurrents LatticeSugawaraVirasoro
open HalfFock.LatticeHalfFockParityField
open _root_.D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)

def arena : Arena where
  signature := complexSignature
  Law observed := ∀
    (D : LatticeData) (hu : IsUnit D.G.det) (h24 : D.rank = 24)
    (H : ℕ) (h s : ℤ) (a : FixedCarrier D) (ha : a.val ∈ grade D h)
    (u : paritySpace D hu (-1))
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (d : ActualTensor D hu),
    let E : ℤ := (H : ℤ)+h-s-1
    let C : Module.End ℂ (ActualTensor D hu) :=
      tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1
    let raw : ℕ → paritySpace D hu (-1) := fun ell =>
      (((fixedParitySlice D hu (-1) a)[[s+(ell : ℤ)]]) u)
    let term : ℕ → paritySpace D hu (-1) := fun ell =>
      ((-1 : ℂ)^(s+(ell : ℤ)+1) * (ell.factorial : ℂ)⁻¹) •
        (translation D hu ^ ell) (raw ell)
    let R := originalRightCoefficient D hu s u a
    Set.Finite (Function.support term) ∧
    (E < 2 → (∀ ell : ℕ, raw ell = 0) ∧ R = 0) ∧
    (2 ≤ E →
      (∀ ell : ℕ, (E-1).toNat ≤ ell → raw ell = 0) ∧
      R = (∑ ell ∈ Finset.range (E-1).toNat, term ell) ∧
      actualTensorL0 D hu R.val = (E : ℂ) • R.val ∧
      (observed.readout () () (actualForm D hu d R.val)
        (∑ ell ∈ Finset.range (E-1).toNat,
          ((-1 : ℂ)^(s+(ell : ℤ)+1) * (ell.factorial : ℂ)⁻¹) *
            actualForm D hu ((C ^ ell) d) (raw ell).val)) ∧
      (∀ (m r : ℤ) (j : ℕ), s = m+r-(j : ℤ) →
        ((-1 : ℂ)^(j : ℤ) * Ring.choose (r : ℂ) j) * actualForm D hu d R.val =
          ∑ ell ∈ Finset.range (E-1).toNat,
            Ring.choose (r : ℂ) j * (-1 : ℂ)^(m+r+(ell : ℤ)+1) *
              (ell.factorial : ℂ)⁻¹ * actualForm D hu ((C ^ ell) d) (raw ell).val) ∧
      (∀ (n r : ℤ) (j : ℕ), s = n+r-(j : ℤ) →
        ((-1 : ℂ)^((j : ℤ)+r) * Ring.choose (r : ℂ) j) * actualForm D hu d R.val =
          ∑ ell ∈ Finset.range (E-1).toNat,
            Ring.choose (r : ℂ) j * (-1 : ℂ)^(n+(ell : ℤ)+1) *
              (ell.factorial : ℂ)⁻¹ * actualForm D hu ((C ^ ell) d) (raw ell).val))

theorem sourceBridge : (type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.original_right_skew_finite)) ↔ arena.Law complexEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro law
  obtain ⟨D, e, h24, hu, hpos, hpair⟩ :=
    _root_.D5.S3.Arith.Lattices.Golay.RealLeech.exists_positive_even_unimodular_gram
  exact ((law D hu h24 2 0 (-1) 0 (by simp) 0 (by simp) 0).2.2 (by norm_num)).2.2.2.1

def family : Registration arena (type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.original_right_skew_finite)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp _root_.D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.original_right_skew_finite, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.original_right_skew_finite)
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := `D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner.original_right_skew_finite.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalRightSkew.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalRightSkew
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "arg", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalRightSkew
