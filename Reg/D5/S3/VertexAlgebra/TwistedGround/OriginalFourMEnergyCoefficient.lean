import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open LatticeHalfFockGradedTrace LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient LatticeInvolution
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open HalfFock.LatticeHalfFockParityField
open TwistedGround OriginalFourMChargeCoset OriginalFourMEnergyCoefficient
open SignedOscillatorWick OperatorAlgebra SourceBPZ.OriginalSourceCoevaluation MvPolynomial
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)
open LeanInformationAudit
open private groundForm from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient

private theorem exists_lattice :
    ∃ D : LatticeData, D.rank = 24 ∧ IsUnit D.G.det ∧
      (D.G.map (Int.cast : ℤ → ℝ)).PosDef := by
  obtain ⟨D, _, h24, hu, hD, _⟩ :=
    _root_.D5.S3.Arith.Lattices.Golay.RealLeech.exists_positive_even_unimodular_gram
  exact ⟨D, h24, hu, hD⟩

namespace oscillatorKernel_reflected

def arena : Arena where
  signature := complexSignature
  Law r := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (H K : ℕ) (k : ℤ) (q : Charge D) (p P Q : Oscillator D),
    r.readout () ()
      (oscillatorKernel D hu H K k (-q) (sigma D p) P Q)
      (oscillatorKernel D hu H K k q p P Q)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro law
  obtain ⟨D, _, hu, _⟩ := exists_lattice
  exact law D hu 0 0 0 0 0 0 0

def family : Registration arena (type_of% (@OriginalFourMEnergyCoefficient.oscillatorKernel_reflected)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@OriginalFourMEnergyCoefficient.oscillatorKernel_reflected, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@OriginalFourMEnergyCoefficient.oscillatorKernel_reflected) (Realization complexSignature) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient.oscillatorKernel_reflected "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient.oscillatorKernel_reflected.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end oscillatorKernel_reflected

namespace cosetKernel_unreflected

def arena : Arena where
  signature := complexSignature
  Law r := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (H K : ℕ) (k t : ℤ) (P Q R S : Oscillator D) (a : ModTwoCharge D),
    r.readout () ()
      (cosetKernel D hu H K k t P Q R S a)
      (∑ᶠ b : EnergyFiber D ((H : ℤ)+(K : ℤ)-k-1),
        if reduceCharge D b.val.1 = a then
          chargeScalar D b.val.1 * chargeScalar D (-b.val.1) *
            oscillatorKernel D hu H K k b.val.1 (monomial b.val.2 1) P Q *
            wick D S (oscillatorCorrected D hu (-b.val.1) (-2*t-2)
              (dualOscillatorMonomial D b.val.2) R)
        else 0)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro law
  obtain ⟨D, _, hu, hD⟩ := exists_lattice
  exact law D hu hD 0 0 0 0 0 0 0 0 0

def family : Registration arena (type_of% (@OriginalFourMEnergyCoefficient.cosetKernel_unreflected)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@OriginalFourMEnergyCoefficient.cosetKernel_unreflected, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@OriginalFourMEnergyCoefficient.cosetKernel_unreflected) (Realization complexSignature) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient.cosetKernel_unreflected "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient.cosetKernel_unreflected.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end cosetKernel_unreflected

namespace fourM_energy_coefficient

def arena : Arena where
  signature := complexSignature
  Law r := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K E : ℕ) (t : ℤ) (u v : paritySpace D hu (-1))
    (P Q R S : Oscillator D) (x y z d : ActualGround D hu)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] y)
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val),
    r.readout () ()
      (fourMScalar D hu hD ((H : ℤ)+(K : ℤ)-E-1) t u v (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d))
      (∑ a : ModTwoCharge D,
        PowerSeries.coeff E (PowerSeries.rescale (-1) (cosetSeries D hD H K t P Q R S a)) *
          groundForm D hu y (chargeOperator D (groundRepresentation D hu) a x) *
          groundForm D hu d (chargeOperator D (groundRepresentation D hu) a z))

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro law
  obtain ⟨D, h24, hu, hD⟩ := exists_lattice
  exact law D hu hD h24 0 0 0 0 0 0 0 0 0 0 0 0 0 0
    (by simp) (by simp) (by simp) (by simp)

def family : Registration arena (type_of% (@OriginalFourMEnergyCoefficient.fourM_energy_coefficient)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@OriginalFourMEnergyCoefficient.fourM_energy_coefficient, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@OriginalFourMEnergyCoefficient.fourM_energy_coefficient) (Realization complexSignature) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient.fourM_energy_coefficient "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient.fourM_energy_coefficient.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end fourM_energy_coefficient

namespace fourM_negative_energy

def arena : Arena where
  signature := complexSignature
  Law r := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K : ℕ) (k t : ℤ) (u v : paritySpace D hu (-1))
    (P Q R S : Oscillator D) (x y z d : ActualGround D hu)
    (huP : u.val = P ⊗ₜ[ℂ] x) (hvQ : v.val = Q ⊗ₜ[ℂ] y)
    (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (hneg : (H : ℤ) + (K : ℤ) - k - 1 < 0),
    r.readout () ()
      (fourMScalar D hu hD k t u v (R ⊗ₜ[ℂ] z) (S ⊗ₜ[ℂ] d))
      (0)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro law
  obtain ⟨D, h24, hu, hD⟩ := exists_lattice
  exact law D hu hD h24 0 0 0 0 0 0 0 0 0 0 0 0 0 0
    (by simp) (by simp) (by simp) (by simp) (by omega)

def family : Registration arena (type_of% (@OriginalFourMEnergyCoefficient.fourM_negative_energy)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@OriginalFourMEnergyCoefficient.fourM_negative_energy, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@OriginalFourMEnergyCoefficient.fourM_negative_energy) (Realization complexSignature) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient.fourM_negative_energy "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient.fourM_negative_energy.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end fourM_negative_energy

namespace right_selector

def arena : Arena where
  signature := complexSignature
  Law r := ∀ (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (E : ℕ) (q : Charge D) (hq : chargeEnergy D q ≤ E)
    (t : ℤ) (beta gamma : Exponent D),
    r.readout () ()
      (selector D (-q) (-2*t-2) (E - (chargeEnergy D q).toNat) beta gamma)
      (if (doubledWeight D beta - doubledWeight D gamma) % 2 = 0 then
        if t = (E : ℤ)-1+(doubledWeight D beta-doubledWeight D gamma)/2 then 1 else 0
      else 0)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro law
  obtain ⟨D, _, _, hD⟩ := exists_lattice
  exact law D hD 0 0 (by simp) 0 0 0

def family : Registration arena (type_of% (@OriginalFourMEnergyCoefficient.right_selector)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@OriginalFourMEnergyCoefficient.right_selector, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@OriginalFourMEnergyCoefficient.right_selector) (Realization complexSignature) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient.right_selector "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient.right_selector.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end right_selector

namespace lowered_left_selector

def arena : Arena where
  signature := complexSignature
  Law r := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (H K E i j : ℕ) (q : Charge D) (hq : chargeEnergy D q ≤ E)
    (P Q : Oscillator D) (x y : ActualGround D hu)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hP : actualTensorL0 D hu (P ⊗ₜ[ℂ] x) = (H : ℂ) • (P ⊗ₜ[ℂ] x))
    (hQ : actualTensorL0 D hu (Q ⊗ₜ[ℂ] y) = (K : ℂ) • (Q ⊗ₜ[ℂ] y))
    (beta gamma : Exponent D)
    (hb : beta ∈ ((oscillatorLower D ^ j) P).support)
    (hg : gamma ∈ ((oscillatorLower D ^ i) Q).support),
    doubledWeight D beta = 2*(H : ℤ)-3-2*(j : ℤ) ∧
    doubledWeight D gamma = 2*(K : ℤ)-3-2*(i : ℤ) ∧
    leftExponent H K E i j = -2*(E : ℤ)-doubledWeight D beta+doubledWeight D gamma ∧
    r.readout () ()
      (selector D q (leftExponent H K E i j) (E - (chargeEnergy D q).toNat) beta gamma)
      (1)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro law
  obtain ⟨D, h24, hu, hD⟩ := exists_lattice
  let a : Fin D.rank := ⟨0, by omega⟩
  let beta : Exponent D := Finsupp.single (a, 0) 1
  let g : ActualGround D hu := Pi.single 0 1
  let P : Oscillator D := monomial beta 1
  have hg : g ≠ 0 := by
    intro h
    have h₀ := congrFun h 0
    simp [g] at h₀
  have hP : actualTensorL0 D hu (P ⊗ₜ[ℂ] g) = (2 : ℂ) • (P ⊗ₜ[ℂ] g) := by
    rw [show P ⊗ₜ[ℂ] g = actualAmbientBasis D hu (beta, 0) from
      (actual_basis_apply D hu beta 0).symm, actual_basis_eigenvalue]
    have w : oddWeight D beta = 1 := by
      simp [beta, oddWeight, Finsupp.weight_single, LatticeHalfFockChargedCoefficients.omega]
    rw [w, h24]
    norm_num
  have hb : beta ∈ ((oscillatorLower D ^ 0) P).support := by
    simp [P, MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial]
  exact (law D hu hD h24 2 2 0 0 0 0 (by simp) P P g g hg hg
    (by simpa using hP) (by simpa using hP) beta beta hb hb).2.2.2

def family : Registration arena (type_of% (@OriginalFourMEnergyCoefficient.lowered_left_selector)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@OriginalFourMEnergyCoefficient.lowered_left_selector, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@OriginalFourMEnergyCoefficient.lowered_left_selector) (Realization complexSignature) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient.lowered_left_selector "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient.lowered_left_selector.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg",
        "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end lowered_left_selector

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient
