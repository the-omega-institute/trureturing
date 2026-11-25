import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAFourCurrent
import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic

/-! Equality readouts for the two physical charge identities and real A/B crossing. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.TwistedGround
open FourPoint.OriginalFourMActualChart
open FourPoint.OriginalFourMChargeNormal (projectOccupations)
open LatticeGeneratingFieldLocality (LatticeData Charge)
open LatticePositiveEnergy (chargeEnergy)
open LatticeDiscriminantTheta (gramReal)
open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge reduceCharge)
open ActualLeechHyperbolic (leechData leech_spec)
open OriginalFourMChartProduct (chartPeriod)
open OriginalFourMPhysicalProduct (physicalChargeSummand)
open OriginalFourMSectorContinuation (slitChargeTerm)
open OriginalFourMSpatialWick (spatialCoefficient)
open OriginalFourMChargeCoset (slitChannelA slitChannelB)
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAFourCurrent

private def sampleColours : Fin 4 → Fin leechData.rank :=
  fun _ => Fin.cast leech_spec.1.symm 0

private theorem sampleChargeEnergy : 0 ≤ chargeEnergy leechData 0 := by simp

namespace chartA_four_current_fixed_charge

abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀
    (D : LatticeData) (colour : Fin 4 → Fin D.rank) (q : Charge D) (hq : 0 ≤ chargeEnergy D q)
    (upperA : Bool) {x : ℝ} (hx : 1 / 2 < x) (hx₁ : x < 1),
    let slot : Fin 4 → Puncture := ![.P, .Q, .R, .S]
    let l : List (Fin 4) := [0, 1, 2, 3]
    let osc := fun i : Fin 4 => MvPolynomial.monomial (Finsupp.single (colour i, 0) 1) (1 : ℂ)
    R.readout () ()
      ((chartPeriod upperA .A x ^ (12 : ℕ))⁻¹ *
        spatialCoefficient (Sum.elim (fun _ : Fin 4 => (0 : ℕ)) (fun _ : Fin 4 => 1))
          (l.map Sum.inr ++ l.map Sum.inl) (physicalChargeSummand D slot colour upperA .A x q) 0)
      ((-Complex.I / ((x : ℂ) ^ 3 * (1 - (x : ℂ)))) *
        projectOccupations D 2 2 0 (-1) (osc 0) (osc 1) (osc 2) (osc 3)
          (fun b g d e => slitChargeTerm D b g d e q (parameter .A (x : ℂ))))

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h leechData sampleColours 0 sampleChargeEnergy true (x := 3 / 4) (by norm_num) (by norm_num)

def family : Registration arena
    (type_of% (@D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAFourCurrent.chartA_four_current_fixed_charge)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation :=
    ⟨@D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAFourCurrent.chartA_four_current_fixed_charge,
      complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAFourCurrent.chartA_four_current_fixed_charge)
    (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAFourCurrent.chartA_four_current_fixed_charge.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAFourCurrent.chartA_four_current_fixed_charge.family
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
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAFourCurrent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end chartA_four_current_fixed_charge

namespace chartB_four_current_fixed_charge

abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀
    (D : LatticeData) (colour : Fin 4 → Fin D.rank) (q : Charge D) (hq : 0 ≤ chargeEnergy D q)
    (upperA : Bool) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1),
    let slot : Fin 4 → Puncture := ![.P, .Q, .R, .S]
    let l : List (Fin 4) := [0, 1, 2, 3]
    let osc := fun i : Fin 4 => MvPolynomial.monomial (Finsupp.single (colour i, 0) 1) (1 : ℂ)
    R.readout () ()
      ((chartPeriod upperA .B x ^ (12 : ℕ))⁻¹ *
        spatialCoefficient (Sum.elim (fun _ : Fin 4 => (0 : ℕ)) (fun _ : Fin 4 => 1))
          (l.map Sum.inr ++ l.map Sum.inl) (physicalChargeSummand D slot colour upperA .B x q) 0)
      ((-Complex.I * (1 - (x : ℂ)) ^ 3 / (x : ℂ)) *
        projectOccupations D 2 2 0 (-1) (osc 1) (osc 2) (osc 0) (osc 3)
          (fun b g d e => slitChargeTerm D b g d e q (parameter .B (x : ℂ))))

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h leechData sampleColours 0 sampleChargeEnergy true (x := 3 / 4) (by norm_num) (by norm_num)

def family : Registration arena
    (type_of% (@D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAFourCurrent.chartB_four_current_fixed_charge)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation :=
    ⟨@D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAFourCurrent.chartB_four_current_fixed_charge,
      complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAFourCurrent.chartB_four_current_fixed_charge)
    (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAFourCurrent.chartB_four_current_fixed_charge.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAFourCurrent.chartB_four_current_fixed_charge.family
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
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAFourCurrent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end chartB_four_current_fixed_charge

namespace four_current_slit_crossing

abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (h24 : D.rank = 24) (colour : Fin 4 → Fin D.rank)
    (m n r : ℤ) (hs : m + n + r = 2) (a : ModTwoCharge D)
    {x : ℝ} (hx : 1 / 2 < x) (hx₁ : x < 1),
    let osc := fun i : Fin 4 => MvPolynomial.monomial (Finsupp.single (colour i, 0) 1) (1 : ℂ)
    R.readout () ()
      (slitChannelA D 2 2 (m + n + r) (osc 0) (osc 1) (osc 2) (osc 3) a
          (parameter .A (x : ℂ)))
      ((2 : ℂ) ^ (12 : ℕ) * (x : ℂ) ^ (4 : ℕ) *
        slitChannelB D 2 2 2 m n r (osc 0) (osc 1) (osc 2) (osc 3) a
          (parameter .B (x : ℂ)))

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h leechData leech_spec.2.1 leech_spec.2.2.1 leech_spec.1 sampleColours
    0 0 2 (by norm_num) (reduceCharge leechData 0) (x := 3 / 4) (by norm_num) (by norm_num)

def family : Registration arena
    (type_of% (@D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAFourCurrent.four_current_slit_crossing)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation :=
    ⟨@D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAFourCurrent.four_current_slit_crossing,
      complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAFourCurrent.four_current_slit_crossing)
    (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAFourCurrent.four_current_slit_crossing.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAFourCurrent.four_current_slit_crossing.family
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
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAFourCurrent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end four_current_slit_crossing

end Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAFourCurrent
