import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent
import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic

/-! Equality readouts for the physical D-lip coefficients and A/D crossing. -/

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
open OriginalFourMSpatialWick (spatialCoefficient)
open OriginalFourPointChartGluing (U_A U_D)
open OriginalFourMSectorContinuation (dLipChargeSector)
open OriginalFourMChargeCoset
  (identityK quadraticSign fourierSign channelA channelB channelD slitChannelA slitChannelD dLipChannel)
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)
open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDFourCurrent (four_current_identityK)
open scoped BigOperators Topology

open private marks slot currentOscillator fourCurrentJet from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAFourCurrent

open private dLipChargeTerm from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent

private def sampleColours : Fin 4 → Fin leechData.rank :=
  fun _ => Fin.cast leech_spec.1.symm 0

private theorem sampleChargeEnergy : 0 ≤ chargeEnergy leechData 0 := by simp

namespace chartD_four_current_fixed_charge

open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDFourCurrent (chartD_four_current_fixed_charge)

abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀
    (D : LatticeData) (colour : Fin 4 → Fin D.rank) (q : Charge D) (_hq : 0 ≤ chargeEnergy D q)
    {x : ℝ} (_hx : 0 < x) (_hx₁ : x < 1),
    let osc := fun i : Fin 4 => MvPolynomial.monomial (Finsupp.single (colour i, 0) 1) (1 : ℂ)
    R.readout () ()
      ((chartPeriod true .D x ^ (12 : ℕ))⁻¹ *
        spatialCoefficient (Sum.elim (fun _ : Fin 4 => (0 : ℕ)) (fun _ : Fin 4 => 1))
          (marks.map Sum.inr ++ marks.map Sum.inl) (physicalChargeSummand D slot colour true .D x q) 0)
      ((-Complex.I * (1 - (x : ℂ)) ^ 3 / (x : ℂ) ^ 3) *
        projectOccupations D 2 2 0 (-1) (osc 0) (osc 2) (osc 1) (osc 3)
          (fun b g d e => dLipChargeTerm D b g d e q (parameter .D (x : ℂ))))

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h leechData sampleColours 0 sampleChargeEnergy (x := 3 / 4) (by norm_num) (by norm_num)

def family : Registration arena (type_of% (@chartD_four_current_fixed_charge)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@chartD_four_current_fixed_charge, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@chartD_four_current_fixed_charge)
    (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent.chartD_four_current_fixed_charge.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent.chartD_four_current_fixed_charge.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent
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

end chartD_four_current_fixed_charge

namespace chartD_four_current_sector

open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDFourCurrent (chartD_four_current_sector)

abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀
    (D : LatticeData) (hu : IsUnit D.G.det) (_hD : (gramReal D).PosDef)
    (colour : Fin 4 → Fin D.rank) {x : ℝ} (_hx : 0 < x) (_hx₁ : x < 1) (a : ModTwoCharge D),
    let osc := currentOscillator D colour
    R.readout () ()
      (fourCurrentJet D hu colour true .D x a)
      ((-Complex.I * (1 - (x : ℂ)) ^ 3 / (x : ℂ) ^ 3) *
        projectOccupations D 2 2 0 (-1) (osc 0) (osc 2) (osc 1) (osc 3)
          (fun b g d e => dLipChargeSector D true a b g d e (parameter .D (x : ℂ))))

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h leechData leech_spec.2.1 leech_spec.2.2.1 sampleColours
    (x := 3 / 4) (by norm_num) (by norm_num) (reduceCharge leechData 0)

def family : Registration arena (type_of% (@chartD_four_current_sector)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@chartD_four_current_sector, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@chartD_four_current_sector)
    (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent.chartD_four_current_sector.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent.chartD_four_current_sector.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent
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

end chartD_four_current_sector

namespace four_current_d_lip_crossing

open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDFourCurrent (four_current_d_lip_crossing)

abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (_hu : IsUnit D.G.det)
    (_hD : (gramReal D).PosDef) (_h24 : D.rank = 24) (colour : Fin 4 → Fin D.rank)
    (m n r : ℤ) (_hs : m + n + r = 2) (b : ModTwoCharge D)
    {x : ℝ} (_hx : 1 / 2 < x) (_hx₁ : x < 1),
    let osc := currentOscillator D colour
    R.readout () ()
      (slitChannelA D 2 2 (m + n + r) (osc 0) (osc 1) (osc 2) (osc 3) b (parameter .A (x : ℂ)))
      (dLipChannel D true 2 2 2 m n r (osc 0) (osc 1) (osc 2) (osc 3) b (parameter .D (x : ℂ)))

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h leechData leech_spec.2.1 leech_spec.2.2.1 leech_spec.1 sampleColours
    0 0 2 (by norm_num) (reduceCharge leechData 0) (x := 3 / 4) (by norm_num) (by norm_num)

def family : Registration arena (type_of% (@four_current_d_lip_crossing)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@four_current_d_lip_crossing, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@four_current_d_lip_crossing)
    (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent.four_current_d_lip_crossing.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent.four_current_d_lip_crossing.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent
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

end four_current_d_lip_crossing

namespace four_current_slit_ad_overlap

open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDFourCurrent (four_current_slit_ad_overlap)

abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (_hu : IsUnit D.G.det)
    (_hD : (gramReal D).PosDef) (_h24 : D.rank = 24) (colour : Fin 4 → Fin D.rank)
    (m n r : ℤ) (_hs : m + n + r = 2) (b : ModTwoCharge D),
    let osc := currentOscillator D colour
    ∃ y ∈ U_A ∩ U_D, ∀ᶠ z in 𝓝 y,
      R.readout () ()
        (slitChannelA D 2 2 (m + n + r) (osc 0) (osc 1) (osc 2) (osc 3) b (parameter .A z))
        (slitChannelD D 2 2 2 m n r (osc 0) (osc 1) (osc 2) (osc 3) b (parameter .D z))

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  obtain ⟨y, _, hFalse⟩ := h leechData leech_spec.2.1 leech_spec.2.2.1 leech_spec.1 sampleColours
    0 0 2 (by norm_num) (reduceCharge leechData 0)
  exact (Filter.Eventually.self_of_nhds hFalse : False)

def family : Registration arena (type_of% (@four_current_slit_ad_overlap)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@four_current_slit_ad_overlap, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@four_current_slit_ad_overlap)
    (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent.four_current_slit_ad_overlap.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent.four_current_slit_ad_overlap.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "arg", "fn", "arg",
        "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end four_current_slit_ad_overlap

namespace actualLeechIdentityK

abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (colour : Fin 4 → Fin leechData.rank) (m n r : ℤ) (_hs : m + n + r = 2),
    let osc := currentOscillator leechData colour
    ∀ b : ModTwoCharge leechData,
      R.readout () ()
        (∑ a : ModTwoCharge leechData, quadraticSign leechData a * fourierSign leechData a b *
          channelA leechData leech_spec.2.1 2 2 m n r (osc 0) (osc 1) (osc 2) (osc 3) a)
        ((2 : ℂ) ^ (12 : ℕ) *
          channelB leechData leech_spec.2.1 2 2 2 m n r (osc 0) (osc 1) (osc 2) (osc 3) b -
          ∑ a : ModTwoCharge leechData, quadraticSign leechData (a + b) *
            channelD leechData leech_spec.2.1 2 2 2 m n r (osc 0) (osc 1) (osc 2) (osc 3) a)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h sampleColours 0 0 2 (by norm_num) (reduceCharge leechData 0)

/-- The original identity on the actual Leech lattice, with every colour and signed mode retained. -/
def family : Registration arena
    (∀ (colour : Fin 4 → Fin leechData.rank) (m n r : ℤ), m + n + r = 2 →
      let osc := currentOscillator leechData colour
      identityK leechData leech_spec.2.1 2 2 2 m n r (osc 0) (osc 1) (osc 2) (osc 3)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation :=
    ⟨four_current_identityK
      leechData leech_spec.2.1 leech_spec.2.2.1 leech_spec.1,
      complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

end actualLeechIdentityK

end Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent
