import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCurrentRegression
import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic

/-! Equality readouts for the fixed-charge two-mark coefficient and the inverse lowering flow. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.TwistedGround
open FourPoint.OriginalFourMActualChart
open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open ActualLeechHyperbolic (leechData leech_spec)
open OriginalFourMChartProduct (chartPeriod)
open OriginalFourMPhysicalProduct (physicalChargeSummand)
open OriginalFourMSectorContinuation (slitChargeTerm)
open OriginalFourMSpatialWick (spatialCoefficient)
open OriginalFourMChargeCoset (oscillatorLower)
open OriginalFourMCurrentRegression
open FactorialFockMetric (weight)
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCurrentRegression

private def sampleColour : Fin leechData.rank := Fin.cast leech_spec.1.symm 0

private theorem sampleChargeEnergy : 0 ≤ chargeEnergy leechData 0 := by simp

namespace FixedCharge

abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (i : Fin D.rank) (q : Charge D) (_hq : 0 ≤ chargeEnergy D q)
    (upperA : Bool) {x : ℝ} (_hx : 1 / 2 < x) (_hx1 : x < 1),
    let t := parameter .A (x : ℂ)
    let lam := scale .A x .P
    let F := fun d => slitChargeTerm D d 0 0 0 q t
    let d10 : Exponent D := Finsupp.single (i, 1) 1 + Finsupp.single (i, 0) 1
    let d00 : Exponent D := Finsupp.single (i, 0) 2
    R.readout () ()
      ((chartPeriod upperA .A x ^ (12 : ℕ))⁻¹ *
        spatialCoefficient (Sum.elim ![1, 0] (fun _ => 1))
          ([Sum.inr 0, Sum.inr 1, Sum.inl 0, Sum.inl 1] : List (Fin 2 ⊕ Fin 2))
          (physicalChargeSummand D (fun _ => .P) (fun _ => i) upperA .A x q) 0)
      (((1 - t) ^ (3 : ℕ) / lam ^ (2 : ℕ)) *
        (F d10 - 3 * F d00 + (3 / 16 : ℂ) * (D.G i i : ℂ) * F 0))

private theorem rejected_law : ¬ arena.Law complexFalse := by
  intro h
  exact h leechData sampleColour 0 sampleChargeEnergy true (x := 3 / 4) (by norm_num) (by norm_num)

def family : Registration arena (type_of% (@chartA_same_puncture_modes_one_zero_fixed_charge)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@chartA_same_puncture_modes_one_zero_fixed_charge, complexFalse, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_law
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@chartA_same_puncture_modes_one_zero_fixed_charge) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCurrentRegression.FixedCharge.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCurrentRegression.FixedCharge.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCurrentRegression
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FixedCharge

namespace LoweringCoefficient

abbrev signature :=
  _root_.Reg.Support.SingleDependentReadout.signature LatticeData
    (fun D => Oscillator D) (fun D => Oscillator D → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ a b => a = b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (_hu : IsUnit D.G.det) (i : Fin D.rank) (n : ℕ),
    R.readout () D
      ((n.factorial : ℂ)⁻¹ • (oscillatorLower D ^ n)
        (MvPolynomial.X (i, 1) * MvPolynomial.X (i, 0)))
      (if n = 0 then MvPolynomial.X (i, 1) * MvPolynomial.X (i, 0)
        else if n = 1 then (3 / 2 : ℂ) • (MvPolynomial.X (i, 0) ^ 2)
        else if n = 2 then ((3 / 16 : ℂ) * (D.G i i : ℂ)) • 1
        else 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h leechData leech_spec.2.1 sampleColour 0

def family : Registration arena (type_of% (@lowering_modes_one_zero)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@lowering_modes_one_zero, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨leechData, 0, 1, ?_⟩
    intro h
    have h' : (1 : Oscillator leechData) = 0 := Eq.mp (congrFun h 0) rfl
    exact one_ne_zero h'

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@lowering_modes_one_zero) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCurrentRegression.LoweringCoefficient.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCurrentRegression.LoweringCoefficient.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCurrentRegression
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LoweringCoefficient

namespace FactorialReadout

abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (_hu : IsUnit D.G.det) (i : Fin D.rank) (q : Charge D)
    (_hq : 0 ≤ chargeEnergy D q) (upperA : Bool) {x : ℝ} (_hx : 1 / 2 < x) (_hx1 : x < 1),
    let t := parameter .A (x : ℂ)
    let lam := scale .A x .P
    let P : Oscillator D := MvPolynomial.X (i, 1) * MvPolynomial.X (i, 0)
    let T := ∑ k ∈ Finset.range 4, ((-1 : ℂ) ^ k / (k.factorial : ℂ)) •
      (oscillatorLower D ^ k) P
    R.readout () ()
      ((chartPeriod upperA .A x ^ (12 : ℕ))⁻¹ *
        spatialCoefficient (Sum.elim ![1, 0] (fun _ => 1))
          ([Sum.inr 0, Sum.inr 1, Sum.inl 0, Sum.inl 1] : List (Fin 2 ⊕ Fin 2))
          (physicalChargeSummand D (fun _ => .P) (fun _ => i) upperA .A x q) 0)
      (((1 - t) ^ (3 : ℕ) / lam ^ (2 : ℕ)) *
        ∑ d ∈ T.support, T.coeff d * (weight d : ℂ) * slitChargeTerm D d 0 0 0 q t)

private theorem rejected_law : ¬ arena.Law complexFalse := by
  intro h
  exact h leechData leech_spec.2.1 sampleColour 0 sampleChargeEnergy true
    (x := 3 / 4) (by norm_num) (by norm_num)

def family : Registration arena (type_of% (@chartA_same_puncture_modes_one_zero_lowering)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@chartA_same_puncture_modes_one_zero_lowering, complexFalse, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_law
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@chartA_same_puncture_modes_one_zero_lowering) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCurrentRegression.FactorialReadout.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCurrentRegression.FactorialReadout.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCurrentRegression
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FactorialReadout

end Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCurrentRegression
