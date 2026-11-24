import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickPartition

/-! Equality readouts for the marked fixed-charge jet and its same-puncture
correction coefficient. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.TwistedGround
open LatticeGeneratingFieldLocality LatticeHalfFock
open FourPoint.OriginalFourMActualChart (Chart Puncture loweringParameter)
open OriginalFourMPhysicalCovariance (jac slotCorrection relative)
open OriginalFourMPhysicalProduct (physicalChargeSummand physicalMean)
open OriginalFourMChartProduct (chartTau)
open OriginalFourMSpatialWick (spatialCoefficient)
open OriginalGaussianSewnAnalytic (coefficient)
open HalfFock.OriginalHalfCurrentWickPolynomial (pair)
open AffineOccurrenceWick (wick)
open AffineWickConvolution (partitions)
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSpatialWickPartition
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickPartition

private def sampleLattice : LatticeData where
  rank := 1
  G := fun _ _ => 2
  symmetric := by intro i j; rfl
  even_diagonal := by intro i; exact ⟨1, rfl⟩

private def sampleColour : Fin sampleLattice.rank := ⟨0, by decide⟩

namespace CorrectionPair

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ (D : LatticeData) {x : ℝ}
      (hx : 0 < x) (hx₁ : x < 1) (c : Chart) (i : Puncture) (a b : Index D),
    r.readout () ()
      (coefficient b.2 (fun v => coefficient a.2 (fun u =>
        ((D.G a.1 b.1 : ℂ) * relative c i * relative c i) *
          (-(slotCorrection c x i i u v / (jac c x i u * jac c x i v))))))
      (liftedScale c x i a.2 * liftedScale c x i b.2 *
        MvPolynomial.constantCoeff ((pair D a b).eval
          (MvPolynomial.C (-loweringParameter c i))))

private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h sampleLattice (x := 3 / 4) (by norm_num) (by norm_num) .A .P
    (sampleColour, 0) (sampleColour, 1)

def family : Registration arena (type_of% (@correction_pair_coefficient)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@correction_pair_coefficient, complexFalse, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@correction_pair_coefficient) (Realization complexSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickPartition.CorrectionPair.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickPartition.CorrectionPair.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickPartition
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CorrectionPair

namespace FixedCharge

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ {X : Type u} [Fintype X] [DecidableEq X] (D : LatticeData)
      (slot : X → Puncture) (colour : X → Fin D.rank) (upperA : Bool) (c : Chart) {x : ℝ}
      (hx : 0 < x) (hx₁ : x < 1) (q : Charge D) (n : X → ℕ) (l : List X) (hl : l.Nodup),
    r.readout () ()
      (spatialCoefficient (Sum.elim n (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl)
        (physicalChargeSummand D slot colour upperA c x q) 0)
      (Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x * (bilinear D q q : ℂ) / 2) *
        ((partitions l).map fun p => wick (correctionTaylor D c x slot colour n) 0 p.1 *
          wick (nativeTaylor D upperA c x slot colour n)
            (fun i => coefficient (n i) (fun u =>
              physicalMean D q upperA c x slot colour i u * relative c (slot i))) p.2).sum)

private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  letI : DecidableEq PUnit.{u+1} := Classical.decEq _
  exact h (X := PUnit.{u+1}) sampleLattice (fun _ => .P) (fun _ => sampleColour)
    true .A (x := 3 / 4) (by norm_num) (by norm_num) 0 (fun _ => 0) [] List.nodup_nil

def family : Registration arena.{u}
    (type_of% (@physical_marked_coefficient_wick_partition.{u})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@physical_marked_coefficient_wick_partition.{u}, complexFalse, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@physical_marked_coefficient_wick_partition.{u}) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickPartition.FixedCharge.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickPartition.FixedCharge.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickPartition
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FixedCharge

end Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWickPartition
