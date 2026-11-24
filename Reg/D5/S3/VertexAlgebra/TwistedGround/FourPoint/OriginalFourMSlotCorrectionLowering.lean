import Reg.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial
import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlotCorrectionLowering

/-! Equality readouts for the signed occurrence scales, puncture factors,
and marked fixed-charge coefficient. -/

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
open OriginalFourMPhysicalCovariance (relative)
open OriginalFourMPhysicalProduct (physicalChargeSummand physicalMean)
open OriginalFourMChartProduct (chartTau)
open OriginalFourMSpatialWick (spatialCoefficient)
open OriginalFourMSpatialWickPartition (correctionTaylor liftedScale nativeTaylor)
open OriginalFourMWickLowering (pairWeight)
open OriginalGaussianSewnAnalytic (coefficient)
open AffineOccurrenceWick (wick)
open AffineWickConvolution (partitions)
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSlotCorrectionLowering
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)

open scoped BigOperators

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlotCorrectionLowering

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i; exact Fin.elim0 i
  even_diagonal := by intro i; exact Fin.elim0 i

private theorem emptyLattice_unit : IsUnit emptyLattice.G.det := by
  change IsUnit (0 : Matrix (Fin 0) (Fin 0) ℤ).det
  simp

namespace SameSlot

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ {X : Type u} (D : LatticeData) (c : Chart) (x : ℝ)
      (i : Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (l : List X),
    r.readout () ()
      (wick (correctionTaylor D c x (fun _ => i) colour n) 0 l)
      ((l.map fun a => liftedScale c x i (n a)).prod *
        wick (Matrix.of fun a b => pairWeight D (-loweringParameter c i)
          (colour a, n a) (colour b, n b)) 0 l)

private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact h (X := PEmpty.{u+1}) emptyLattice .A 0 .P (fun a => nomatch a) (fun _ => 0) []

def family : Registration arena.{u} (type_of% (@same_slot_correction.{u})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@same_slot_correction.{u}, complexFalse, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@same_slot_correction.{u}) (Realization complexSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlotCorrectionLowering.SameSlot.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlotCorrectionLowering.SameSlot.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlotCorrectionLowering
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

end SameSlot

namespace FourSlots

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ {X : Type u} [Finite X] (D : LatticeData)
      (_hu : IsUnit D.G.det) (c : Chart) (x : ℝ) (slot : X → Puncture)
      (colour : X → Fin D.rank) (n : X → ℕ) (l : List X),
    r.readout () ()
      (wick (correctionTaylor D c x slot colour n) 0 l)
      ((l.map fun a => liftedScale c x (slot a) (n a)).prod *
        (open Classical in ∏ i ∈ ({.P, .Q, .R, .S} : Finset Puncture),
          wick (Matrix.of fun a b => pairWeight D (-loweringParameter c i)
            (colour a, n a) (colour b, n b)) 0 (l.filter fun a => decide (slot a = i))))

private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact h (X := PEmpty.{u+1}) emptyLattice emptyLattice_unit .A 0 (fun _ => .P)
    (fun a => nomatch a) (fun _ => 0) []

def family : Registration arena.{u} (type_of% (@physical_correction_by_slot.{u})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@physical_correction_by_slot.{u}, complexFalse, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@physical_correction_by_slot.{u}) (Realization complexSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlotCorrectionLowering.FourSlots.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlotCorrectionLowering.FourSlots.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlotCorrectionLowering
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

end FourSlots

namespace FixedCharge

open Classical in
abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ {X : Type u} [Fintype X] [DecidableEq X] (D : LatticeData)
      (_hu : IsUnit D.G.det) (slot : X → Puncture) (colour : X → Fin D.rank)
      (upperA : Bool) (c : Chart) {x : ℝ} (_hx : 0 < x) (_hx₁ : x < 1)
      (q : Charge D) (n : X → ℕ) (l : List X) (_hl : l.Nodup),
    r.readout () ()
      (spatialCoefficient (Sum.elim n (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl)
        (physicalChargeSummand D slot colour upperA c x q) 0)
      (Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x * (bilinear D q q : ℂ) / 2) *
        ((partitions l).map fun p =>
          (p.1.map fun a => liftedScale c x (slot a) (n a)).prod *
          (∏ i ∈ ({.P, .Q, .R, .S} : Finset Puncture),
            wick (Matrix.of fun a b => pairWeight D (-loweringParameter c i)
              (colour a, n a) (colour b, n b)) 0 (p.1.filter fun a => decide (slot a = i))) *
          wick (nativeTaylor D upperA c x slot colour n)
            (fun i => coefficient (n i) (fun u =>
              physicalMean D q upperA c x slot colour i u * relative c (slot i))) p.2).sum)

private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  classical
  exact h (X := PEmpty.{u+1}) emptyLattice emptyLattice_unit (fun _ => .P)
    (fun a => nomatch a) true .A (x := 3 / 4) (by norm_num) (by norm_num) 0
    (fun _ => 0) [] List.nodup_nil

def family : Registration arena.{u} (type_of% (@physical_marked_coefficient_by_slot.{u})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@physical_marked_coefficient_by_slot.{u}, complexFalse, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@physical_marked_coefficient_by_slot.{u}) (Realization complexSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlotCorrectionLowering.FixedCharge.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlotCorrectionLowering.FixedCharge.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlotCorrectionLowering
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FixedCharge

namespace FiniteLowering

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality (LatticeData)
open _root_.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMActualChart
  (Chart Puncture loweringParameter)
open _root_.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial (word creator)
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset (oscillatorLower)
open _root_.D5.S3.VertexAlgebra.TwistedGround.AffineOccurrenceWick (wick)
open _root_.D5.S3.VertexAlgebra.TwistedGround.AffineWickConvolution (partitions)
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMWickLowering (pairWeight)
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMSlotCorrectionLowering
  (slot_lowering_partition)
open _root_.Reg.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial
  (signature oscillatorEqual oscillatorFalse)

open private emptyLattice from Reg.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial
open private oscillatorEqualDependence from Reg.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} [Finite X] (D : LatticeData) (_hu : IsUnit D.G.det)
      (c : Chart) (i : Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (l : List X) (N : ℕ)
      (_hN : (word D (l.map fun a => (colour a, n a))).natDegree < N),
    R.readout () D
      (∑ k ∈ Finset.range N, ((-loweringParameter c i) ^ k / (k.factorial : ℂ)) •
        (oscillatorLower D ^ k) ((l.map fun a => MvPolynomial.X (colour a, n a)).prod))
      (((partitions l).map fun p =>
        MvPolynomial.C (wick (Matrix.of fun a b => pairWeight D (-loweringParameter c i)
          (colour a, n a) (colour b, n b)) 0 p.1) *
          (p.2.map fun a => (creator D (colour a, n a)).eval
            (MvPolynomial.C (-loweringParameter c i))).prod).sum)

private theorem rejectedLaw : ¬ arena.{u}.Law oscillatorFalse := by
  intro h
  have hu : IsUnit emptyLattice.G.det := by
    change IsUnit (0 : Matrix (Fin 0) (Fin 0) ℤ).det
    simp
  exact @h (ULift.{u} (Fin 0)) inferInstance emptyLattice hu .A .P
    (fun a => Fin.elim0 a.down) (fun _ => 0) [] 1 (by simp [word])

def family : Registration arena.{u} (type_of% (@slot_lowering_partition.{u})) where
  actual := oscillatorEqual
  bridge := Iff.rfl
  variation := ⟨@slot_lowering_partition.{u}, oscillatorFalse, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law oscillatorEqual oscillatorFalse rejectedLaw
  dependence := oscillatorEqualDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@slot_lowering_partition.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlotCorrectionLowering.FiniteLowering.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlotCorrectionLowering.FiniteLowering.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature oscillatorEqual.readout oscillatorEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlotCorrectionLowering
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FiniteLowering

end Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlotCorrectionLowering
