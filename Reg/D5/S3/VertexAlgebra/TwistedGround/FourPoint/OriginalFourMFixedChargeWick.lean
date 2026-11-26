import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMFixedChargeWick

/-! Dependent-family equality readout for the physical fixed-charge coefficient. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.TwistedGround
open LatticeGeneratingFieldLocality LatticeHalfFock
open FourPoint.OriginalFourMActualChart (Chart Puncture loweringParameter parameter)
open OriginalFourMPhysicalProduct (physicalChargeSummand)
open OriginalFourMChartProduct (chartTau)
open OriginalFourMSpatialWick (spatialCoefficient)
open OriginalFourMSpatialWickPartition (liftedScale)
open OriginalFourMWickLowering (pairWeight)
open AffineOccurrenceWick (wick)
open AffineWickConvolution (partitions)
open AffineWickAssignments (assign)
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMFixedChargeWick
  (modeMatrix nativeModeCovariance nativeModeMean physical_marked_coefficient_assign)
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)

open scoped BigOperators

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMFixedChargeWick

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i; exact Fin.elim0 i
  even_diagonal := by intro i; exact Fin.elim0 i

private theorem emptyLattice_unit : IsUnit emptyLattice.G.det := by
  change IsUnit (0 : Matrix (Fin 0) (Fin 0) ℤ).det
  simp

open Classical in
abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ {X : Type u} [Fintype X] [DecidableEq X] (D : LatticeData)
      (_hu : IsUnit D.G.det) (slot : X → Puncture) (colour : X → Fin D.rank)
      (upperA : Bool) (c : Chart) {x : ℝ} (_hx : 0 < x) (_hx₁ : x < 1)
      (_h : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨ c = .D ∧ upperA = true)
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
          assign (modeMatrix c x slot n) p.2
            (wick (nativeModeCovariance D c x slot colour n)
              (nativeModeMean D q c x slot colour n))).sum)

private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  classical
  exact h (X := PEmpty.{u+1}) emptyLattice emptyLattice_unit (fun _ => .P)
    (fun a => nomatch a) true .D (x := 1 / 2) (by norm_num) (by norm_num)
    (Or.inr ⟨rfl, rfl⟩) 0 (fun _ => 0) [] List.nodup_nil

def family : Registration arena.{u} (type_of% (@physical_marked_coefficient_assign.{u})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@physical_marked_coefficient_assign.{u}, complexFalse, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@physical_marked_coefficient_assign.{u}) (Realization complexSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMFixedChargeWick.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMFixedChargeWick.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMFixedChargeWick
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMFixedChargeWick
