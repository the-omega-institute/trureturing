import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccurrenceWick
import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic

/-! Readouts for the physical marked coefficient and its charge sum. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.TwistedGround
open LatticeGeneratingFieldLocality
open FourPoint.OriginalFourMActualChart
open ActualLeechHyperbolic (leechData leech_spec)
open OriginalFourMPhysicalCovariance (relative)
open OriginalFourMPhysicalProduct (physicalChargeSummand physicalMean physicalProduct)
open OriginalFourMChartProduct (chartTau chartPeriod)
open OriginalFourMSpatialWick (spatialCoefficient)
open NativeAffineExternalCoefficient (coordinateJet)
open AffineOccurrenceWick (wick)
open AffineWickConvolution (partitions)
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMOccurrenceWick
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)
open LeanInformationAudit
open scoped Classical

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccurrenceWick

private def sampleColour : Fin leechData.rank := Fin.cast leech_spec.1.symm 0

namespace physical_mark_jet_partition

abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ {X : Type u} [Fintype X] [DecidableEq X] (D : LatticeData) (slot : X → Puncture)
    (colour : X → Fin D.rank) (upperA : Bool) (c : Chart) (x : ℝ)
    (q : Charge D) (l : List X) (u : X → ℂ),
    R.readout () ()
      (coordinateJet l (fun v => physicalChargeSummand D slot colour upperA c x q (Sum.elim u v)) 0)
      (Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x * (bilinear D q q : ℂ) / 2) *
        ((partitions l).map fun p => wick (correctionEntry D c x slot colour u) 0 p.1 *
          wick (nativeEntry D upperA c x slot colour u)
            (fun i => physicalMean D q upperA c x slot colour i (u i) * relative c (slot i)) p.2).sum)

private theorem rejected_fails : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact h (X := PUnit.{u+1}) leechData
    (fun _ => .P) (fun _ => sampleColour) true .A 0 0 [] 0

def family : Registration arena (type_of% (@physical_mark_jet_partition.{u})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@physical_mark_jet_partition, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@physical_mark_jet_partition.{u}) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccurrenceWick.physical_mark_jet_partition.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccurrenceWick.physical_mark_jet_partition.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccurrenceWick
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

end physical_mark_jet_partition

namespace physical_marked_coefficient_partition

abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ {X : Type u} [Fintype X] [DecidableEq X] (D : LatticeData)
    (slot : X → Puncture) (colour : X → Fin D.rank) (upperA : Bool) (c : Chart) (x : ℝ)
    (q : Charge D) (n : X → ℕ) (l : List X) (hl : l.Nodup),
    R.readout () ()
      (spatialCoefficient (Sum.elim n (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl)
        (physicalChargeSummand D slot colour upperA c x q) 0)
      (Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x * (bilinear D q q : ℂ) / 2) *
        spatialCoefficient n l (fun u =>
          ((partitions l).map fun p => wick (correctionEntry D c x slot colour u) 0 p.1 *
            wick (nativeEntry D upperA c x slot colour u)
              (fun i => physicalMean D q upperA c x slot colour i (u i) *
                relative c (slot i)) p.2).sum) 0)

private theorem rejected_fails : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact h (X := PUnit.{u+1}) leechData
    (fun _ => .P) (fun _ => sampleColour) true .A 0 0 (fun _ => 0) [] (by simp)

def family : Registration arena (type_of% (@physical_marked_coefficient_partition.{u})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@physical_marked_coefficient_partition, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@physical_marked_coefficient_partition.{u}) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccurrenceWick.physical_marked_coefficient_partition.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccurrenceWick.physical_marked_coefficient_partition.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccurrenceWick
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end physical_marked_coefficient_partition

namespace physical_marked_partition_hasSum

open LatticeDiscriminantTheta (gramReal)
open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge reduceCharge)
open OriginalFourMChartProduct (chart_charge_data)

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ z => Complex.exp z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X : Type u} [Fintype X] [DecidableEq X] (D : LatticeData)
    (hu : IsUnit D.G.det) (hD : (gramReal D).PosDef)
    (slot : X → Puncture) (colour : X → Fin D.rank) (upperA : Bool) (c : Chart) {x : ℝ}
    (hx : 0 < x) (hx₁ : x < 1) (a : ModTwoCharge D) (n : X → ℕ) (l : List X)
    (hl : l.Nodup),
    HasSum (fun q : {q : Charge D // reduceCharge D q = a} =>
      (chartPeriod upperA c x ^ (12 : ℕ))⁻¹ *
        (R.readout () () ((Real.pi : ℂ) * Complex.I * chartTau upperA c x *
          (bilinear D q.val q.val : ℂ) / 2) *
        spatialCoefficient n l (fun u =>
          ((partitions l).map fun p => wick (correctionEntry D c x slot colour u) 0 p.1 *
            wick (nativeEntry D upperA c x slot colour u)
              (fun i => physicalMean D q.val upperA c x slot colour i (u i) *
                relative c (slot i)) p.2).sum) 0))
      (spatialCoefficient (Sum.elim n (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl)
        (fun z => physicalProduct D hu slot colour upperA x c a
          (z ∘ Sum.inl) (z ∘ Sum.inr)) 0)

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i; exact Fin.elim0 i
  even_diagonal := by intro i; exact Fin.elim0 i

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  classical
  let D := emptyLattice
  have hu : IsUnit D.G.det := by
    change IsUnit (0 : Matrix (Fin 0) (Fin 0) ℤ).det
    simp
  have hD : (gramReal D).PosDef := by
    refine ⟨?_, ?_⟩
    · ext i j
      exact Fin.elim0 i
    · intro v hv
      exfalso
      apply hv
      ext i
      exact Fin.elim0 i
  let slot : PEmpty.{u+1} → Puncture := fun i => nomatch i
  let colour : PEmpty.{u+1} → Fin D.rank := fun i => nomatch i
  let x : ℝ := 3 / 4
  have hx : 0 < x := by norm_num [x]
  have hx₁ : x < 1 := by norm_num [x]
  let a := reduceCharge D 0
  let q₀ : {q : Charge D // reduceCharge D q = a} := ⟨0, rfl⟩
  let n : PEmpty.{u+1} → ℕ := 0
  let l : List PEmpty.{u+1} := []
  have hl : l.Nodup := List.nodup_nil
  have hactual := physical_marked_partition_hasSum D hu hD slot colour true .A hx hx₁ a n l hl
  have hbad := h D hu hD slot colour true .A hx hx₁ a n l hl
  change HasSum (fun q : {q : Charge D // reduceCharge D q = a} =>
    (chartPeriod true .A x ^ (12 : ℕ))⁻¹ * (0 * _)) _ at hbad
  simp only [zero_mul, mul_zero] at hbad
  let weight := (chartPeriod true .A x ^ (12 : ℕ))⁻¹
  have hterm :
      (fun q : {q : Charge D // reduceCharge D q = a} =>
        (chartPeriod true .A x ^ (12 : ℕ))⁻¹ *
          (Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau true .A x *
            (bilinear D q.val q.val : ℂ) / 2) *
          spatialCoefficient n l (fun u =>
            ((partitions l).map fun p => wick (correctionEntry D .A x slot colour u) 0 p.1 *
              wick (nativeEntry D true .A x slot colour u)
                (fun i => physicalMean D q.val true .A x slot colour i (u i) *
                  relative .A (slot i)) p.2).sum) 0)) =
      (fun q => if q = q₀ then weight else 0) := by
    funext q
    have hq : q = q₀ := Subtype.ext (funext fun i => Fin.elim0 i)
    rw [hq, if_pos rfl]
    simp [weight, q₀, l, bilinear, spatialCoefficient, partitions, wick]
  rw [hterm] at hactual
  have hnonzero : weight ≠ 0 :=
    inv_ne_zero (pow_ne_zero 12 (chart_charge_data true .A hx hx₁).1)
  exact hnonzero (((hasSum_ite_eq q₀ weight).unique hactual).trans (hbad.unique hasSum_zero))

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, (Real.pi : ℂ) * Complex.I, ?_⟩
  change Complex.exp 0 ≠ Complex.exp ((Real.pi : ℂ) * Complex.I)
  rw [Complex.exp_zero, Complex.exp_pi_mul_I]
  norm_num

def family : Registration arena (type_of% (@physical_marked_partition_hasSum.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@physical_marked_partition_hasSum, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@physical_marked_partition_hasSum.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccurrenceWick.physical_marked_partition_hasSum.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccurrenceWick.physical_marked_partition_hasSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => Complex.exp z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccurrenceWick
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "fn", "arg", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end physical_marked_partition_hasSum

end Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMOccurrenceWick
