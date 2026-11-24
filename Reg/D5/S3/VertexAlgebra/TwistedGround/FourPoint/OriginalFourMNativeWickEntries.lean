import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeWickEntries

/-! Dependent-family equality readouts for the physical inverse jet coefficients. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.TwistedGround
open LatticeGeneratingFieldLocality LatticeHalfFock
open FourPoint.OriginalFourMActualChart
open OriginalFourMOccupationTransport (flags)
open OriginalFourMPhysicalCovariance (relative)
open OriginalFourMPhysicalProduct (physicalMean)
open OriginalFourMSpatialWickPartition (nativeTaylor)
open OriginalFourMInverseJets (inverseJetWeight)
open OriginalFourMSlitMean (slitMeanEntry slitCovarianceEntry)
open OriginalGaussianSewnAnalytic (coefficient)
open private dLipCovarianceEntry dLipMeanEntry from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipChannel
open OriginalFourMNativeWickEntries
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)

open scoped BigOperators

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeWickEntries

private def witnessLattice : LatticeData where
  rank := 1
  G := 0
  symmetric := by intro i j; rfl
  even_diagonal := by intro i; simp

private def witnessColour : Fin witnessLattice.rank := ⟨0, by decide⟩

private theorem norm_parameter_half : ‖parameter .B ((1 / 2 : ℝ) : ℂ)‖ < 1 := by
  change ‖((1 / 2 : ℝ) : ℂ)‖ < 1
  rw [Complex.norm_real]
  norm_num

namespace ABCovariance

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ (D : LatticeData) {X : Type u}
    (upperA : Bool) (c : Chart) {x : ℝ} (_hx : 0 < x) (_hx₁ : x < 1)
    (_hc : c = .A ∨ c = .B) (_hr : ‖parameter c (x : ℂ)‖ < 1)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (i j : X),
    r.readout () ()
      (nativeTaylor D upperA c x slot colour n i j)
      ((relative c (slot i) * relative c (slot j)) *
        ∑ a ∈ Finset.range (n i + 1), ∑ b ∈ Finset.range (n j + 1),
          slitCovarianceEntry D (flags c (slot i)).1 (flags c (slot j)).1
            ((flags c (slot i)).2, colour i, a) ((flags c (slot j)).2, colour j, b)
            (parameter c x) * inverseJetWeight c x (slot i) (n i) a *
              inverseJetWeight c x (slot j) (n j) b)

private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact h witnessLattice (X := PUnit.{u+1}) true .B
    (x := 1 / 2) (by norm_num) (by norm_num) (Or.inr rfl) norm_parameter_half
    (fun _ => .P) (fun _ => witnessColour) (fun _ => 0) PUnit.unit PUnit.unit

def family : Registration arena.{u} (type_of% (@nativeTaylor_ab.{u})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@nativeTaylor_ab.{u}, complexFalse, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@nativeTaylor_ab.{u}) (Realization complexSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeWickEntries.ABCovariance.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeWickEntries.ABCovariance.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeWickEntries
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

end ABCovariance

namespace DCovariance

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ (D : LatticeData) {X : Type u} {x : ℝ} (_hx : 0 < x) (_hx₁ : x < 1)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (i j : X),
    r.readout () ()
      (nativeTaylor D true .D x slot colour n i j)
      ((relative .D (slot i) * relative .D (slot j)) *
        ∑ a ∈ Finset.range (n i + 1), ∑ b ∈ Finset.range (n j + 1),
          dLipCovarianceEntry D true (flags .D (slot i)).1 (flags .D (slot j)).1
            ((flags .D (slot i)).2, colour i, a) ((flags .D (slot j)).2, colour j, b)
            (parameter .D x) * inverseJetWeight .D x (slot i) (n i) a *
              inverseJetWeight .D x (slot j) (n j) b)

private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact h witnessLattice (X := PUnit.{u+1}) (x := 1 / 2) (by norm_num) (by norm_num)
    (fun _ => .P) (fun _ => witnessColour) (fun _ => 0) PUnit.unit PUnit.unit

def family : Registration arena.{u} (type_of% (@nativeTaylor_d.{u})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@nativeTaylor_d.{u}, complexFalse, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@nativeTaylor_d.{u}) (Realization complexSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeWickEntries.DCovariance.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeWickEntries.DCovariance.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeWickEntries
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DCovariance

namespace ABMean

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ (D : LatticeData) {X : Type u}
    (q : Charge D) (upperA : Bool) (c : Chart) {x : ℝ} (_hx : 0 < x) (_hx₁ : x < 1)
    (_hc : c = .A ∨ c = .B) (_hr : ‖parameter c (x : ℂ)‖ < 1)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (i : X),
    r.readout () ()
      (coefficient (n i) (fun u => physicalMean D q upperA c x slot colour i u *
        relative c (slot i)))
      (((bilinear D (unitCharge D (colour i)) q : ℂ) * relative c (slot i)) *
        ∑ a ∈ Finset.range (n i + 1),
          slitMeanEntry (flags c (slot i)).1 (flags c (slot i)).2 a (parameter c x) *
            inverseJetWeight c x (slot i) (n i) a)

private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact h witnessLattice (X := PUnit.{u+1}) 0 true .B
    (x := 1 / 2) (by norm_num) (by norm_num) (Or.inr rfl) norm_parameter_half
    (fun _ => .P) (fun _ => witnessColour) (fun _ => 0) PUnit.unit

def family : Registration arena.{u} (type_of% (@meanTaylor_ab.{u})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@meanTaylor_ab.{u}, complexFalse, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@meanTaylor_ab.{u}) (Realization complexSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeWickEntries.ABMean.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeWickEntries.ABMean.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeWickEntries
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

end ABMean

namespace DMean

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ (D : LatticeData) {X : Type u} (q : Charge D)
    {x : ℝ} (_hx : 0 < x) (_hx₁ : x < 1)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (i : X),
    r.readout () ()
      (coefficient (n i) (fun u => physicalMean D q true .D x slot colour i u *
        relative .D (slot i)))
      (((bilinear D (unitCharge D (colour i)) q : ℂ) * relative .D (slot i)) *
        ∑ a ∈ Finset.range (n i + 1),
          dLipMeanEntry true (flags .D (slot i)).1 (flags .D (slot i)).2 a (parameter .D x) *
            inverseJetWeight .D x (slot i) (n i) a)

private theorem rejectedLaw : ¬ arena.{u}.Law complexFalse := by
  intro h
  exact h witnessLattice (X := PUnit.{u+1}) 0 (x := 1 / 2) (by norm_num) (by norm_num)
    (fun _ => .P) (fun _ => witnessColour) (fun _ => 0) PUnit.unit

def family : Registration arena.{u} (type_of% (@meanTaylor_d.{u})) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@meanTaylor_d.{u}, complexFalse, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@meanTaylor_d.{u}) (Realization complexSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeWickEntries.DMean.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeWickEntries.DMean.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeWickEntries
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DMean

end Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeWickEntries
