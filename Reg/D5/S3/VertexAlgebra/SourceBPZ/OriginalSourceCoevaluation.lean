import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation

/-!
Source-owned typed attempts for the original Q coevaluation endpoints.
The actual readouts retain the source carrier, inverse Gram/factorial vectors,
projected frames and all integer grades. No finite-state surrogate is used.
DependentFamily.realize uses the existing Reg.Support.DependentFamily enrollment.

A source bridge and positive law do not establish native source reconstruction,
lawful template binding or declared_validated status. The conditional assemblies
retain missing whole-family variation and observational dependence as premises;
they supply neither premise. Sensitivity follows from supplied variation for
these single-role, anchor-free signatures. Continuation remains unknown.
Unfinished registration and native binding are tracked by issue #24182.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeInvolution
open _root_.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing
open _root_.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i j; rfl
  even_diagonal := by intro i; exact Fin.elim0 i

private theorem emptyUnit : IsUnit emptyLattice.G.det := by
  simp [emptyLattice]

namespace DualCarrierPairing
structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  a : Label D

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Params (fun p => Carrier p.D) (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ p v => sourcePairing p.D (dualCarrierBasis p.D p.a) v)
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Label D) (v : Carrier D),
    r.readout () ⟨D, hu, a⟩ v = carrierCoeffEquiv D v a

theorem sourceBridge : (type_of% (@dualCarrierBasis_pairing)) ↔
    arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := sourceBridge.mp (@dualCarrierBasis_pairing)

def shifted : Realization signature := realize signature
  (fun i p v => actual.readout i p v + 1) (fun e => nomatch e)

private theorem rejectedLaw : ¬ arena.Law shifted := by
  intro h
  have he := h emptyLattice emptyUnit (0, 0) 0
  change sourcePairing emptyLattice (dualCarrierBasis emptyLattice (0, 0)) 0 + 1 =
    carrierCoeffEquiv emptyLattice 0 (0, 0) at he
  simpa using he

theorem variation : Variation arena actual := ⟨source_actual, shifted, rejectedLaw⟩

theorem sensitivity : Sensitivity arena actual :=
  Reg.Support.SingleDependentReadout.sensitivity arena.Law actual shifted rejectedLaw

theorem dependence : ObservationalDependence signature actual := by
  intro i
  let p : Params := ⟨emptyLattice, emptyUnit, (0, 0)⟩
  refine ⟨p, 0, carrierBasis p.D p.a, ?_⟩
  intro he
  change sourcePairing p.D (dualCarrierBasis p.D p.a) 0 =
    sourcePairing p.D (dualCarrierBasis p.D p.a) (carrierBasis p.D p.a) at he
  rw [map_zero, dualCarrierBasis_pairing p.D p.hu] at he
  have hb : carrierCoeffEquiv p.D (carrierBasis p.D p.a) =
      Finsupp.single p.a 1 := (carrierBasis p.D).repr_self p.a
  rw [hb, Finsupp.single_eq_same] at he
  exact zero_ne_one he

def family : Registration arena (type_of% (@dualCarrierBasis_pairing)) where
  actual := actual
  bridge := sourceBridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

/-- Typed source submission; native reconstruction and template binding remain
separate obligations, even with the family proof terms supplied. -/
def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@dualCarrierBasis_pairing) (Realization signature) Params Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.dualCarrierBasis_pairing "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.DualCarrierPairing.family
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
  escapeFrom := some (⟨emptyLattice, emptyUnit, (0, 0)⟩ : Params)
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DualCarrierPairing

namespace DualCarrierGrade
structure Params where
  D : LatticeData

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Params (fun p => Label p.D) (fun p => Carrier p.D)

def actual : Realization signature := realize signature
  (fun _ p a => dualCarrierBasis p.D a) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (a : Label D),
    r.readout () ⟨D⟩ a ∈ grade D (energy D a)

theorem sourceBridge : (type_of% (@dualCarrierBasis_mem_grade)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := sourceBridge.mp (@dualCarrierBasis_mem_grade)

/-- A supplied whole-family counterexample suffices for the one registered role.
This implication does not supply the missing counterexample. -/
theorem sensitivity_of_variation (h : Variation arena actual) : Sensitivity arena actual := by
  rcases h.2 with ⟨bad, hbad⟩
  exact Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad hbad

def family (hvariation : Variation arena actual)
    (hdependence : ObservationalDependence signature actual) :
    Registration arena (type_of% (@dualCarrierBasis_mem_grade)) where
  actual := actual
  bridge := sourceBridge
  variation := hvariation
  sensitivity := sensitivity_of_variation hvariation
  dependence := hdependence

/-- Conditional assembly only: variation and actual observational dependence
remain unprovided. This is not a closed registration or a validation claim. -/
theorem auditAssembly : Nonempty (Variation arena actual →
    ObservationalDependence signature actual →
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@dualCarrierBasis_mem_grade) (Realization signature) Params Unit) :=
  ⟨fun hvariation hdependence => {
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.dualCarrierBasis_mem_grade "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.DualCarrierGrade.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family hvariation hdependence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }⟩

end DualCarrierGrade

namespace FixedGradePairing
structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))
  h : ℤ
  f : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D)

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Params (fun p => ↥(grade p.D p.h ⊓ fixedSpace p.D)) (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ p x => sourcePairing p.D (representFixedGrade p.D p.hD p.h p.f).val x.val)
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (h : ℤ) (f : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D))
    (x : ↥(grade D h ⊓ fixedSpace D)),
    r.readout () ⟨D, hu, hD, h, f⟩ x = f x

theorem sourceBridge : (type_of% (@representFixedGrade_pairing)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := sourceBridge.mp (@representFixedGrade_pairing)

/-- A supplied whole-family counterexample suffices for the one registered role.
This implication does not supply the missing counterexample. -/
theorem sensitivity_of_variation (h : Variation arena actual) : Sensitivity arena actual := by
  rcases h.2 with ⟨bad, hbad⟩
  exact Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad hbad

def family (hvariation : Variation arena actual)
    (hdependence : ObservationalDependence signature actual) :
    Registration arena (type_of% (@representFixedGrade_pairing)) where
  actual := actual
  bridge := sourceBridge
  variation := hvariation
  sensitivity := sensitivity_of_variation hvariation
  dependence := hdependence

/-- Conditional assembly only: variation and actual observational dependence
remain unprovided. This is not a closed registration or a validation claim. -/
theorem auditAssembly : Nonempty (Variation arena actual →
    ObservationalDependence signature actual →
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@representFixedGrade_pairing) (Realization signature) Params Unit) :=
  ⟨fun hvariation hdependence => {
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.representFixedGrade_pairing "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.FixedGradePairing.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family hvariation hdependence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }⟩

end FixedGradePairing

namespace FixedGradeUnique
structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))
  h : ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Params (fun p => Module.Dual ℂ ↥(grade p.D p.h ⊓ fixedSpace p.D))
    (fun p => ↥(grade p.D p.h ⊓ fixedSpace p.D))

def actual : Realization signature := realize signature
  (fun _ p f => representFixedGrade p.D p.hD p.h f) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (h : ℤ) (f : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D))
    (x : ↥(grade D h ⊓ fixedSpace D))
    (hx : ∀ y : ↥(grade D h ⊓ fixedSpace D), sourcePairing D x.val y.val = f y),
    x = r.readout () ⟨D, hu, hD, h⟩ f

theorem sourceBridge : (type_of% (@representFixedGrade_unique)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := sourceBridge.mp (@representFixedGrade_unique)

/-- A supplied whole-family counterexample suffices for the one registered role.
This implication does not supply the missing counterexample. -/
theorem sensitivity_of_variation (h : Variation arena actual) : Sensitivity arena actual := by
  rcases h.2 with ⟨bad, hbad⟩
  exact Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad hbad

def family (hvariation : Variation arena actual)
    (hdependence : ObservationalDependence signature actual) :
    Registration arena (type_of% (@representFixedGrade_unique)) where
  actual := actual
  bridge := sourceBridge
  variation := hvariation
  sensitivity := sensitivity_of_variation hvariation
  dependence := hdependence

/-- Conditional assembly only: variation and actual observational dependence
remain unprovided. This is not a closed registration or a validation claim. -/
theorem auditAssembly : Nonempty (Variation arena actual →
    ObservationalDependence signature actual →
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@representFixedGrade_unique) (Realization signature) Params Unit) :=
  ⟨fun hvariation hdependence => {
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.representFixedGrade_unique "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.FixedGradeUnique.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family hvariation hdependence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }⟩

end FixedGradeUnique

namespace FixedContraction
structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))
  h : ℤ
  f : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D)

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Params (fun p => Module.Dual ℂ ↥(grade p.D p.h ⊓ fixedSpace p.D)) (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ p g => ∑ᶠ a : EnergyFiber p.D p.h,
    p.f (fixedFrame p.D p.h a) * g (fixedDualFrame p.D p.h a))
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (h : ℤ) (f g : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D)),
    r.readout () ⟨D, hu, hD, h, f⟩ g =
      (∑ᶠ a : EnergyFiber D h,
        g (fixedFrame D h a) * f (fixedDualFrame D h a))

theorem sourceBridge : (type_of% (@fixed_contraction_comm)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := sourceBridge.mp (@fixed_contraction_comm)

/-- A supplied whole-family counterexample suffices for the one registered role.
This implication does not supply the missing counterexample. -/
theorem sensitivity_of_variation (h : Variation arena actual) : Sensitivity arena actual := by
  rcases h.2 with ⟨bad, hbad⟩
  exact Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad hbad

def family (hvariation : Variation arena actual)
    (hdependence : ObservationalDependence signature actual) :
    Registration arena (type_of% (@fixed_contraction_comm)) where
  actual := actual
  bridge := sourceBridge
  variation := hvariation
  sensitivity := sensitivity_of_variation hvariation
  dependence := hdependence

/-- Conditional assembly only: variation and actual observational dependence
remain unprovided. This is not a closed registration or a validation claim. -/
theorem auditAssembly : Nonempty (Variation arena actual →
    ObservationalDependence signature actual →
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@fixed_contraction_comm) (Realization signature) Params Unit) :=
  ⟨fun hvariation hdependence => {
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.fixed_contraction_comm "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.FixedContraction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family hvariation hdependence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }⟩

end FixedContraction

end Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
