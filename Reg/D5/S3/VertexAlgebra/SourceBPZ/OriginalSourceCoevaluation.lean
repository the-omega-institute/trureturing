import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeInvolution
open LatticeAllStateField MvPolynomial
open SourceBPZ.OriginalSourcePairing SourceBPZ.OriginalSourceCoevaluation

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i j; rfl
  even_diagonal := by intro i; exact Fin.elim0 i

private theorem emptyUnit : IsUnit emptyLattice.G.det := by
  simp [emptyLattice]

private theorem emptyPositive : Matrix.PosDef (emptyLattice.G.map (Int.cast : ℤ → ℝ)) := by
  constructor
  · ext i j
    exact Fin.elim0 i
  · intro x hx
    exact (hx (by ext i; exact Fin.elim0 i)).elim

private def vacuumTest (D : LatticeData) : Module.Dual ℂ (Carrier D) :=
  sourcePairing D (vacuum D)

private def fixedVacuumTest (D : LatticeData) :
    Module.Dual ℂ ↥(grade D 0 ⊓ fixedSpace D) :=
  (vacuumTest D).comp (grade D 0 ⊓ fixedSpace D).subtype

private theorem fixedVacuumTest_one (D : LatticeData) :
    fixedVacuumTest D (gradeVacuum D) = 1 := sourcePairing_vacuum D

namespace Coefficient
structure Params where
  D : LatticeData
  a : Label D

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Params
    (fun p => Carrier p.D) (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ p v => sourcePairing p.D (dualCarrierBasis p.D p.a) v)
  (fun e => nomatch e)

def bad : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Label D) (v : Carrier D),
    r.readout () ⟨D, a⟩ v = carrierCoeffEquiv D v a

theorem sourceBridge : (type_of% (@dualCarrierBasis_pairing)) ↔ arena.Law actual := Iff.rfl

private theorem rejectedLaw : ¬ arena.Law bad := by
  intro h
  have he := h emptyLattice emptyUnit (0,0) (vacuum emptyLattice)
  change (0 : ℂ) = ((vacuum emptyLattice) 0).coeff 0 at he
  simpa [vacuum] using he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨emptyLattice, (0,0)⟩, 0, vacuum emptyLattice, ?_⟩
  change sourcePairing emptyLattice (dualCarrierBasis emptyLattice (0,0)) 0 ≠
    sourcePairing emptyLattice (dualCarrierBasis emptyLattice (0,0)) (vacuum emptyLattice)
  rw [dualCarrierBasis_pairing _ emptyUnit, dualCarrierBasis_pairing _ emptyUnit]
  change ((0 : Carrier emptyLattice) 0).coeff 0 ≠ ((vacuum emptyLattice) 0).coeff 0
  simp [vacuum]

def family : Registration arena (type_of% (@dualCarrierBasis_pairing)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp (@dualCarrierBasis_pairing), bad, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@dualCarrierBasis_pairing)
    (type_of% (realize signature actual.readout actual.anchor)) Params Unit where
  unitName := `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.dualCarrierBasis_pairing.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.Coefficient.family
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
    owner := `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Coefficient


namespace Energy

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature LatticeData
    (fun p => Label p) (fun p => Carrier p)

def actual : Realization signature := realize signature
  (fun _ p a => dualCarrierBasis p a) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (a : Label D), r.readout () D a ∈ grade D (energy D a)

theorem sourceBridge : (type_of% (@dualCarrierBasis_mem_grade)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := sourceBridge.mp (@dualCarrierBasis_mem_grade)

/-- The original telescope and readout are retained. Variation, sensitivity,
actual observational dependence and native binding remain required. -/
theorem auditAssembly : Nonempty (Variation arena actual → Sensitivity arena actual →
    ObservationalDependence signature actual → Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@dualCarrierBasis_mem_grade) (Realization signature) LatticeData Unit) :=
  ⟨fun variation sensitivity dependence => {
    unitName := `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.dualCarrierBasis_mem_grade.__information_unit
    realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.Energy.family
    realizationSource := none
    generated := false
    arena := .source ⟨arena⟩
    objectArena := .source ⟨arena⟩
    catalog := Lean.Name.anonymous
    localNames := false
    realization := .source arena ⟨{
      actual := actual
      bridge := sourceBridge
      variation := variation
      sensitivity := sensitivity
      dependence := dependence }⟩
    correspondence := { stage := .evidence, objectStage := .evidence }
    bundleNonempty := .absent
    readout := some (realize signature actual.readout actual.anchor)
    variation := .absent
    sensitivity := .absent
    partialSensitivity := none
    escapeFrom := none
    sourceSelection := none
    continuation := .unknown
    familyRecord := none
    options := #[] }⟩

#print axioms sourceBridge
end Energy

namespace Evaluation
structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))
  h : ℤ
  f : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D)

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Params
    (fun p => ↥(grade p.D p.h ⊓ fixedSpace p.D)) (fun p => ℂ)

def actual : Realization signature := realize signature
  (fun _ p x => sourcePairing p.D (coevaluation p.D p.h p.f).val x.val) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ)
    (f : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D))
    (x : ↥(grade D h ⊓ fixedSpace D)),
    r.readout () ⟨D, hu, hD, h, f⟩ x = f x

theorem sourceBridge : (type_of% (@coevaluation_pairing)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := sourceBridge.mp (@coevaluation_pairing)


def bad : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem rejectedLaw : ¬ arena.Law bad := by
  intro h
  have he := h emptyLattice emptyUnit emptyPositive 0 0 0
  exact one_ne_zero he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨emptyLattice, emptyUnit, emptyPositive, 0, fixedVacuumTest emptyLattice⟩,
    0, gradeVacuum emptyLattice, ?_⟩
  change sourcePairing _ (coevaluation _ _ _).val (0 : Carrier _) ≠
    sourcePairing _ (coevaluation _ _ _).val (gradeVacuum _).val
  rw [coevaluation_pairing _ emptyUnit emptyPositive]
  simp only [map_zero, fixedVacuumTest_one]
  exact zero_ne_one

def family : Registration arena (type_of% (@coevaluation_pairing)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨source_actual, bad, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@coevaluation_pairing) (type_of% (realize signature actual.readout actual.anchor)) Params Unit where
    unitName := `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.coevaluation_pairing.__information_unit
    realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.Evaluation.family
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
    sourceSelection := none
    continuation := .unknown
    familyRecord := none
    options := #[]


#print axioms family
end Evaluation

namespace Contraction
structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))
  h : ℤ
  f : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D)
  x : ↥(grade D h ⊓ fixedSpace D)
  hx : ∀ y : ↥(grade D h ⊓ fixedSpace D), sourcePairing D x.val y.val = f y

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Params
    (fun p => Module.Dual ℂ ↥(grade p.D p.h ⊓ fixedSpace p.D)) (fun p => ℂ)

def actual : Realization signature := realize signature
  (fun _ p g => g p.x) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ)
    (f g : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D))
    (x : ↥(grade D h ⊓ fixedSpace D))
    (hx : ∀ y : ↥(grade D h ⊓ fixedSpace D), sourcePairing D x.val y.val = f y),
    r.readout () ⟨D, hu, hD, h, f, x, hx⟩ g =
      ∑ᶠ a : EnergyFiber D h, f (fixedFrame D h a) * g (fixedDualFrame D h a)

theorem sourceBridge : (type_of% (@inverse_contraction)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := sourceBridge.mp (@inverse_contraction)


def bad : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem rejectedLaw : ¬ arena.Law bad := by
  intro h
  have he := h emptyLattice emptyUnit emptyPositive 0 0 0 0 (by intro y; simp)
  have ht := inverse_contraction emptyLattice emptyUnit emptyPositive 0 0 0 0 (by intro y; simp)
  exact one_ne_zero (he.trans ht.symm)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨emptyLattice, emptyUnit, emptyPositive, 0, fixedVacuumTest emptyLattice,
    gradeVacuum emptyLattice, fun _ => rfl⟩, 0, fixedVacuumTest emptyLattice, ?_⟩
  change (0 : ℂ) ≠ fixedVacuumTest emptyLattice (gradeVacuum emptyLattice)
  rw [fixedVacuumTest_one]
  exact zero_ne_one

def family : Registration arena (type_of% (@inverse_contraction)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨source_actual, bad, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@inverse_contraction) (type_of% (realize signature actual.readout actual.anchor)) Params Unit where
    unitName := `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.inverse_contraction.__information_unit
    realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.Contraction.family
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
    sourceSelection := none
    continuation := .unknown
    familyRecord := none
    options := #[]


#print axioms family
end Contraction

namespace HalfAverage
structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))
  h : ℤ
  f : Module.Dual ℂ (Carrier D)
  x : ↥(grade D h ⊓ fixedSpace D)
  hx : ∀ y : ↥(grade D h ⊓ fixedSpace D), sourcePairing D x.val y.val = f y.val

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Params
    (fun p => Module.Dual ℂ (Carrier p.D)) (fun p => ℂ)

def actual : Realization signature := realize signature
  (fun _ p g => g p.x.val) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ)
    (f g : Module.Dual ℂ (Carrier D)) (x : ↥(grade D h ⊓ fixedSpace D))
    (hx : ∀ y : ↥(grade D h ⊓ fixedSpace D), sourcePairing D x.val y.val = f y.val),
    r.readout () ⟨D, hu, hD, h, f, x, hx⟩ g = (2 : ℂ)⁻¹ *
      ∑ᶠ a : EnergyFiber D h,
        (f (carrierBasis D a.val) + f (theta D (carrierBasis D a.val))) *
          g (dualCarrierBasis D a.val)

theorem sourceBridge : (type_of% (@inverse_contraction_half_average)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := sourceBridge.mp (@inverse_contraction_half_average)


def bad : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem rejectedLaw : ¬ arena.Law bad := by
  intro h
  have he := h emptyLattice emptyUnit emptyPositive 0 0 0 0 (by intro y; simp)
  have ht := inverse_contraction_half_average emptyLattice emptyUnit emptyPositive 0 0 0 0 (by intro y; simp)
  exact one_ne_zero (he.trans ht.symm)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨emptyLattice, emptyUnit, emptyPositive, 0, vacuumTest emptyLattice,
    gradeVacuum emptyLattice, fun _ => rfl⟩, 0, vacuumTest emptyLattice, ?_⟩
  change (0 : ℂ) ≠ sourcePairing emptyLattice (vacuum emptyLattice) (vacuum emptyLattice)
  rw [sourcePairing_vacuum]
  exact zero_ne_one

def family : Registration arena (type_of% (@inverse_contraction_half_average)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨source_actual, bad, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@inverse_contraction_half_average) (type_of% (realize signature actual.readout actual.anchor)) Params Unit where
    unitName := `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.inverse_contraction_half_average.__information_unit
    realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.HalfAverage.family
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
    sourceSelection := none
    continuation := .unknown
    familyRecord := none
    options := #[]


#print axioms family
end HalfAverage

namespace Negative
structure Params where
  D : LatticeData
  hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))
  h : ℤ
  hh : h < 0

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Params
    (fun p => Module.Dual ℂ ↥(grade p.D p.h ⊓ fixedSpace p.D)) (fun p => ↥(grade p.D p.h ⊓ fixedSpace p.D))

def actual : Realization signature := realize signature
  (fun _ p f => coevaluation p.D p.h f) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (h : ℤ) (hh : h < 0) (f : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D)),
    r.readout () ⟨D, hD, h, hh⟩ f = 0

theorem sourceBridge : (type_of% (@coevaluation_negative)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := sourceBridge.mp (@coevaluation_negative)

/-- The original telescope and readout are retained. Variation, sensitivity,
actual observational dependence and native binding remain required. -/
theorem auditAssembly : Nonempty (Variation arena actual → Sensitivity arena actual →
    ObservationalDependence signature actual → Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@coevaluation_negative) (Realization signature) Params Unit) :=
  ⟨fun variation sensitivity dependence => {
    unitName := `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.coevaluation_negative.__information_unit
    realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.Negative.family
    realizationSource := none
    generated := false
    arena := .source ⟨arena⟩
    objectArena := .source ⟨arena⟩
    catalog := Lean.Name.anonymous
    localNames := false
    realization := .source arena ⟨{
      actual := actual
      bridge := sourceBridge
      variation := variation
      sensitivity := sensitivity
      dependence := dependence }⟩
    correspondence := { stage := .evidence, objectStage := .evidence }
    bundleNonempty := .absent
    readout := some (realize signature actual.readout actual.anchor)
    variation := .absent
    sensitivity := .absent
    partialSensitivity := none
    escapeFrom := none
    sourceSelection := none
    continuation := .unknown
    familyRecord := none
    options := #[] }⟩

#print axioms sourceBridge
end Negative

namespace Vacuum
structure Params where
  D : LatticeData
  hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Params
    (fun p => Module.Dual ℂ ↥(grade p.D 0 ⊓ fixedSpace p.D)) (fun p => ↥(grade p.D 0 ⊓ fixedSpace p.D))

def actual : Realization signature := realize signature
  (fun _ p f => coevaluation p.D 0 f) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (f : Module.Dual ℂ ↥(grade D 0 ⊓ fixedSpace D)),
    r.readout () ⟨D, hD⟩ f = f (gradeVacuum D) • gradeVacuum D

theorem sourceBridge : (type_of% (@coevaluation_vacuum)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := sourceBridge.mp (@coevaluation_vacuum)


def bad : Realization signature := realize signature (fun _ p _ => gradeVacuum p.D) (fun e => nomatch e)

private theorem rejectedLaw : ¬ arena.Law bad := by
  intro h
  have he := h emptyLattice emptyPositive 0
  change gradeVacuum emptyLattice = (0 : ℂ) • gradeVacuum emptyLattice at he
  rw [zero_smul] at he
  have hc := congrArg (fixedVacuumTest emptyLattice) he
  rw [fixedVacuumTest_one, map_zero] at hc
  exact one_ne_zero hc

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨emptyLattice, emptyPositive⟩, 0, fixedVacuumTest emptyLattice, ?_⟩
  change coevaluation _ 0 0 ≠ coevaluation _ 0 (fixedVacuumTest emptyLattice)
  rw [coevaluation_vacuum _ emptyPositive, coevaluation_vacuum _ emptyPositive,
    LinearMap.zero_apply, zero_smul, fixedVacuumTest_one, one_smul]
  intro he
  have hc := congrArg (fixedVacuumTest emptyLattice) he
  rw [map_zero, fixedVacuumTest_one] at hc
  exact zero_ne_one hc

def family : Registration arena (type_of% (@coevaluation_vacuum)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨source_actual, bad, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@coevaluation_vacuum) (type_of% (realize signature actual.readout actual.anchor)) Params Unit where
    unitName := `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.coevaluation_vacuum.__information_unit
    realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.Vacuum.family
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
    sourceSelection := none
    continuation := .unknown
    familyRecord := none
    options := #[]


#print axioms family
end Vacuum

namespace Signed
structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))
  h : ℤ
  f : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D)
  x : ↥(grade D h ⊓ fixedSpace D)
  hx : ∀ y : ↥(grade D h ⊓ fixedSpace D), sourcePairing D x.val y.val = f y

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Params
    (fun p => Module.Dual ℂ (Carrier p.D)) (fun p => ℂ)

def actual : Realization signature := realize signature
  (fun _ p g => g p.x.val) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ)
    (f : Module.Dual ℂ ↥(grade D h ⊓ fixedSpace D))
    (g : Module.Dual ℂ (Carrier D))
    (x : ↥(grade D h ⊓ fixedSpace D))
    (hx : ∀ y : ↥(grade D h ⊓ fixedSpace D), sourcePairing D x.val y.val = f y),
    r.readout () ⟨D, hu, hD, h, f, x, hx⟩ g =
      if hh : h < 0 then 0 else if hz : h = 0 then
        f (hz.symm ▸ gradeVacuum D) * g (vacuum D) else
        ∑ᶠ a : EnergyFiber D h, f (fixedFrame D h a) * g (fixedDualFrame D h a).val

theorem sourceBridge : (type_of% (@inverse_contraction_signed)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := sourceBridge.mp (@inverse_contraction_signed)


def bad : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem rejectedLaw : ¬ arena.Law bad := by
  intro h
  have he := h emptyLattice emptyUnit emptyPositive 0 0 0 0 (by intro y; simp)
  have ht := inverse_contraction_signed emptyLattice emptyUnit emptyPositive 0 0 0 0 (by intro y; simp)
  exact one_ne_zero (he.trans ht.symm)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨emptyLattice, emptyUnit, emptyPositive, 0, fixedVacuumTest emptyLattice,
    gradeVacuum emptyLattice, fun _ => rfl⟩, 0, vacuumTest emptyLattice, ?_⟩
  change (0 : ℂ) ≠ sourcePairing emptyLattice (vacuum emptyLattice) (vacuum emptyLattice)
  rw [sourcePairing_vacuum]
  exact zero_ne_one

def family : Registration arena (type_of% (@inverse_contraction_signed)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨source_actual, bad, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual bad rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@inverse_contraction_signed) (type_of% (realize signature actual.readout actual.anchor)) Params Unit where
    unitName := `D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.inverse_contraction_signed.__information_unit
    realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation.Signed.family
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
    sourceSelection := none
    continuation := .unknown
    familyRecord := none
    options := #[]


#print axioms family
end Signed

end Reg.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
