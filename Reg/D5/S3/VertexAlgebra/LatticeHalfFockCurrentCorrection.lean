import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

structure CorrectionParameters where
  lattice : LatticeData
  charge : Charge lattice
  index : Index lattice

def correctionSignature : Signature where
  Params := CorrectionParameters
  State parameter := Oscillator parameter.lattice × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := Oscillator parameter.lattice × Oscillator parameter.lattice
  Anchor := Empty
  finiteAnchor := inferInstance

def correctionReadout : Realization correctionSignature :=
  realize correctionSignature (fun _ parameter state =>
    (MvPolynomial.pderiv parameter.index
        (Corr parameter.lattice parameter.charge state.1 state.2),
      Corr parameter.lattice parameter.charge (MvPolynomial.pderiv parameter.index state.1) state.2))
    (fun empty => nomatch empty)

def correctionArena : Arena where
  signature := correctionSignature
  Law readout := ∀ parameter state,
    (readout.readout () parameter state).1 = (readout.readout () parameter state).2

theorem correctionBridge : (type_of% (@Corr_partial)) ↔ correctionArena.Law correctionReadout := by
  constructor
  · intro source parameter state
    exact source parameter.lattice parameter.charge parameter.index state.1 state.2
  · intro law lattice charge index polynomial shift
    exact law ⟨lattice, charge, index⟩ ⟨polynomial, shift⟩

def correctionEscapeFrom := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.Corr
def correctionContinuation : Contract.Continuation Unit := .unknown
abbrev correctionRealizationObligation := Registration correctionArena (type_of% (@Corr_partial))
abbrev correctionContractObligation := Contract.Registration (@Corr_partial)
  (type_of% correctionReadout) (type_of% correctionEscapeFrom) Unit

private theorem indexFamily_nonempty : Nonempty (Σ lattice : LatticeData, Index lattice) := by
  rcases _root_.Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.MatchingDerivative.familyRegistration.dependence
    () with ⟨parameter, first, second, different⟩
  exact ⟨parameter⟩

namespace OccurrencesCons

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature LatticeData
  (fun lattice => Index lattice →₀ ℕ) (fun lattice => List (Index lattice))

def actual : Realization signature := realize signature
  (fun _ lattice exponent => _root_.D5.S3.VertexAlgebra.LatticeAllStateField.occurrences lattice exponent)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => [])
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (index : Index lattice) (exponent : Index lattice →₀ ℕ),
    (index :: _root_.D5.S3.VertexAlgebra.LatticeAllStateField.occurrences lattice exponent).Perm
      (readout.readout () lattice (exponent + Finsupp.single index 1))

theorem source_bridge : (type_of% (@occurrences_cons)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨parameter⟩ := indexFamily_nonempty
  have contradiction := law parameter.1 parameter.2 0
  simpa [rejected, realize,
    _root_.D5.S3.VertexAlgebra.LatticeAllStateField.occurrences] using contradiction.length_eq

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  obtain ⟨parameter⟩ := indexFamily_nonempty
  refine ⟨parameter.1, 0, Finsupp.single parameter.2 1, ?_⟩
  intro equal
  change _root_.D5.S3.VertexAlgebra.LatticeAllStateField.occurrences parameter.1 0 =
    _root_.D5.S3.VertexAlgebra.LatticeAllStateField.occurrences parameter.1
      (Finsupp.single parameter.2 1) at equal
  have lengths := (occurrences_cons parameter.1 parameter.2 0).length_eq
  simp only [zero_add] at lengths
  rw [← equal] at lengths
  simpa [_root_.D5.S3.VertexAlgebra.LatticeAllStateField.occurrences] using lengths

def familyRegistration : Registration arena (type_of% (@occurrences_cons)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp occurrences_cons, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@occurrences_cons) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection.occurrences_cons "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection.OccurrencesCons.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end OccurrencesCons

namespace LiftReadout

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ lattice : LatticeData, Charge lattice)
  (fun parameter => Oscillator parameter.1)
  (fun parameter => CorrectionPolynomial parameter.1)

def actual : Realization signature := realize signature
  (fun _ parameter polynomial => correctionLift parameter.1 parameter.2 polynomial)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => 1)
  (fun empty => nomatch empty)

theorem dependence : ObservationalDependence signature actual := by
  intro role
  rcases _root_.Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.MonomialEnumeration.familyRegistration.dependence
    () with ⟨parameter, first, second, different⟩
  refine ⟨parameter, first, second, ?_⟩
  intro equal
  change correctionLift parameter.1 parameter.2 first =
    correctionLift parameter.1 parameter.2 second at equal
  apply different
  change Corr parameter.1 parameter.2 first = Corr parameter.1 parameter.2 second
  exact congrArg (fun polynomial : CorrectionPolynomial parameter.1 =>
    shiftCoefficients parameter.1 (MvPolynomial.optionEquivLeft ℂ (Index parameter.1) polynomial)) equal

end LiftReadout

namespace LiftInsertion

abbrev signature := LiftReadout.signature
abbrev actual := LiftReadout.actual
abbrev rejected := LiftReadout.rejected

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (charge : Charge lattice) (index : Index lattice)
    (polynomial : Oscillator lattice),
    readout.readout () ⟨lattice, charge⟩ (polynomial * MvPolynomial.X index) =
      insertion lattice charge index (correctionLift lattice charge polynomial)

theorem source_bridge : (type_of% (@correctionLift_X_mul)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨parameter⟩ := indexFamily_nonempty
  have contradiction := law parameter.1 0 parameter.2 0
  simpa [rejected, LiftReadout.rejected, realize] using contradiction

def familyRegistration : Registration arena (type_of% (@correctionLift_X_mul)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp correctionLift_X_mul, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := LiftReadout.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@correctionLift_X_mul) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection.correctionLift_X_mul "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection.LiftInsertion.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end LiftInsertion

namespace LiftPartial

abbrev signature := LiftReadout.signature
abbrev actual := LiftReadout.actual
abbrev rejected := LiftReadout.rejected

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (charge : Charge lattice) (index : Index lattice)
    (polynomial : Oscillator lattice),
    MvPolynomial.pderiv (some index) (correctionLift lattice charge polynomial) =
      readout.readout () ⟨lattice, charge⟩ (MvPolynomial.pderiv index polynomial)

theorem source_bridge : (type_of% (@correctionLift_partial)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨parameter⟩ := indexFamily_nonempty
  have contradiction := law parameter.1 0 parameter.2 0
  simpa [rejected, LiftReadout.rejected, realize] using contradiction

def familyRegistration : Registration arena (type_of% (@correctionLift_partial)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp correctionLift_partial, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := LiftReadout.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@correctionLift_partial) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection.correctionLift_partial "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection.LiftPartial.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end LiftPartial

namespace CorrPartial

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ lattice : LatticeData, Index lattice)
  (fun parameter => Oscillator parameter.1) (fun parameter => Oscillator parameter.1)

def actual : Realization signature := realize signature
  (fun _ parameter polynomial => MvPolynomial.pderiv parameter.2 polynomial)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature (fun _ _ _ => 1)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (lattice : LatticeData) (charge : Charge lattice) (index : Index lattice)
    (polynomial : Oscillator lattice) (shift : ℕ),
    readout.readout () ⟨lattice, index⟩ (Corr lattice charge polynomial shift) =
      Corr lattice charge (MvPolynomial.pderiv index polynomial) shift

theorem source_bridge : (type_of% (@Corr_partial)) ↔ arena.Law actual := by
  constructor
  · intro source lattice charge index polynomial shift
    exact correctionBridge.mp source ⟨lattice, charge, index⟩ ⟨polynomial, shift⟩
  · intro law
    apply correctionBridge.mpr
    intro parameter state
    exact law parameter.lattice parameter.charge parameter.index state.1 state.2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨parameter⟩ := indexFamily_nonempty
  have contradiction := law parameter.1 0 parameter.2 0 0
  simpa [rejected, realize] using contradiction

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  obtain ⟨parameter⟩ := indexFamily_nonempty
  refine ⟨parameter, 0, MvPolynomial.X parameter.2, ?_⟩
  simp [actual, realize, MvPolynomial.pderiv_X, Pi.single_apply]

def familyRegistration : Registration arena (type_of% (@Corr_partial)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp Corr_partial, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Corr_partial) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection.Corr_partial "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection.CorrPartial.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end CorrPartial

namespace LiftConstant

abbrev signature := LiftReadout.signature
abbrev actual := LiftReadout.actual
abbrev rejected := LiftReadout.rejected

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (charge : Charge D) (scalar : ℂ),
    readout.readout () ⟨D, charge⟩ (MvPolynomial.C scalar) = MvPolynomial.C scalar

theorem source_bridge : (type_of% (@correctionLift_C)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨parameter⟩ := indexFamily_nonempty
  have contradiction := law parameter.1 0 0
  simpa [rejected, LiftReadout.rejected, realize] using contradiction

def familyRegistration : Registration arena (type_of% (@correctionLift_C)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp correctionLift_C, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := LiftReadout.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@correctionLift_C) (type_of% (realize signature actual.readout actual.anchor))
    (type_of% (@correctionLift)) Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection.correctionLift_C "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection.LiftConstant.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end LiftConstant

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection
