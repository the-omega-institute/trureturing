import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev rootSignature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def rootActual : Realization rootSignature := realize rootSignature (fun _ _ t => root t)
  (fun e => nomatch e)
def rootBad : Realization rootSignature := realize rootSignature (fun _ _ _ => .of false)
  (fun e => nomatch e)

abbrev rootArena : Arena where
  signature := rootSignature
  Law R := ∀ t : Source,
    (∀ k : ℕ, (∃ x : Source, substitution^[k] x = t) ↔ k ≤ depth t) ∧
    Primitive (R.readout () () t) ∧ substitution^[depth t] (R.readout () () t) = t ∧
    (∀ (p : Source) (n : ℕ), Primitive p → substitution^[n] p = t →
      n = depth t ∧ p = R.readout () () t) ∧
    (flag t = true ↔ substitution^[depth t] (.of true) = t)

theorem rootBadLaw : ¬ rootArena.Law rootBad := by
  intro h
  exact (h (.of true)).2.1 ⟨.of true, rfl⟩

theorem rootDependence : ObservationalDependence rootSignature rootActual := by
  intro i
  refine ⟨(), .of true, .mul (.of true) (.of true), ?_⟩
  have ha : flag (.of true) = true :=
    congrArg Prod.snd all_source_coordinate_law.2.2.2.1
  have hp := all_source_coordinate_law.2.2.1 (.of true) (.of true)
  have hn : ¬ (flag (.of true) = true ∧ flag (.of true) = true ∧
      depth (.of true) = depth (.of true) + 1) := by omega
  rw [if_neg hn] at hp
  have hb : flag (.mul (.of true) (.of true)) = false := congrArg Prod.snd hp
  change root (.of true) ≠ root (.mul (.of true) (.of true))
  intro h
  have hf : flag (.of true) = flag (.mul (.of true) (.of true)) :=
    congrArg (fun p : Source => decide (p = .of true)) h
  rw [ha, hb] at hf
  cases hf

def rootFamily : Registration rootArena (type_of% (@intrinsic_coordinates)) where
  actual := rootActual
  bridge := Iff.rfl
  variation := ⟨intrinsic_coordinates, rootBad, rootBadLaw⟩
  sensitivity := ⟨fun _i => ⟨rootBad, fun _j h => (h (Subsingleton.elim _ _)).elim,
    rfl, rootBadLaw⟩, fun i => nomatch i⟩
  dependence := rootDependence

abbrev coordinateSignature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ × Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def coordinateActual : Realization coordinateSignature :=
  realize coordinateSignature (fun _ _ t => Q t) (fun e => nomatch e)
def coordinateBad : Realization coordinateSignature :=
  realize coordinateSignature (fun _ _ _ => (0,false)) (fun e => nomatch e)

abbrev coordinateArena : Arena where
  signature := coordinateSignature
  Law R :=
    (∀ t : Source,
      (∀ k : ℕ, (∃ x : Source, substitution^[k] x = t) ↔ k ≤ depth t) ∧
      Primitive (root t) ∧ substitution^[depth t] (root t) = t ∧
      (∀ (p : Source) (n : ℕ), Primitive p → substitution^[n] p = t →
        n = depth t ∧ p = root t) ∧
      (flag t = true ↔ substitution^[depth t] (.of true) = t)) ∧
    (∀ t : Source, R.readout () () (substitution t) = (depth t + 1, flag t)) ∧
    (∀ s t : Source, R.readout () () (.mul s t) =
      if flag s = true ∧ flag t = true ∧ depth s = depth t + 1
      then (depth t + 2, true) else (min (depth s) (depth t), false)) ∧
    R.readout () () (.of true) = (0, true) ∧ R.readout () () (.of false) = (1, true)

theorem coordinateBadLaw : ¬ coordinateArena.Law coordinateBad := by
  intro h
  have hx := congrArg Prod.snd h.2.2.2.1
  exact Bool.false_ne_true hx

theorem coordinateDependence : ObservationalDependence coordinateSignature coordinateActual := by
  intro i
  refine ⟨(), .of true, .of false, ?_⟩
  change Q (.of true) ≠ Q (.of false)
  rw [all_source_coordinate_law.2.2.2.1, all_source_coordinate_law.2.2.2.2]
  decide

def coordinateFamily : Registration coordinateArena (type_of% (@all_source_coordinate_law)) where
  actual := coordinateActual
  bridge := Iff.rfl
  variation := ⟨all_source_coordinate_law, coordinateBad, coordinateBadLaw⟩
  sensitivity := ⟨fun _i => ⟨coordinateBad, fun _j h => (h (Subsingleton.elim _ _)).elim,
    rfl, coordinateBadLaw⟩, fun i => nomatch i⟩
  dependence := coordinateDependence

def rootRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@intrinsic_coordinates) (type_of% (realize rootSignature rootActual.readout rootActual.anchor))
    Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates.intrinsic_coordinates.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates.rootFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rootArena⟩
  objectArena := .source ⟨rootArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rootArena ⟨rootFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rootSignature rootActual.readout rootActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "arg", "fn", "arg", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def coordinateRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@all_source_coordinate_law)
    (type_of% (realize coordinateSignature coordinateActual.readout coordinateActual.anchor)) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates.all_source_coordinate_law.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates.coordinateFamily
  realizationSource := none
  generated := false
  arena := .source ⟨coordinateArena⟩
  objectArena := .source ⟨coordinateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coordinateArena ⟨coordinateFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coordinateSignature coordinateActual.readout coordinateActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["arg", "fn", "arg", "body", "fn", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev signature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ t => substitution t)
  (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => .of true)
  (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ t : Source, R.readout () () t ≠ .of true

theorem badLaw : ¬ arena.Law bad := fun h => h (.of true) rfl

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), .of true, .of false, ?_⟩
  change FreeMagma.of false ≠ FreeMagma.mul (.of false) (.of true)
  intro h
  cases h

def family : Registration arena (type_of% (@no_alpha)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨no_alpha, bad, badLaw⟩
  sensitivity := ⟨fun _i => ⟨bad, fun _j h => (h (Subsingleton.elim _ _)).elim,
    rfl, badLaw⟩, fun i => nomatch i⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@no_alpha) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates.no_alpha.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev pairArena : Arena where
  signature := signature
  Law R := ∀ s t : Source,
    (∃ x : Source, R.readout () () x = .mul s t) ↔
      (s = .of false ∧ t = .of true) ∨
      ((∃ x : Source, substitution x = s) ∧ (∃ y : Source, substitution y = t))

theorem pairBadLaw : ¬ pairArena.Law bad := by
  intro h
  obtain ⟨x,hx⟩ := (h (.of false) (.of true)).mpr (Or.inl ⟨rfl,rfl⟩)
  change FreeMagma.of true = FreeMagma.mul _ _ at hx
  cases hx

def pairFamily : Registration pairArena (type_of% (@pair_image)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pair_image,bad,pairBadLaw⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,pairBadLaw⟩,
    fun i => nomatch i⟩
  dependence := dependence

def pairRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pair_image) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates.pair_image.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates.pairFamily
  realizationSource := none
  generated := false
  arena := .source ⟨pairArena⟩
  objectArena := .source ⟨pairArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pairArena ⟨pairFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","fn","arg","arg","body","fn","arg"],
      stateBinder := 2,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms pairRegistration
#print axioms no_alpha
#print axioms registration
#print axioms rootRegistration
#print axioms coordinateRegistration
end Reg.D5.S3.Arith.FibonacciAtomic.SourceCoordinates.IntrinsicSubstitutionCoordinates
