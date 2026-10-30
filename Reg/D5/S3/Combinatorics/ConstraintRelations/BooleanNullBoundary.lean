import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary

/-! # Source-bound observation of the five-mode relation -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary
open _root_.D5.S3.Combinatorics.ConstraintRelations.PrimitivePositive
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window bits)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

def windowSignature : Signature where
  Params := Unit
  State _ := Fin 3 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def windowActual : Realization windowSignature :=
  realize windowSignature (fun _ _ a => A a) (fun e => nomatch e)

def windowRejected : Realization windowSignature :=
  realize windowSignature (fun _ _ _ => False) (fun e => nomatch e)

def windowArena : Arena where
  signature := windowSignature
  Law R := ∀ x y z : Bool, R.readout () () ![x, y, z] ↔
    ∃ w : Window, bits w = [x, z, y]

private theorem windowRejected_law : ¬ windowArena.Law windowRejected := by
  intro h
  exact (h false false false).mpr ⟨.zero, rfl⟩

def windowFamily : Registration windowArena (type_of% (@a_window_iff)) where
  actual := windowActual
  bridge := Iff.rfl
  variation := ⟨a_window_iff, windowRejected, windowRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨windowRejected, ?_, rfl, windowRejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), ![false, false, false], ![true, true, true], ?_⟩
    intro h
    change A ![false, false, false] = A ![true, true, true] at h
    have hzero : A ![false, false, false] := by constructor <;> rfl
    have hbad : A ![true, true, true] := Eq.mp h hzero
    exact Bool.noConfusion hbad.1

noncomputable def windowRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@a_window_iff) (Realization windowSignature) Type Unit where
  unitName := `D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary.a_window_iff.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary.windowFamily
  realizationSource := none
  generated := false
  arena := .source ⟨windowArena⟩
  objectArena := .source ⟨windowArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source windowArena ⟨windowFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize windowSignature (fun _ _ a => A a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev ResultParameters := Σ m : Nat, List (Atom baseArity (3 + m))

def resultSignature : Signature where
  Params := ResultParameters
  State _ := Fin 3 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def resultActual : Realization resultSignature :=
  realize resultSignature (fun _ p a => Defines baseRelations p.2 a) (fun e => nomatch e)

def resultRejected : Realization resultSignature :=
  realize resultSignature (fun _ _ a => OR3 a) (fun e => nomatch e)

def resultArena : Arena where
  signature := resultSignature
  Law R :=
    (∀ m : Nat, ∀ atoms : List (Atom baseArity (3 + m)),
      ¬ (∀ a : Fin 3 → Bool, R.readout () ⟨m, atoms⟩ a ↔ OR3 a)) ∧
    (∃ m : Nat, ∃ atoms : List (Atom nArity (3 + m)),
      ∀ a : Fin 3 → Bool, Defines nRelations atoms a ↔ OR3 a)

private theorem resultRejected_law : ¬ resultArena.Law resultRejected := by
  intro h
  exact h.1 0 [] (fun _ => Iff.rfl)

def resultFamily : Registration resultArena (type_of% (@result)) where
  actual := resultActual
  bridge := Iff.rfl
  variation := ⟨result, resultRejected, resultRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨resultRejected, ?_, rfl, resultRejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨0, [⟨.one, ![0]⟩]⟩,
      ![true, false, false], ![false, false, false], ?_⟩
    intro h
    dsimp [resultActual, realize] at h
    have ht : Defines baseRelations [⟨.one, ![0]⟩] ![true, false, false] :=
      ⟨Fin.elim0, rfl, trivial⟩
    obtain ⟨w, hw, _⟩ := Eq.mp h ht
    exact Bool.noConfusion hw

noncomputable def resultRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@result) (Realization resultSignature) Type Unit where
  unitName := `D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary.resultFamily
  realizationSource := none
  generated := false
  arena := .source ⟨resultArena⟩
  objectArena := .source ⟨resultArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source resultArena ⟨resultFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize resultSignature
    (fun _ p a => Defines baseRelations p.2 a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary

namespace Reg.D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary.Nor

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary
open _root_.D5.S3.ConceptDynamics.InformationEscape

def signature : DependentFamily.Signature where
  Params := Bool
  State := fun _ => Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ x y => !(x || y)) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ x y z : Bool, N ![x, y, z] ↔ z = R.readout () x y

abbrev sourceScope := type_of% (@n_iff_nor)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := source_bridge.mp n_iff_nor

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => false) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hn := (h false false false).mpr rfl
  exact (by simp [N, A] : ¬ N ![false, false, false]) hn

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨false, false, true, ?_⟩
    change true ≠ false
    decide

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@n_iff_nor) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary.n_iff_nor.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary.Nor.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun _ x y => !(x || y)) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end Reg.D5.S3.Combinatorics.ConstraintRelations.BooleanNullBoundary.Nor
