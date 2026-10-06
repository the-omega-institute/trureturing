import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit

open _root_.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Equiv

universe u
noncomputable section

private def flip : Perm (ULift.{u} Bool) := Equiv.swap ⟨false⟩ ⟨true⟩

private theorem flip_involutive : Function.Involutive (flip.{u}) :=
  Equiv.swap_apply_self _ _

private theorem flip_no_fixed : ∀ x, flip.{u} x ≠ x := by
  rintro ⟨x⟩
  cases x <;> simp [flip]

namespace Reflection

abbrev signature : Signature where
  Params := Σ X : Type u, Σ _s : Perm X, Σ _t : Perm X, ℤ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ p x => ((p.2.1 * p.2.2.1) ^ p.2.2.2 * p.2.1) x)
  (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature (fun _ _ x => x)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} (s t : Perm X)
    (_hs : Function.Involutive s) (_ht : Function.Involutive t),
    ((∀ x, s x ≠ x) ∧ (∀ x, t x ≠ x)) ↔
      ∀ (k : ℤ) (x : X), R.readout () ⟨X, s, t, k⟩ x ≠ x

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := (h flip flip flip_involutive flip_involutive).mp
    ⟨flip_no_fixed, flip_no_fixed⟩ 0 ⟨false⟩
  exact hh rfl

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by intro X s t hs ht; exact fixedPointFree_iff_reflection_exclusion s t hs ht,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, 1, 1, 0⟩, ⟨false⟩, ⟨true⟩, ?_⟩
    simp [actual, realize]

def registration_contract : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.fixedPointFree_iff_reflection_exclusion.{u})
    (type_of% (realize signature.{u}
    (fun _ p x => ((p.2.1 * p.2.2.1) ^ p.2.2.2 * p.2.1) x)
    (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.fixedPointFree_iff_reflection_exclusion "Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit/Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Reflection.arena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Reflection.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p x => ((p.2.1 * p.2.2.1) ^ p.2.2.2 * p.2.1) x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    definition := none
    owner := `D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
    coordinates := #[0, 1, 2, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "body", "fn", "arg"]
      stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reflection

namespace Separation

abbrev signature : Signature where
  Params := Σ X : Type u, Σ _s : Perm X, Perm X
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ p x => (p.2.1 * p.2.2).SameCycle x (p.2.1 x))
  (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature (fun _ _ _ => True)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} (s t : Perm X)
    (_hs : Function.Involutive s) (_ht : Function.Involutive t),
    ((∀ x, s x ≠ x) ∧ (∀ x, t x ≠ x)) ↔
      ∀ x, ¬ R.readout () ⟨X, s, t⟩ x

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact (h flip flip flip_involutive flip_involutive).mp
    ⟨flip_no_fixed, flip_no_fixed⟩ ⟨false⟩ trivial

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by intro X s t hs ht; exact fixedPointFree_iff_rotation_separation s t hs ht,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let q : Perm (ULift.{u} (Fin 3)) := Equiv.swap ⟨0⟩ ⟨1⟩
    refine ⟨⟨ULift.{u} (Fin 3), q, q⟩, ⟨0⟩, ⟨2⟩, ?_⟩
    simp [actual, realize, q, Equiv.swap_mul_self, Perm.sameCycle_one,
      Equiv.swap_apply_def]

def registration_contract : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.fixedPointFree_iff_rotation_separation.{u})
    (type_of% (realize signature.{u}
    (fun _ p x => (p.2.1 * p.2.2).SameCycle x (p.2.1 x))
    (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.fixedPointFree_iff_rotation_separation "Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit/Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Separation.arena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Separation.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p x => (p.2.1 * p.2.2).SameCycle x (p.2.1 x))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    definition := none
    owner := `D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg"]
      stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Separation

namespace Reachability

abbrev signature : Signature where
  Params := Σ X : Type u, Σ _s : Perm X, Σ _t : Perm X, X
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ p y => Connected p.2.1 p.2.2.1 p.2.2.2 y)
  (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature (fun _ _ _ => False)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} (s t : Perm X),
    Function.Involutive s → Function.Involutive t → ∀ (x y : X),
    R.readout () ⟨X, s, t, x⟩ y ↔
      (s * t).SameCycle x y ∨ (s * t).SameCycle (s x) y

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact (h (1 : Perm (ULift.{u} Bool)) 1 (fun _ => rfl) (fun _ => rfl)
    ⟨false⟩ ⟨false⟩).mpr (Or.inl (Perm.SameCycle.refl _ _))

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by intro X s t hs ht x y; exact connected_iff_rotation_orbits s t hs ht x y,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} Bool, 1, 1, ⟨false⟩⟩, ⟨false⟩, ⟨true⟩, ?_⟩
    change Connected 1 1 (ULift.up false) (ULift.up false) ≠
      Connected 1 1 (ULift.up false) (ULift.up true)
    rw [connected_iff_rotation_orbits 1 1 (fun _ => rfl) (fun _ => rfl),
      connected_iff_rotation_orbits 1 1 (fun _ => rfl) (fun _ => rfl)]
    simp

def registration_contract : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.connected_iff_rotation_orbits.{u})
    (type_of% (realize signature.{u}
    (fun _ p y => Connected p.2.1 p.2.2.1 p.2.2.2 y)
    (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.connected_iff_rotation_orbits "Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit/Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Reachability.arena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Reachability.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p y => Connected p.2.1 p.2.2.1 p.2.2.2 y)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    definition := none
    owner := `D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
    coordinates := #[0, 1, 2, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reachability

namespace Components

abbrev signature : Signature where
  Params := Σ X : Type u, Σ _s : Perm X, Perm X
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Set p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ p x => RotationOrbit (p.2.1 * p.2.2) x) (fun e => nomatch e)

def emptyRejected : Realization signature.{u} := realize signature
  (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev splitArena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} (s t : Perm X),
    Function.Involutive s → Function.Involutive t →
    (∀ x, s x ≠ x) → (∀ x, t x ≠ x) → ∀ x,
    Disjoint (RotationOrbit (s * t) x) (RotationOrbit (s * t) (s x)) ∧
    (R.readout () ⟨X, s, t⟩ x).Nonempty ∧
    (RotationOrbit (s * t) (s x)).Nonempty ∧
    {y | Connected s t x y} =
      RotationOrbit (s * t) x ∪ RotationOrbit (s * t) (s x) ∧
    s '' RotationOrbit (s * t) x = RotationOrbit (s * t) (s x) ∧
    t '' RotationOrbit (s * t) x = RotationOrbit (s * t) (s x)

private theorem emptyRejected_law : ¬ splitArena.{u}.Law emptyRejected := by
  intro h
  exact Set.not_nonempty_empty
    (h flip flip flip_involutive flip_involutive flip_no_fixed flip_no_fixed ⟨false⟩).2.1

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} Bool, 1, 1⟩, ⟨false⟩, ⟨true⟩, ?_⟩
  intro h
  have hh := Set.ext_iff.mp h (ULift.up false)
  simp [actual, realize, RotationOrbit] at hh

def splitRegistration : Registration splitArena.{u} (splitArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by intro X s t hs ht hsl htr x; exact component_split s t hs ht hsl htr x,
    emptyRejected, emptyRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨emptyRejected, ?_, rfl, emptyRejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def splitRegistration_contract : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.component_split.{u})
    (type_of% (realize signature.{u}
    (fun _ p x => RotationOrbit (p.2.1 * p.2.2) x) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.component_split "Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit/Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Components.splitArena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Components.splitRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨splitArena.{u}⟩
  objectArena := .source ⟨splitArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source splitArena.{u} ⟨splitRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p x => RotationOrbit (p.2.1 * p.2.2) x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    definition := none
    owner := `D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "arg"]
      stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def coincidentRejected : Realization signature.{u} := realize signature
  (fun _ p x => RotationOrbit (p.2.1 * p.2.2) (p.2.1 x)) (fun e => nomatch e)

abbrev classesArena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} (s t : Perm X),
    Function.Involutive s → Function.Involutive t →
    (∀ x, s x ≠ x) → (∀ x, t x ≠ x) → ∀ x,
    Set.range (fun y : {y // Connected s t x y} => RotationOrbit (s * t) y.val) =
      {RotationOrbit (s * t) x, RotationOrbit (s * t) (s x)} ∧
    R.readout () ⟨X, s, t⟩ x ≠ RotationOrbit (s * t) (s x)

private theorem coincidentRejected_law : ¬ classesArena.{u}.Law coincidentRejected := by
  intro h
  exact (h flip flip flip_involutive flip_involutive flip_no_fixed flip_no_fixed ⟨false⟩).2 rfl

def classesRegistration : Registration classesArena.{u} (classesArena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by intro X s t hs ht hsl htr x; exact component_orbit_classes s t hs ht hsl htr x,
    coincidentRejected, coincidentRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨coincidentRejected, ?_, rfl, coincidentRejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def classesRegistration_contract : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.component_orbit_classes.{u})
    (type_of% (realize signature.{u}
    (fun _ p x => RotationOrbit (p.2.1 * p.2.2) x) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.component_orbit_classes "Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit/Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Components.classesArena/[anonymous]") "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Components.classesRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨classesArena.{u}⟩
  objectArena := .source ⟨classesArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source classesArena.{u} ⟨classesRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p x => RotationOrbit (p.2.1 * p.2.2) x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    definition := none
    owner := `D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg"]
      stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Components

#print axioms Reflection.registration
#print axioms Separation.registration
#print axioms Reachability.registration
#print axioms Components.splitRegistration
#print axioms Components.classesRegistration

end
end Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit

namespace Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Reflection
open LeanInformationAudit.Contract
universe u
noncomputable section

def lawStatement : Prop := arena.{u}.Law registration.actual

def lawFunction := arena.{u}.Law

def bridgeFact : NodeFact := .equivalent
  (type_of% @_root_.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.fixedPointFree_iff_reflection_exclusion.{u})
  (arena.{u}.Law registration.actual)
  { owner := `D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit,
    declaration := `D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.fixedPointFree_iff_reflection_exclusion,
    part := .type, path := [], levels := [.param `u] }
  { owner := `Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit,
    declaration := `Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Reflection.lawStatement,
    part := .value, path := [], levels := [.param `u] }
  registration.bridge

def exclusion : StatementExclusion arena.{u}.Law
    (type_of% @_root_.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.fixedPointFree_iff_reflection_exclusion.{u}) where
  lawLocation := {
    owner := `Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit,
      declaration := `Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Reflection.lawFunction,
      part := .value, path := [], levels := [.param `u] }
  statementLocation := {
    owner := `D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit,
      declaration := `D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.fixedPointFree_iff_reflection_exclusion,
      part := .type, path := [], levels := [.param `u] }
  excludes := _root_.Reg.Support.NodeFacts.excludeFixed _ _ registration.actual
    registration.variation.2.choose
    (by intro X s t hs ht; exact registration.variation.1 s t hs ht)
    registration.variation.2.choose_spec


def observed := fun {X : Type u} (s t : Equiv.Perm X)
    (hs : Function.Involutive s) (ht : Function.Involutive t) (k : ℤ) (x : X) =>
  actual.readout () ⟨X,s,t,k⟩ x

def observationFact : NodeFact := .equal
  (fun {X : Type u} (s t : Equiv.Perm X)
    (hs : Function.Involutive s) (ht : Function.Involutive t) (k : ℤ) (x : X) =>
    ((s * t) ^ k * s) x)
  (fun {X : Type u} (s t : Equiv.Perm X)
    (hs : Function.Involutive s) (ht : Function.Involutive t) (k : ℤ) (x : X) =>
    actual.readout () ⟨X,s,t,k⟩ x)
  { owner := `D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit,
    declaration := `D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.fixedPointFree_iff_reflection_exclusion,
    part := .type, path := [.body,.body,.body,.body,.body,.argument,.body,.body,.function,.argument],
    levels := [.param `u] }
  { owner := `Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit,
    declaration := `Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Reflection.observed,
    part := .value, path := [], levels := [.param `u] }
  rfl

end
end Reg.D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Reflection
