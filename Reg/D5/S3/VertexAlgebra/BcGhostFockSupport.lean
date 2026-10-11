import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.BcGhostFockSupport
import Reg.Support.DependentFamily

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.BcGhostFockSupport

namespace Reg.D5.S3.VertexAlgebra.BcGhostFockSupport

noncomputable section

universe u

theorem sample_vacuum_ne_zero : (vacuum : Fock (ULift.{u} ℤ)) ≠ 0 := by
  intro equality
  have coefficient := congrArg (fun state : Fock (ULift.{u} ℤ) => state ∅) equality
  simpa [vacuum] using coefficient

namespace Annihilation

abbrev Params := Σ Scalar : Type u, Σ _ : CommRing Scalar, ℕ

instance (parameter : Params.{u}) : CommRing parameter.1 := parameter.2.1

abbrev signature : Signature where
  Params := Params.{u}
  State parameter := Fock parameter.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := Fock parameter.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ parameter state => annihilate parameter.2.2 state)
    (fun empty => nomatch empty)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => vacuum) (fun empty => nomatch empty)

abbrev absentArena : Arena where
  signature := signature.{u}
  Law readout := ∀ (parameter : Params) (state : Fock parameter.1),
    parameter.2.2 ∉ occupied state → readout.readout () parameter state = 0

abbrev boundArena : Arena where
  signature := signature.{u}
  Law readout := ∀ (parameter : Params) (state : Fock parameter.1),
    (occupied state).sup id < parameter.2.2 → readout.readout () parameter state = 0

def absentStatement : Prop := ∀ (Scalar : Type u) (_ : CommRing Scalar)
  (state : Fock Scalar) (site : ℕ), site ∉ occupied state → annihilate site state = 0

def boundStatement : Prop := ∀ (Scalar : Type u) (_ : CommRing Scalar)
  (state : Fock Scalar) (site : ℕ),
  (occupied state).sup id < site → annihilate site state = 0

theorem absent_rejected_fails : ¬ absentArena.{u}.Law rejected := by
  intro law
  let parameter : Params := ⟨ULift.{u} ℤ, inferInstance, 1⟩
  have equality := law parameter 0 (by simp [occupied])
  exact sample_vacuum_ne_zero (by simpa [rejected, realize] using equality)

theorem bound_rejected_fails : ¬ boundArena.{u}.Law rejected := by
  intro law
  let parameter : Params := ⟨ULift.{u} ℤ, inferInstance, 1⟩
  have equality := law parameter 0 (by simp [occupied, parameter])
  exact sample_vacuum_ne_zero (by simpa [rejected, realize] using equality)

theorem actual_depends : ObservationalDependence signature.{u} actual := by
  intro role
  let parameter : Params := ⟨ULift.{u} ℤ, inferInstance, 1⟩
  refine ⟨parameter, 0, Finsupp.single {1} 1, ?_⟩
  intro equality
  have coefficient := congrArg (fun state : Fock parameter.1 => state ∅) equality
  norm_num [actual, realize, parameter, annihilate, annihilateBasis, sign,
    Finsupp.linearCombination_single, Finset.filter_singleton] at coefficient

def absentSource : Registration absentArena.{u} absentStatement where
  actual := actual
  bridge := by
    constructor
    · intro law parameter state absent
      exact law parameter.1 parameter.2.1 state parameter.2.2 absent
    · intro law Scalar ring state site absent
      exact law ⟨Scalar, ring, site⟩ state absent
  variation := ⟨fun _ state absent => annihilate_eq_zero state _ absent,
    rejected, absent_rejected_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, absent_rejected_fails⟩
      intro other distinct
      exact (distinct (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := actual_depends

def boundSource : Registration boundArena.{u} boundStatement where
  actual := actual
  bridge := by
    constructor
    · intro law parameter state bound
      exact law parameter.1 parameter.2.1 state parameter.2.2 bound
    · intro law Scalar ring state site bound
      exact law ⟨Scalar, ring, site⟩ state bound
  variation := ⟨fun _ state bound => annihilate_eq_zero_of_sup_lt state _ bound,
    rejected, bound_rejected_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, bound_rejected_fails⟩
      intro other distinct
      exact (distinct (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := actual_depends

def absentRegistration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0,
    _, _, _, _, _, 0}
    (@_root_.D5.S3.VertexAlgebra.BcGhostFockSupport.annihilate_eq_zero.{u})
    (type_of% actual.{u}) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.BcGhostFockSupport.Annihilation.absentUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostFockSupport.Annihilation.absentSource
  realizationSource := none
  generated := false
  arena := .source ⟨absentArena⟩
  objectArena := .source ⟨absentArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source absentArena ⟨absentSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostFockSupport
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def boundRegistration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0,
    _, _, _, _, _, 0}
    (@_root_.D5.S3.VertexAlgebra.BcGhostFockSupport.annihilate_eq_zero_of_sup_lt.{u})
    (type_of% actual.{u}) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.BcGhostFockSupport.Annihilation.boundUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostFockSupport.Annihilation.boundSource
  realizationSource := none
  generated := false
  arena := .source ⟨boundArena⟩
  objectArena := .source ⟨boundArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source boundArena ⟨boundSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostFockSupport
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Annihilation

namespace Support

abbrev Params := Σ Scalar : Type u, Σ _ : CommRing Scalar, ℤ

instance (parameter : Params.{u}) : CommRing parameter.1 := parameter.2.1

abbrev signature : Signature where
  Params := Params.{u}
  State parameter := Fock parameter.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ℤ → Fock parameter.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ parameter state index =>
    normalPair (parameter.2.2 + index) (-index) state) (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature.{u}
  Law readout := ∀ (parameter : Params) (state : Fock parameter.1),
    Function.support (readout.readout () parameter state) ⊆
      Set.Icc (-cutoff parameter.2.2 state) (cutoff parameter.2.2 state)

def statement : Prop := ∀ (Scalar : Type u) (_ : CommRing Scalar)
  (mode : ℤ) (state : Fock Scalar),
  Function.support (fun index : ℤ => normalPair (mode + index) (-index) state) ⊆
    Set.Icc (-cutoff mode state) (cutoff mode state)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => vacuum) (fun empty => nomatch empty)

theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro law
  let parameter : Params := ⟨ULift.{u} ℤ, inferInstance, 0⟩
  have member : (5 : ℤ) ∈ Function.support (rejected.readout () parameter 0) := by
    exact sample_vacuum_ne_zero
  have bound := (law parameter 0 member).2
  norm_num [cutoff, occupied, parameter] at bound

def source : Registration arena.{u} statement where
  actual := actual
  bridge := by
    constructor
    · intro law parameter state
      exact law parameter.1 parameter.2.1 parameter.2.2 state
    · intro law Scalar ring mode state
      exact law ⟨Scalar, ring, mode⟩ state
  variation := ⟨fun parameter state => normal_pair_support_interval parameter.2.2 state,
    rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro other distinct
      exact (distinct (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    let parameter : Params := ⟨ULift.{u} ℤ, inferInstance, 0⟩
    let one : Fock parameter.1 := Finsupp.single {3} 1
    refine ⟨parameter, 0, one, ?_⟩
    intro equality
    have evaluation := congrFun equality 0
    have filter : ({3} : Finset ℕ).filter (fun site => site < 3) = ∅ := by decide
    have bad : (0 : Fock parameter.1) = -one := by
      simpa [actual, realize, parameter, one, normalPair, b, c, create, annihilate,
        createBasis, annihilateBasis, sign, Finsupp.linearCombination_single, filter]
        using evaluation
    have coefficient := congrArg (fun state : Fock parameter.1 => state {3}) bad
    norm_num [one] at coefficient

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0,
    _, _, _, _, _, 0}
    (@_root_.D5.S3.VertexAlgebra.BcGhostFockSupport.normal_pair_support_interval.{u})
    (type_of% actual.{u}) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.BcGhostFockSupport.Support.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostFockSupport.Support.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostFockSupport
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Support

namespace Interval

abbrev Params := Σ Scalar : Type u, Σ _ : CommRing Scalar, Σ _ : ℤ, Σ _ : ℤ, ℤ

instance (parameter : Params.{u}) : CommRing parameter.1 := parameter.2.1

abbrev signature : Signature where
  Params := Params.{u}
  State parameter := Fock parameter.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := Fock parameter.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ parameter state => L parameter.2.2.1 state)
    (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature.{u}
  Law readout := ∀ (parameter : Params) (state : Fock parameter.1),
    parameter.2.2.2.1 ≤ -cutoff parameter.2.2.1 state →
    cutoff parameter.2.2.1 state ≤ parameter.2.2.2.2 →
    readout.readout () parameter state =
      ∑ index ∈ Finset.Icc parameter.2.2.2.1 parameter.2.2.2.2,
        (parameter.2.2.1 - index : parameter.1) •
          normalPair (parameter.2.2.1 + index) (-index) state

def statement : Prop := ∀ (Scalar : Type u) (_ : CommRing Scalar)
  (mode : ℤ) (state : Fock Scalar) (intervalStart intervalEnd : ℤ),
  intervalStart ≤ -cutoff mode state → cutoff mode state ≤ intervalEnd →
  L mode state = ∑ index ∈ Finset.Icc intervalStart intervalEnd,
    (mode - index : Scalar) • normalPair (mode + index) (-index) state

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => vacuum) (fun empty => nomatch empty)

theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro law
  let parameter : Params := ⟨ULift.{u} ℤ, inferInstance, 0, -4, 4⟩
  have equality := law parameter 0 (by norm_num [cutoff, occupied, parameter])
    (by norm_num [cutoff, occupied, parameter])
  exact sample_vacuum_ne_zero (by simpa [rejected, realize] using equality)

theorem sample_action : L (K := ULift.{u} ℤ) 0 (Finsupp.single {1} 1) =
    -Finsupp.single {1} 1 := by
  let state : Fock (ULift.{u} ℤ) := Finsupp.single {1} 1
  have bound : cutoff 0 state = 5 := by simp [cutoff, occupied, state]
  have interval : Finset.Icc (-5 : ℤ) 5 = {-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5} :=
    by decide
  change L 0 state = -state
  rw [L_interval_sum 0 state (-5) 5 (by omega) (by omega), interval]
  norm_num [state, normalPair, b, c, create, annihilate, createBasis, annihilateBasis,
    sign, Finsupp.linearCombination_single, Finset.filter_singleton]

def source : Registration arena.{u} statement where
  actual := actual
  bridge := by
    constructor
    · intro law parameter state lower upper
      exact law parameter.1 parameter.2.1 parameter.2.2.1 state
        parameter.2.2.2.1 parameter.2.2.2.2 lower upper
    · intro law Scalar ring mode state intervalStart intervalEnd lower upper
      exact law ⟨Scalar, ring, mode, intervalStart, intervalEnd⟩ state lower upper
  variation := ⟨fun parameter state lower upper => L_interval_sum
    parameter.2.2.1 state parameter.2.2.2.1 parameter.2.2.2.2 lower upper,
    rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro other distinct
      exact (distinct (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    let parameter : Params := ⟨ULift.{u} ℤ, inferInstance, 0, -4, 4⟩
    refine ⟨parameter, 0, Finsupp.single {1} 1, ?_⟩
    intro equality
    change L (K := ULift.{u} ℤ) 0 0 = L 0 (Finsupp.single {1} 1) at equality
    rw [map_zero, sample_action] at equality
    have coefficient := congrArg (fun state : Fock (ULift.{u} ℤ) => state {1}) equality
    norm_num at coefficient

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0,
    _, _, _, _, _, 0}
    (@_root_.D5.S3.VertexAlgebra.BcGhostFockSupport.L_interval_sum.{u})
    (type_of% actual.{u}) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.BcGhostFockSupport.Interval.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostFockSupport.Interval.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostFockSupport
    definition := none
    coordinates := #[0, 1, 2, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Interval

namespace Cyclic

abbrev Params := Σ Scalar : Type u, CommRing Scalar

instance (parameter : Params.{u}) : CommRing parameter.1 := parameter.2

abbrev signature : Signature where
  Params := Params.{u}
  State parameter := Submodule parameter.1 (Fock parameter.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := Submodule parameter.1 (Fock parameter.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ state => state) (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature.{u}
  Law readout := ∀ (parameter : Params) (submodule : Submodule parameter.1 (Fock parameter.1)),
    vacuum ∈ submodule →
    (∀ mode : ℤ, mode ≤ -2 → ∀ state ∈ submodule, b mode state ∈ submodule) →
    (∀ mode : ℤ, mode ≤ 1 → ∀ state ∈ submodule, c mode state ∈ submodule) →
    readout.readout () parameter submodule = ⊤

def statement : Prop := ∀ (Scalar : Type u) (_ : CommRing Scalar)
  (submodule : Submodule Scalar (Fock Scalar)), vacuum ∈ submodule →
  (∀ mode : ℤ, mode ≤ -2 → ∀ state ∈ submodule, b mode state ∈ submodule) →
  (∀ mode : ℤ, mode ≤ 1 → ∀ state ∈ submodule, c mode state ∈ submodule) → submodule = ⊤

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ⊥) (fun empty => nomatch empty)

theorem sample_submodule_ne : (⊥ : Submodule (ULift.{u} ℤ) (Fock (ULift.{u} ℤ))) ≠ ⊤ := by
  intro equality
  have member : (vacuum : Fock (ULift.{u} ℤ)) ∈
      (⊥ : Submodule (ULift.{u} ℤ) (Fock (ULift.{u} ℤ))) := by
    rw [equality]
    trivial
  exact sample_vacuum_ne_zero (by simpa using member)

theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro law
  let parameter : Params := ⟨ULift.{u} ℤ, inferInstance⟩
  have equality := law parameter ⊤ (by trivial) (by intros; trivial) (by intros; trivial)
  exact sample_submodule_ne equality

def source : Registration arena.{u} statement where
  actual := actual
  bridge := by
    constructor
    · intro law parameter submodule vacuumMember bStable cStable
      exact law parameter.1 parameter.2 submodule vacuumMember bStable cStable
    · intro law Scalar ring submodule vacuumMember bStable cStable
      exact law ⟨Scalar, ring⟩ submodule vacuumMember bStable cStable
  variation := ⟨fun _ submodule vacuumMember bStable cStable =>
    creation_cyclic submodule vacuumMember bStable cStable, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro other distinct
      exact (distinct (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    exact ⟨⟨ULift.{u} ℤ, inferInstance⟩, ⊥, ⊤, sample_submodule_ne⟩

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0,
    _, _, _, _, _, 0}
    (@_root_.D5.S3.VertexAlgebra.BcGhostFockSupport.creation_cyclic.{u})
    (type_of% actual.{u}) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.BcGhostFockSupport.Cyclic.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostFockSupport.Cyclic.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostFockSupport
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Cyclic

#print axioms Annihilation.absentRegistration
#print axioms Annihilation.boundRegistration
#print axioms Support.registration
#print axioms Interval.registration
#print axioms Cyclic.registration

end

end Reg.D5.S3.VertexAlgebra.BcGhostFockSupport
