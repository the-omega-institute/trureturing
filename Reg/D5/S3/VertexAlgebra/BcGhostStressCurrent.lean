import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.BcGhostStressCurrent
import Reg.Support.DependentFamily
import Mathlib.Algebra.Ring.ULift

set_option autoImplicit false

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.BcGhostFockSupport
open _root_.D5.S3.VertexAlgebra.BcGhostStressCurrent
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.BcGhostStressCurrent
universe scalarLevel
noncomputable section

abbrev signature : Signature where
  Params := (Scalar : Type scalarLevel) × CommRing Scalar
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameters := letI := parameters.2; Module.End parameters.1 (Fock parameters.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def bActual : Realization signature :=
  realize signature (fun _ parameters index => letI := parameters.2; b index)
    (fun empty => nomatch empty)

def cActual : Realization signature :=
  realize signature (fun _ parameters index => letI := parameters.2; c index)
    (fun empty => nomatch empty)

def oneReadout : Realization signature :=
  realize signature (fun _ parameters _ => letI := parameters.2; 1)
    (fun empty => nomatch empty)

def zeroReadout : Realization signature :=
  realize signature (fun _ parameters _ => letI := parameters.2; 0)
    (fun empty => nomatch empty)

theorem bDependence : ObservationalDependence signature.{scalarLevel} bActual := by
  intro role
  refine ⟨⟨ULift.{scalarLevel} ℤ, inferInstance⟩, -2, 0, ?_⟩
  change b (K := ULift.{scalarLevel} ℤ) (-2) ≠ b 0
  intro equality
  have identity := b_c (K := ULift.{scalarLevel} ℤ) (-2) 2
  have zero := b_c (K := ULift.{scalarLevel} ℤ) 0 2
  rw [equality] at identity
  have contradiction : (1 : Module.End (ULift.{scalarLevel} ℤ)
      (Fock (ULift.{scalarLevel} ℤ))) = 0 := by
    simpa using identity.symm.trans zero
  exact one_ne_zero contradiction

theorem cDependence : ObservationalDependence signature.{scalarLevel} cActual := by
  intro role
  refine ⟨⟨ULift.{scalarLevel} ℤ, inferInstance⟩, 2, 3, ?_⟩
  change c (K := ULift.{scalarLevel} ℤ) 2 ≠ c 3
  intro equality
  have identity := b_c (K := ULift.{scalarLevel} ℤ) (-2) 2
  have zero := b_c (K := ULift.{scalarLevel} ℤ) (-2) 3
  rw [equality] at identity
  have contradiction : (1 : Module.End (ULift.{scalarLevel} ℤ)
      (Fock (ULift.{scalarLevel} ℤ))) = 0 := by
    simpa using identity.symm.trans zero
  exact one_ne_zero contradiction

def evidenceFor (predicate : Realization signature.{scalarLevel} → Prop)
    (observed intervention : Realization signature)
    (positive : predicate observed) (negative : ¬ predicate intervention)
    (dependence : ObservationalDependence signature observed) :
    Registration ⟨signature, predicate⟩ (predicate observed) where
  actual := observed
  bridge := Iff.rfl
  variation := ⟨positive, intervention, negative⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨intervention, ?_, ?_, negative⟩
      · intro other distinct
        exact (distinct (Subsingleton.elim other role)).elim
      · funext empty
        exact nomatch empty
    · intro empty
      exact nomatch empty
  dependence := dependence

namespace BB

abbrev arena : Arena where
  signature := signature.{scalarLevel}
  Law family := ∀ {Scalar : Type scalarLevel} [CommRing Scalar] (first second : ℤ),
    family.readout () ⟨Scalar, inferInstance⟩ first *
        family.readout () ⟨Scalar, inferInstance⟩ second +
      family.readout () ⟨Scalar, inferInstance⟩ second *
        family.readout () ⟨Scalar, inferInstance⟩ first = 0

theorem rejected : ¬ arena.{scalarLevel}.Law oneReadout := by
  intro law
  have equation := law (Scalar := ULift.{scalarLevel} ℤ) 0 0
  change (1 : Module.End (ULift.{scalarLevel} ℤ) (Fock (ULift.{scalarLevel} ℤ))) * 1 +
    1 * 1 = 0 at equation
  have value := congrArg (fun operator : Module.End (ULift.{scalarLevel} ℤ)
    (Fock (ULift.{scalarLevel} ℤ)) => (operator vacuum) ∅) equation
  norm_num [vacuum] at value
  have integerValue := congrArg ULift.down value
  change (2 : ℤ) = 0 at integerValue
  norm_num at integerValue

def evidence : Registration arena (arena.Law bActual) :=
  evidenceFor arena.Law bActual oneReadout (fun first second => b_b first second)
    rejected bDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@b_b.{scalarLevel}) (type_of% bActual.{scalarLevel})
    Unit Unit where
  unitName := `D5.S3.VertexAlgebra.BcGhostStressCurrent.b_b.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostStressCurrent.BB.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ parameters index => letI := parameters.2; b index)
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostStressCurrent
    definition := none
    coordinates := #[0, 1]
    readouts := #[
      { path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"],
        stateBinder := 2, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"],
        stateBinder := 3, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"],
        stateBinder := 3, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "body", "body", "fn", "arg", "arg", "arg"],
        stateBinder := 2, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `linter.mathlibStandardSet, value := .bool true }]

#print axioms evidence
#print axioms registration
end BB

namespace CC

abbrev arena : Arena where
  signature := signature.{scalarLevel}
  Law family := ∀ {Scalar : Type scalarLevel} [CommRing Scalar] (first second : ℤ),
    family.readout () ⟨Scalar, inferInstance⟩ first *
        family.readout () ⟨Scalar, inferInstance⟩ second +
      family.readout () ⟨Scalar, inferInstance⟩ second *
        family.readout () ⟨Scalar, inferInstance⟩ first = 0

def evidence : Registration arena (arena.Law cActual) :=
  evidenceFor arena.Law cActual oneReadout (fun first second => c_c first second)
    BB.rejected cDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@c_c.{scalarLevel}) (type_of% cActual.{scalarLevel})
    Unit Unit where
  unitName := `D5.S3.VertexAlgebra.BcGhostStressCurrent.c_c.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostStressCurrent.CC.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ parameters index => letI := parameters.2; c index)
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostStressCurrent
    definition := none
    coordinates := #[0, 1]
    readouts := #[
      { path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"],
        stateBinder := 2, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"],
        stateBinder := 3, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"],
        stateBinder := 3, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "body", "body", "fn", "arg", "arg", "arg"],
        stateBinder := 2, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `linter.mathlibStandardSet, value := .bool true }]

#print axioms evidence
#print axioms registration
end CC

namespace BC

abbrev arena : Arena where
  signature := signature.{scalarLevel}
  Law family := ∀ {Scalar : Type scalarLevel} [CommRing Scalar] (first second : ℤ),
    family.readout () ⟨Scalar, inferInstance⟩ first * c second +
      c second * family.readout () ⟨Scalar, inferInstance⟩ first =
        if first + second = 0 then 1 else 0

theorem rejected : ¬ arena.{scalarLevel}.Law zeroReadout := by
  intro law
  have equation := law (Scalar := ULift.{scalarLevel} ℤ) (-2) 2
  have contradiction : (0 : Module.End (ULift.{scalarLevel} ℤ)
      (Fock (ULift.{scalarLevel} ℤ))) = 1 := by
    simpa [zeroReadout, realize] using equation
  exact zero_ne_one contradiction

def evidence : Registration arena (arena.Law bActual) :=
  evidenceFor arena.Law bActual zeroReadout (fun first second => b_c first second)
    rejected bDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@b_c.{scalarLevel}) (type_of% bActual.{scalarLevel})
    Unit Unit where
  unitName := `D5.S3.VertexAlgebra.BcGhostStressCurrent.b_c.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostStressCurrent.BC.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ parameters index => letI := parameters.2; b index)
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostStressCurrent
    definition := none
    coordinates := #[0, 1]
    readouts := #[
      { path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"],
        stateBinder := 2, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "body", "body", "fn", "arg", "arg", "arg"],
        stateBinder := 2, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `linter.mathlibStandardSet, value := .bool true }]

#print axioms evidence
#print axioms registration
end BC

namespace LB

abbrev arena : Arena where
  signature := signature.{scalarLevel}
  Law family := ∀ {Scalar : Type scalarLevel} [CommRing Scalar] (first second : ℤ),
    L first * family.readout () ⟨Scalar, inferInstance⟩ second -
      family.readout () ⟨Scalar, inferInstance⟩ second * L first =
        (first - second : Scalar) • family.readout () ⟨Scalar, inferInstance⟩ (first + second)

theorem rejected : ¬ arena.{scalarLevel}.Law oneReadout := by
  intro law
  have equation := law (Scalar := ULift.{scalarLevel} ℤ) 1 0
  have contradiction : (0 : Module.End (ULift.{scalarLevel} ℤ)
      (Fock (ULift.{scalarLevel} ℤ))) = 1 := by
    simpa [oneReadout, realize] using equation
  exact zero_ne_one contradiction

def evidence : Registration arena (arena.Law bActual) :=
  evidenceFor arena.Law bActual oneReadout
    (fun first second => L_b_commutator first second) rejected bDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@L_b_commutator.{scalarLevel})
    (type_of% bActual.{scalarLevel}) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.BcGhostStressCurrent.L_b_commutator.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostStressCurrent.LB.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ parameters index => letI := parameters.2; b index)
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostStressCurrent
    definition := none
    coordinates := #[0, 1]
    readouts := #[
      { path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"],
        stateBinder := 3, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"],
        stateBinder := 3, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "body", "body", "arg", "arg"],
        stateBinder := 3, functionOperand := false,
        stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `linter.mathlibStandardSet, value := .bool true }]

#print axioms evidence
#print axioms registration
end LB

namespace LC

abbrev arena : Arena where
  signature := signature.{scalarLevel}
  Law family := ∀ {Scalar : Type scalarLevel} [CommRing Scalar] (first second : ℤ),
    L first * family.readout () ⟨Scalar, inferInstance⟩ second -
      family.readout () ⟨Scalar, inferInstance⟩ second * L first =
        (-2 * first - second : Scalar) •
          family.readout () ⟨Scalar, inferInstance⟩ (first + second)

theorem rejected : ¬ arena.{scalarLevel}.Law oneReadout := by
  intro law
  have equation := law (Scalar := ULift.{scalarLevel} ℤ) 0 (-1)
  have contradiction : (0 : Module.End (ULift.{scalarLevel} ℤ)
      (Fock (ULift.{scalarLevel} ℤ))) = 1 := by
    simpa [oneReadout, realize] using equation
  exact zero_ne_one contradiction

def evidence : Registration arena (arena.Law cActual) :=
  evidenceFor arena.Law cActual oneReadout
    (fun first second => L_c_commutator first second) rejected cDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@L_c_commutator.{scalarLevel})
    (type_of% cActual.{scalarLevel}) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.BcGhostStressCurrent.L_c_commutator.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostStressCurrent.LC.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ parameters index => letI := parameters.2; c index)
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostStressCurrent
    definition := none
    coordinates := #[0, 1]
    readouts := #[
      { path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"],
        stateBinder := 3, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"],
        stateBinder := 3, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body", "body", "body", "body", "arg", "arg"],
        stateBinder := 3, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `linter.mathlibStandardSet, value := .bool true }]

#print axioms evidence
#print axioms registration
end LC

end
end Reg.D5.S3.VertexAlgebra.BcGhostStressCurrent
