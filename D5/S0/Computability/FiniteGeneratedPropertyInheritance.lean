/- GID: D5/S0/Computability/FiniteGeneratedPropertyInheritance
   generality: G
   mirror-B: D5/B/S0/Computability/FiniteGeneratedPropertyInheritance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Three object laws inherited by generators and finitary rules hold on their closure. -/

import D5.S0.Computability.PropertyObject

/- Library-search audit trail (2026-09-04):
   * D5 searches covered finite generation, generation complexity, structural
     induction, property objects, definition history, canonical readout,
     residual ledgers, and inheritance in spaced, underscored, and CamelCase
     forms. `PropertyObject` is the exact owner of the seven-component carrier;
     `EventHistoryInduction` covers only unary event append, not arbitrary
     finite-arity construction rules.
   * The pzg-v170 digestion record and residual/digest indexes list this atom as
     residual-open with no coverage GID. The retired formalization-receipt tree
     is absent and was neither inspected nor recreated.
   * Generalized searches of pinned Mathlib for finitary term algebras and
     closure-property induction found no theorem with a finite generator set,
     a finite rule set, rule-dependent finite arities, and this typed carrier.
   * The exact fixed-code owner is `CodeFixedPoint.code_fixed_point`; it is not
     imported or repackaged here. This module formalizes only the missing
     finite-generation inheritance step, avoiding an aggregate second source.
   * Logs of every origin/lane/math branch above origin/dev contain no matching
     atom identifier or equivalent in-flight finite-generation result. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Computability.FiniteGeneratedPropertyInheritance

open D5.S0.Computability.PropertyObject

universe uObject

/-- A finite collection of generators and construction rules. Each rule has a
finite, rule-dependent arity. -/
structure FiniteGenerationSystem (Object : Type uObject) where
  generatorCount : Nat
  generator : Fin generatorCount -> Object
  ruleCount : Nat
  arity : Fin ruleCount -> Nat
  construct : (rule : Fin ruleCount) -> (Fin (arity rule) -> Object) -> Object

/-- The least class obtained by finitely many applications of the registered
finite-arity construction rules to the registered generators. -/
inductive Generated {Object : Type uObject} (system : FiniteGenerationSystem Object) :
    Object -> Prop where
  | generator (index : Fin system.generatorCount) : Generated system (system.generator index)
  | construct (rule : Fin system.ruleCount)
      (inputs : Fin (system.arity rule) -> Object)
      (generated : ∀ index, Generated system (inputs index)) :
      Generated system (system.construct rule inputs)

/-- The three laws attached to an internal property object: temporal,
unitary, and ledgered. They remain external predicates rather than fields, so
their inheritance is not true merely by construction. -/
def HasThreeProperties {Object : Type uObject}
    (temporal unitary ledgered : Object -> Prop) (object : Object) : Prop :=
  temporal object ∧ unitary object ∧ ledgered object

/-- If every generator has the temporal, unitary, and ledger properties and
every registered finite-arity rule preserves all three simultaneously, then
every finitely generated internal property object has all three. -/
theorem finite_generated_property_inheritance
    {History Encoding Reading Ledger SelfCode Update Certificate : Type*}
    (system : FiniteGenerationSystem
      (InternalProperty History Encoding Reading Ledger SelfCode Update Certificate))
    (temporal unitary ledgered :
      InternalProperty History Encoding Reading Ledger SelfCode Update Certificate -> Prop)
    (generatorLaws : ∀ index,
      HasThreeProperties temporal unitary ledgered (system.generator index))
    (ruleLaws : ∀ (rule : Fin system.ruleCount)
      (inputs : Fin (system.arity rule) ->
        InternalProperty History Encoding Reading Ledger SelfCode Update Certificate),
      (∀ index, HasThreeProperties temporal unitary ledgered (inputs index)) ->
        HasThreeProperties temporal unitary ledgered (system.construct rule inputs)) :
    ∀ object, Generated system object -> HasThreeProperties temporal unitary ledgered object := by
  intro object generated
  induction generated with
  | generator index => exact generatorLaws index
  | construct rule inputs _ inherited => exact ruleLaws rule inputs inherited

#print axioms finite_generated_property_inheritance

end D5.S0.Computability.FiniteGeneratedPropertyInheritance
