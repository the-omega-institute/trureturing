/- GID: D5/S3/ConceptDynamics/ObservationTopology/EscapeUnderObservation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationTopology/EscapeUnderObservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Injective observation preserves escapes; noninjective hides one on inhabited input. -/

import D5.S0.Diagonal.Lawvere.QualitativeEscape
import Mathlib.Tactic

/- Library-search audit trail (2026-08-25):
   * `QualitativeEscape.escaped_of_fixedPointFree` supplies the canonical
     fixed-point-free diagonal escape.
   * Pinned Mathlib supplies function extensionality, range membership, and
     injectivity.
   * Repository searches found no accepted characterization of observations
     that preserve every function-catalog escape. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ObservationTopology.EscapeUnderObservation

open D5.S0.Diagonal.EscapeCount
open D5.S0.Diagonal.Lawvere.QualitativeEscape

/-- A candidate escapes a catalog when it is absent from the catalog range. -/
def CatalogEscape {Index Input Output : Type*}
    (catalog : Index → Input → Output) (candidate : Input → Output) : Prop :=
  candidate ∉ Set.range catalog

/-- Postcompose every catalog row with an observation. -/
def observedCatalog {Index Input Output Observation : Type*}
    (observe : Output → Observation) (catalog : Index → Input → Output) :
    Index → Input → Observation :=
  fun index => observe ∘ catalog index

/-- Postcompose a candidate with an observation. -/
def observedCandidate {Input Output Observation : Type*}
    (observe : Output → Observation) (candidate : Input → Output) :
    Input → Observation :=
  observe ∘ candidate

/-- Injective observations preserve every catalog escape. -/
theorem injective_preserves_catalog_escape
    {Index Input Output Observation : Type*}
    (observe : Output → Observation) (injective : Function.Injective observe)
    (catalog : Index → Input → Output) (candidate : Input → Output)
    (escape : CatalogEscape catalog candidate) :
    CatalogEscape (observedCatalog observe catalog)
      (observedCandidate observe candidate) := by
  rintro ⟨index, observedEquality⟩
  apply escape
  refine ⟨index, ?_⟩
  funext input
  apply injective
  exact congrFun observedEquality input

/-- Every noninjective observation hides some genuine catalog escape on any
 inhabited input type. -/
theorem noninjective_hides_some_catalog_escape
    {Input Output Observation : Type*} [Nonempty Input]
    (observe : Output → Observation) (notInjective : ¬Function.Injective observe) :
    ∃ catalog : Unit → Input → Output, ∃ candidate : Input → Output,
      CatalogEscape catalog candidate ∧
        observedCandidate observe candidate ∈
          Set.range (observedCatalog observe catalog) := by
  classical
  rw [Function.Injective] at notInjective
  push Not at notInjective
  rcases notInjective with ⟨first, second, observedEqual, different⟩
  let catalog : Unit → Input → Output := fun _ _ => first
  let candidate : Input → Output := fun _ => second
  refine ⟨catalog, candidate, ?_, ?_⟩
  · intro captured
    rcases captured with ⟨index, equality⟩
    have atInput := congrFun equality (Classical.choice (inferInstance : Nonempty Input))
    exact different atInput
  · refine ⟨(), ?_⟩
    funext input
    exact observedEqual

/-- Injectivity is exactly preservation of all one-row catalog escapes. -/
theorem injective_iff_preserves_unit_catalog_escape
    {Input Output Observation : Type*} [Nonempty Input]
    (observe : Output → Observation) :
    Function.Injective observe ↔
      ∀ (catalog : Unit → Input → Output) (candidate : Input → Output),
        CatalogEscape catalog candidate →
          CatalogEscape (observedCatalog observe catalog)
            (observedCandidate observe candidate) := by
  constructor
  · intro injective catalog candidate escape
    exact injective_preserves_catalog_escape
      observe injective catalog candidate escape
  · intro preserves
    by_contra notInjective
    rcases noninjective_hides_some_catalog_escape
      (Input := Input) (Output := Output) (Observation := Observation)
      observe notInjective with
      ⟨catalog, candidate, escape, hidden⟩
    exact (preserves catalog candidate escape) hidden

/-- Postcomposition on function spaces is injective exactly when the observation
 is injective, provided the input type is inhabited. -/
theorem observedCandidate_injective_iff
    {Input Output Observation : Type*} [Nonempty Input]
    (observe : Output → Observation) :
    Function.Injective (fun candidate : Input → Output =>
      observedCandidate observe candidate) ↔
      Function.Injective observe := by
  constructor
  · intro postcomposeInjective first second observedEqual
    let firstConstant : Input → Output := fun _ => first
    let secondConstant : Input → Output := fun _ => second
    have functionsEqual : firstConstant = secondConstant := by
      apply postcomposeInjective
      funext input
      exact observedEqual
    exact congrFun functionsEqual (Classical.choice (inferInstance : Nonempty Input))
  · intro observeInjective first second observedEqual
    funext input
    apply observeInjective
    exact congrFun observedEqual input

/-- A fixed-point-free diagonal escape remains escaped after every injective
 observation of its output. -/
theorem observed_diagonal_escape_of_injective
    {Address Symbol Observation : Type*}
    (twist : Symbol → Symbol) (fixedPointFree : ∀ symbol, twist symbol ≠ symbol)
    (catalog : Address → Address → Symbol)
    (observe : Symbol → Observation) (injective : Function.Injective observe) :
    CatalogEscape (observedCatalog observe catalog)
      (observedCandidate observe (diagonal twist catalog)) := by
  exact injective_preserves_catalog_escape observe injective catalog
    (diagonal twist catalog)
    (escaped_of_fixedPointFree twist fixedPointFree catalog)

#print axioms injective_preserves_catalog_escape
#print axioms noninjective_hides_some_catalog_escape
#print axioms injective_iff_preserves_unit_catalog_escape

end D5.S3.ConceptDynamics.ObservationTopology.EscapeUnderObservation
