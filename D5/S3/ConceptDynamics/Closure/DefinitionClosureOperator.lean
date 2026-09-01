/- GID: D5/S3/ConceptDynamics/Closure/DefinitionClosureOperator
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Closure/DefinitionClosureOperator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The repository semantic definition closure is bundled as Mathlib's canonical closure operator. -/

import Mathlib.Order.Closure
import D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois

/- Library-search audit trail (2026-09-01):
   * `DefinitionKernelGalois` already proves monotonicity, extensivity, and
     literal idempotence of the same-codomain `DefinitionClosure`.
   * Pinned Mathlib's `ClosureOperator` is the canonical bundled carrier for
     exactly those three laws. Repository searches found no existing bundle for
     `DefinitionClosure`.
   * This file introduces no second closure operation. It exposes the existing
     operation through the upstream API and identifies its closed elements. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Closure.DefinitionClosureOperator

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois

/-- The existing semantic closure of output-valued readouts, bundled as a
Mathlib closure operator on the inclusion order of readout families. -/
def definitionClosureOperator {X Output : Type*} :
    ClosureOperator (Set (Concept X Output)) where
  toFun := DefinitionClosure
  monotone' := definitionClosure_mono
  le_closure' := definitionClosure_extensive
  idempotent' := definitionClosure_idempotent

@[simp]
theorem definitionClosureOperator_apply
    {X Output : Type*} (Gamma : Set (Concept X Output)) :
    definitionClosureOperator Gamma = DefinitionClosure Gamma := rfl

/-- A readout family is closed for the upstream closure operator exactly when
it already contains every readout invariant on its common observational
kernel. -/
theorem isClosed_definitionClosureOperator_iff
    {X Output : Type*} (Gamma : Set (Concept X Output)) :
    (definitionClosureOperator (X := X) (Output := Output)).IsClosed Gamma <->
      DefinitionClosure Gamma = Gamma := by
  exact (definitionClosureOperator (X := X) (Output := Output)).isClosed_iff

/-- The upstream closed-element carrier is definitionally the repository's
semantically closed readout families. -/
def ClosedDefinitionFamily (X Output : Type*) :=
  (definitionClosureOperator (X := X) (Output := Output)).Closeds

/-- Taking semantic closure produces a canonical closed family through the
upstream `toCloseds` construction. -/
def closeDefinitionFamily {X Output : Type*}
    (Gamma : Set (Concept X Output)) :
    ClosedDefinitionFamily X Output :=
  (definitionClosureOperator (X := X) (Output := Output)).toCloseds Gamma

@[simp]
theorem closeDefinitionFamily_value
    {X Output : Type*} (Gamma : Set (Concept X Output)) :
    (closeDefinitionFamily Gamma : Set (Concept X Output)) =
      DefinitionClosure Gamma := rfl

#print axioms isClosed_definitionClosureOperator_iff

end D5.S3.ConceptDynamics.Closure.DefinitionClosureOperator
