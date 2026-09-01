/- GID: D5/S3/ConceptDynamics/ObservationFormalConceptAdapter
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationFormalConceptAdapter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Readout kernels are singleton extent closures in Mathlib formal concept analysis. -/

import Mathlib.Order.Concept
import D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois

/- Library-search audit trail (2026-09-01):
   * Pinned Mathlib supplies polar Galois connections, `extentClosure`, and the
     complete lattice of formal concepts.
   * The repository supplies readout families and their common observational
     kernel. Searches found no incidence context connecting those objects to
     Mathlib formal concept analysis.
   * Attributes below are observed readout/value pairs. The resulting singleton
     extent closure is proved to be exactly the common-kernel equivalence class,
     giving a lossless upstream adapter rather than a parallel concept theory. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ObservationFormalConceptAdapter

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v

/-- Explicit terminology for the repository's function-valued concept
primitive when it is used as an observation map. -/
abbrev Readout (X : Type u) (Output : Type v) := Concept X Output

/-- An attribute records one readout from the family together with one possible
output value. -/
def ObservationAttribute {X : Type u} {Output : Type v}
    (Gamma : Set (Readout X Output)) :=
  Sigma fun _definition : Gamma => Output

/-- A state has the attribute `(q, value)` exactly when `q` reads that value on
the state. -/
def observationIncidence {X : Type u} {Output : Type v}
    (Gamma : Set (Readout X Output))
    (state : X) (attribute : ObservationAttribute Gamma) : Prop :=
  attribute.1.1 state = attribute.2

/-- Mathlib's formal-concept extent closure of a singleton state is exactly the
equivalence class left indistinguishable by the complete readout family. -/
theorem extentClosure_singleton_eq_jointKernel_class
    {X : Type u} {Output : Type v}
    (Gamma : Set (Readout X Output)) (state : X) :
    extentClosure (observationIncidence Gamma) ({state} : Set X) =
      {other |
        (state, other) ∈
          jointKernel (fun definition : Gamma => definition.1)} := by
  ext other
  change
    other ∈
        lowerPolar (observationIncidence Gamma)
          (upperPolar (observationIncidence Gamma) ({state} : Set X)) <->
      (state, other) ∈
        jointKernel (fun definition : Gamma => definition.1)
  constructor
  · intro closed definition
    change definition.1 state = definition.1 other
    let attribute : ObservationAttribute Gamma :=
      ⟨definition, definition.1 state⟩
    have attributeOfState :
        attribute ∈
          upperPolar (observationIncidence Gamma) ({state} : Set X) := by
      intro point pointMem
      have pointEq : point = state := Set.mem_singleton_iff.mp pointMem
      subst point
      rfl
    exact (closed attributeOfState).symm
  · intro sameReadouts attribute attributeOfState
    have atState : observationIncidence Gamma state attribute :=
      attributeOfState (by simp)
    have sameForAttribute :
        attribute.1.1 state = attribute.1.1 other := by
      exact Set.mem_iInter.1 sameReadouts attribute.1
    unfold observationIncidence at atState ⊢
    exact sameForAttribute.symm.trans atState

/-- The observational equivalence class of a state is therefore an extent in
the upstream formal-concept context. -/
theorem jointKernel_class_isExtent
    {X : Type u} {Output : Type v}
    (Gamma : Set (Readout X Output)) (state : X) :
    Order.IsExtent (observationIncidence Gamma)
      {other |
        (state, other) ∈
          jointKernel (fun definition : Gamma => definition.1)} := by
  rw [← extentClosure_singleton_eq_jointKernel_class Gamma state]
  apply Order.isExtent_iff.mpr
  exact (extentClosure (observationIncidence Gamma)).idempotent
    ({state} : Set X)

/-- Each state determines a canonical formal concept whose extent is its full
observational equivalence class. -/
noncomputable def stateObservationConcept
    {X : Type u} {Output : Type v}
    (Gamma : Set (Readout X Output)) (state : X) :
    _root_.Concept X (ObservationAttribute Gamma)
      (observationIncidence Gamma) :=
  _root_.Concept.ofIsExtent
    (observationIncidence Gamma)
    {other |
      (state, other) ∈
        jointKernel (fun definition : Gamma => definition.1)}
    (jointKernel_class_isExtent Gamma state)

@[simp]
theorem stateObservationConcept_extent
    {X : Type u} {Output : Type v}
    (Gamma : Set (Readout X Output)) (state : X) :
    (stateObservationConcept Gamma state).extent =
      {other |
        (state, other) ∈
          jointKernel (fun definition : Gamma => definition.1)} := rfl

#print axioms extentClosure_singleton_eq_jointKernel_class
#print axioms jointKernel_class_isExtent

end D5.S3.ConceptDynamics.ObservationFormalConceptAdapter
