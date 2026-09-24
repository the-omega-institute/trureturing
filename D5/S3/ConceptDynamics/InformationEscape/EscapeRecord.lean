/- GID: D5/S3/ConceptDynamics/InformationEscape/EscapeRecord
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/EscapeRecord
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Escape records close a statement onto an arena law and certify where escape continues. -/

import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.EscapeRecord

universe u v w

/-- A statement closes onto an arena law in one direction: the statement implies the law of the
declared realization. What the closure leaves unresolved is recorded by a separate residual
witness; nothing here claims equivalence. -/
structure EscapePrimitiveRealization (arena : PrimitiveLawArena.{u, v, w}) (statement : Prop)
    (realization : PrimitiveRealization arena.signature) where
  forward : statement → arena.Law realization

/-- A legacy equivalence bridge is in particular a forward escape bridge. -/
theorem EscapePrimitiveRealization.ofLegacy {arena : PrimitiveLawArena.{u, v, w}} {statement : Prop}
    {realization : PrimitiveRealization arena.signature}
    (bridge : LegacyPrimitiveRealization arena statement realization) :
    EscapePrimitiveRealization arena statement realization :=
  ⟨bridge.equivalence.mp⟩

/-- Where the closed arena's information continues to escape: a pair of states that the finest
listed kernel of the chain still fails to separate. -/
structure EscapeResidualWitness {arena : Arena.{u}} (chain : LayerChain arena) where
  left : arena.State
  right : arena.State
  unresolved : (left, right) ∈ chain.unresolvedPairs

/-- The closure leaves no residual: the finest listed kernel separates every pair. -/
def EscapeResidualEmpty {arena : Arena.{u}} (chain : LayerChain arena) : Prop :=
  chain.unresolvedCount = 0

theorem escapeResidualEmpty_iff {arena : Arena.{u}} (chain : LayerChain arena) :
    EscapeResidualEmpty chain ↔ chain.unresolvedPairs = ∅ := by
  simp [EscapeResidualEmpty, LayerChain.unresolvedCount, Finset.card_eq_zero]

theorem escapeResidualEmpty_no_witness {arena : Arena.{u}} (chain : LayerChain arena)
    (empty : EscapeResidualEmpty chain) : IsEmpty (EscapeResidualWitness chain) := by
  refine ⟨fun witness => ?_⟩
  have h := (escapeResidualEmpty_iff chain).mp empty
  have := witness.unresolved
  rw [h] at this
  simpa using this

#print axioms escapeResidualEmpty_iff
#print axioms escapeResidualEmpty_no_witness

end D5.S3.ConceptDynamics.InformationEscape.EscapeRecord
