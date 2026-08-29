/- GID: D5/S3/Observer/Agency/Holonomy/MemoryTransport
   generality: G
   mirror-B: D5/B/S3/Observer/Agency/Holonomy/MemoryTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Sequential memory transport along concatenated action words composes. -/

import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-29):
   * The statement is formulated over arbitrary types and functions.
   * Pinned Mathlib supplies only the elementary logical and function facts
     used below.
   * No finiteness, decidable equality, topology, probability, or algebraic
     structure is assumed unless it occurs explicitly in the theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Agency.Holonomy.MemoryTransport

universe u

/-- Execute a finite word of memory updates from left to right. -/
def transportWord {Memory : Type u} :
    List (Memory -> Memory) -> Memory -> Memory
  | [], memory => memory
  | step :: rest, memory => transportWord rest (step memory)

/-- Transport along a concatenated word equals sequential transport along its
two factors. -/
theorem transportWord_append
    {Memory : Type u}
    (first second : List (Memory -> Memory)) (memory : Memory) :
    transportWord (first ++ second) memory =
      transportWord second (transportWord first memory) := by
  induction first generalizing memory with
  | nil =>
      rfl
  | cons step rest inductionHypothesis =>
      simpa [transportWord] using
        inductionHypothesis second (step memory)

/-- The empty action word has trivial memory holonomy. -/
@[simp] theorem transportWord_nil
    {Memory : Type u} (memory : Memory) :
    transportWord ([] : List (Memory -> Memory)) memory = memory :=
  rfl

#print axioms transportWord_append
#print axioms transportWord_nil

end D5.S3.Observer.Agency.Holonomy.MemoryTransport
