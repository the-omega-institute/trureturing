/- GID: D5/S3/ObserverMemory/ContextUpdates/SuffixMergeCriterion
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/ContextUpdates/SuffixMergeCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A context update merges exactly when suffix and next token agree. -/

import Mathlib.Data.Prod.Basic

/- Library-search audit trail (2026-08-16):
   * Repository searches found no declaration matching the context-update equality criterion.
     The related `forward_merge_persistence` theorem already covers equality after the merge.
   * Pinned Mathlib contains the exact product-constructor criterion `Prod.mk_inj`; it is imported
     and applied directly below.
-/

namespace D5.S3.ObserverMemory.ContextUpdates.SuffixMergeCriterion

/-- Update a finite context by retaining its suffix and appending the generated next token. -/
def contextUpdate {Token Suffix : Type*} (nextToken : Token -> Suffix -> Token)
    (context : Token × Suffix) : Suffix × Token :=
  (context.2, nextToken context.1 context.2)

/-- Two contexts have the same successor exactly when their retained suffixes and generated next
tokens agree. -/
theorem context_update_eq_iff
    {Token Suffix : Type*} (nextToken : Token -> Suffix -> Token)
    (a a' : Token) (s s' : Suffix) :
    contextUpdate nextToken (a, s) = contextUpdate nextToken (a', s') <->
      s = s' /\ nextToken a s = nextToken a' s' := by
  exact Prod.mk_inj

#print axioms context_update_eq_iff

end D5.S3.ObserverMemory.ContextUpdates.SuffixMergeCriterion
