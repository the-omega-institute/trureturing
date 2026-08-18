/- GID: D5/S3/ObserverMemory/Runtime/FiniteRuntimeStateCardinality
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Runtime/FiniteRuntimeStateCardinality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite runtime state components have multiplicative joint cardinality. -/

import Mathlib.Data.Fintype.Prod

/- Library-search audit trail (2026-08-18):
   * Exact pinned-Mathlib and Loogle hit: `Fintype.card_prod` computes the cardinality of a
     binary product; it is applied repeatedly below, with `Nat.mul_assoc` for normalization.
   * Two local `smart_search.sh` queries found the exact binary lemma but no declaration for the
     five-component runtime state. Repository search found uses of the binary lemma, but no
     equivalent five-component statement. LeanSearch's `/api/search` returned HTTP 404, so it
     supplied no search conclusion.
   * Scope: this closes only the finite-state cardinality clause of qdo-v1 theorem/21.1; it does
     not formalize the source's separate runtime-modeling assumptions or parameter-space bound.
-/

namespace D5.S3.ObserverMemory.Runtime.FiniteRuntimeStateCardinality

/-- Five finite runtime components form a finite joint state space whose number of states is the
product of the component cardinalities. -/
theorem finite_runtime_state_cardinality
    {C K R M S : Type*}
    [Fintype C] [Fintype K] [Fintype R] [Fintype M] [Fintype S] :
    Fintype.card (C × K × R × M × S) =
      Fintype.card C * Fintype.card K * Fintype.card R * Fintype.card M * Fintype.card S := by
  simp only [Fintype.card_prod, Nat.mul_assoc]

#print axioms finite_runtime_state_cardinality

end D5.S3.ObserverMemory.Runtime.FiniteRuntimeStateCardinality
