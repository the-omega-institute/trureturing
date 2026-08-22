# Phase-Enriched Adjacent Core Edges

## Abstract

Strict core enumerations have unique adjacent successors, while phase enrichment isolates the remaining gap-phase obligation.

**Theorem 1.1 (Consecutive frontier values form adjacent core edges).**

$$\forall w,c,n,\ \operatorname{FrontierReturnWordFor}(w,c) \Rightarrow \operatorname{AdjacentCorePoint}(w,c.\operatorname{enumerate}(n),c.\operatorname{enumerate}(n+1))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Expansions/BasePhiNegativePrefixTridentEdge.frontier_consecutive_core_adjacent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every pair of consecutive values in a complete strict core enumeration is an adjacent core pair. The accompanying endpoint-uniqueness theorem forces every other locally adjacent candidate to equal the enumerated successor.

**Theorem 1.2 (Phase-enriched traces are equivalent to the exact gap phase).**

$$\forall w,c,\ \operatorname{FrontierReturnWordFor}(w,c) \Rightarrow (\operatorname{PhaseEnrichedCoreTrace}(w,c) \Leftrightarrow \operatorname{FrontierGapPhase}(c))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Expansions/BasePhiNegativePrefixTridentEdge.phase_enriched_core_trace_iff_gap_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A phase-enriched adjacent-core trace exists exactly when the certificate satisfies its phase-selected additive gap equation. This equivalence preserves the six-state label without manufacturing the missing enriched-edge existence witness.

## References

- Truth anchor: `D5/S1/Words/Expansions/BasePhiNegativePrefixTridentEdge.frontier_consecutive_core_adjacent`
- Truth anchor: `D5/S1/Words/Expansions/BasePhiNegativePrefixTridentEdge.phase_enriched_core_trace_iff_gap_phase`
