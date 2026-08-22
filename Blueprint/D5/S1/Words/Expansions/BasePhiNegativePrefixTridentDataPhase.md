# Data-Derived Frontier Gap Phases

## Abstract

Exact core-gap data corrects the recursive-state projection and isolates the remaining global recurrence obligation.

**Theorem 1.1 (The corrected selector returns eleven for prefix 010).**

$$\operatorname{dataFrontierGapSelector}(c,0)=11$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Expansions/BasePhiNegativePrefixTridentDataPhase.dataFrontierGapSelector_prefix010_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The executable prefix certificate for 010 is the recursive state G0o with return values eleven and seven. The data-derived projection sends G0o to family F, whose first letter therefore selects the observed first core gap eleven.

**Theorem 1.2 (Data-labeled traces are equivalent to the corrected gap phase).**

$$\forall w,c,\ \operatorname{FrontierReturnWordFor}(w,c) \Rightarrow (\operatorname{DataPhaseEnrichedCoreTrace}(w,c) \Leftrightarrow \operatorname{DataFrontierGapPhase}(c))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Expansions/BasePhiNegativePrefixTridentDataPhase.data_phase_enriched_core_trace_iff_gap_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A corrected data-labeled adjacent-core trace exists exactly when the return-word certificate satisfies the data-derived selector at every index. The theorem supplies the reconstruction interface without claiming the still-open global trace existence result.

## References

- Truth anchor: `D5/S1/Words/Expansions/BasePhiNegativePrefixTridentDataPhase.dataFrontierGapSelector_prefix010_zero`
- Truth anchor: `D5/S1/Words/Expansions/BasePhiNegativePrefixTridentDataPhase.data_phase_enriched_core_trace_iff_gap_phase`
- Dependency: [D5/S1/Words/Expansions/BasePhiNegativePrefixTridentEdge](BasePhiNegativePrefixTridentEdge.md)
