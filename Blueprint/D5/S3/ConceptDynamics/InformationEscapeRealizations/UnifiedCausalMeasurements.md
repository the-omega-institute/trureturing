# Unified Causal Measurements

## Abstract

Exact reflected values measure the section 43.1 unified causal construction.

**Example 1.1 (Unified state enumeration).**

$$
unifiedStateEnumeration: StateEnumeration\left(unifiedArena\right)
$$

*Source.* Repository-derived.

*Commentary.*

A private duplicate-free list composes the landed sixteen-state IC and thirty-two-state OI enumerations for measurement only.

**Example 1.2 (Branch-local escape measurements).**

$$
(icEscapePairs\left(ObsU\right).card = 80) \land (icEscapePairs\left(IntU\right).card = 20) \land (icEscapePairs\left(CfU\right).card = 0) \land (oiEscapePairs\left(ObsU\right).card = 56) \land (oiEscapePairs\left(IntU\right).card = 24) \land (oiEscapePairs\left(CfU\right).card = 0)
$$

*Source.* Repository-derived.

*Commentary.*

The literal cumulative readouts leave 80/20/0 ordered IC pairs and 56/24/0 ordered OI pairs indistinguishable.

**Example 1.3 (Cumulative causal measurements).**

$$
(emptyCumulativeCounts.full = 2256) \land (observationCumulativeCounts.full = 136) \land (interventionCumulativeCounts.full = 44) \land (counterfactualCumulativeCounts.full = 0) \land (unifiedOffDiagonalPairs.card = 2256) \land (E_{obs}.card = 136) \land (E_{int}.card = 44) \land (E_{cf}.card = 0) \land (L_{obs}.card = 2120) \land (L_{int}.card = 92) \land (L_{cf}.card = 44) \land (flatCumulativeCounts.unique\left(.observation\right) = 0) \land (flatCumulativeCounts.unique\left(.intervention\right) = 0) \land (flatCumulativeCounts.unique\left(.counterfactual\right) = 44)
$$

*Source.* Repository-derived.

*Commentary.*

The full counts are 2256/136/44/0, the layered captures are 2120/92/44, and the flat unique counts are 0/0/44. The two zero results are the section 43.1 causal fixed-catalog instance of CIRPT-IE-024, not the general law owned by AnalysisLaws.

## References

- Dependency: [D5/S3/ConceptDynamics/InformationEscapeCounting/Enumerations](../InformationEscapeCounting/Enumerations.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog](UnifiedCausalCatalog.md)
