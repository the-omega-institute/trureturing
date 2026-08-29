# Positive-Support Non-Explosion

## Abstract

Both-supported evidence supplies a countermodel to positive-support explosion.

**Theorem 1.1 (Both-supported premises do not entail an unsupported conclusion).**

$$\operatorname{let} proposition: \operatorname{Fin}\left(3\right) = 0, \operatorname{let} negatedProposition: \operatorname{Fin}\left(3\right) = 1, \operatorname{let} conclusion: \operatorname{Fin}\left(3\right) = 2, \operatorname{let} positivelyEntails: Prop = \forall candidateValuation \in \operatorname{Fin}\left(3\right) \to \operatorname{EvidenceValue}\left(\right),\; candidateValuation\left(negatedProposition\right) = \operatorname{swap}\left(candidateValuation\left(proposition\right)\right) \Rightarrow \left(\left(\operatorname{fst}\left(candidateValuation\left(proposition\right)\right) = true \land \operatorname{fst}\left(candidateValuation\left(negatedProposition\right)\right) = true\right) \Rightarrow \operatorname{fst}\left(candidateValuation\left(conclusion\right)\right) = true\right), \exists valuation \in \operatorname{Fin}\left(3\right) \to \operatorname{EvidenceValue}\left(\right),\; valuation\left(proposition\right) = \operatorname{bothSupported}\left(\right) \land \left(valuation\left(negatedProposition\right) = \operatorname{swap}\left(valuation\left(proposition\right)\right) \land \left(\operatorname{fst}\left(valuation\left(proposition\right)\right) = true \land \left(\operatorname{fst}\left(valuation\left(negatedProposition\right)\right) = true \land \left(valuation\left(conclusion\right) = (false, false) \land \left(\operatorname{fst}\left(valuation\left(conclusion\right)\right) = false \land \left(\left(\neg \operatorname{EvidenceConsistent}\left(valuation\left(proposition\right)\right)\right) \land \left(\neg positivelyEntails\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Evidence/PositiveSupportNonexplosion.positive_support_nonexplosion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the repository's two-bit evidence carrier. The proposition receives the canonical both-supported value, while the value of its negation is obtained by swapping the two support coordinates.

Both premises therefore have positive support. A third formula receives neither positive nor negative support, so this valuation refutes positive-support entailment of that conclusion.

The same witness has inconsistent premise evidence while the consequence relation remains non-explosive: an unsupported conclusion is not made supported merely by the conflict.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Evidence/PositiveSupportNonexplosion.positive_support_nonexplosion`
- Dependency: [D5/S3/ConceptDynamics/Evidence/ConflictingEvidenceAggregation](ConflictingEvidenceAggregation.md)
