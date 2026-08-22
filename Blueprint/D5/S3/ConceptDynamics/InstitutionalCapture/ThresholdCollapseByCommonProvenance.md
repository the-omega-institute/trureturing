# Threshold Collapse by Common Provenance

## Abstract

Equal formal role counts can conceal radically different capture thresholds.

**Theorem 1.1 (Common provenance collapses the capture threshold).**

$$\forall n: Nat, 0 < n \Rightarrow\ \operatorname{card}\left(\operatorname{Fin}\left(n\right)\right) = n \land\ \operatorname{captureNumber}\left(commonProvenanceReadout_{n}, commonProvenanceReadout_{n}\right) = 1 \land\ \operatorname{captureNumber}\left(independentProvenanceReadout_{n}, independentProvenanceReadout_{n}\right) = n.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InstitutionalCapture/ThresholdCollapseByCommonProvenance.threshold_collapse_by_common_provenance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formal roles are the n elements of Fin n, and both constructions use states in Fin n x Bool. The common-provenance readout ignores the state label, so every named role exposes the same Boolean source.

The independent-provenance readout exposes the Boolean value only when the state's label matches the named source, returning false for all other labels. Consequently, each role has a distinct necessary source.

For every positive n, the two systems therefore have the same formal role cardinality n while their exact capture numbers are one and n. Formal role multiplicity alone does not determine the capture threshold.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InstitutionalCapture/ThresholdCollapseByCommonProvenance.threshold_collapse_by_common_provenance`
- Dependency: [D5/S3/ConceptDynamics/InstitutionalCapture/IndependentSourceCaptureLowerBound](IndependentSourceCaptureLowerBound.md)
