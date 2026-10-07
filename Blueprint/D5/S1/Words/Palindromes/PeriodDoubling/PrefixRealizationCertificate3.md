# Marker Reconstruction Certificate

## Abstract

Literal marker successors are completely represented in this finite row interval.

**Theorem 1.1 (Rows 1536 through 2047).**

$$\forall i \in \mathbb{N},\; \left(1536 \le i \land i < 2048\right) \Rightarrow \operatorname{prefixRealizationRowCheck}\left(i\right) = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/PrefixRealizationCertificate3.prefix_realization_rows_3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Kernel reduction checks every literal marker successor against the indexed edge list and every target index against the 4262-state bound. The interval includes its lower endpoint and excludes its upper endpoint.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/PrefixRealizationCertificate3.prefix_realization_rows_3`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates](MarkedPrefixCertificates.md)
