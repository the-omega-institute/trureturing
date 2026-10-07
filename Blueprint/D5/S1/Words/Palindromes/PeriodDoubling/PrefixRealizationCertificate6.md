# Marker Reconstruction Certificate

## Abstract

Literal marker successors are completely represented in this finite row interval.

**Theorem 1.1 (Rows 3072 through 3583).**

$$\forall i \in \mathbb{N},\; \left(3072 \le i \land i < 3584\right) \Rightarrow \operatorname{prefixRealizationRowCheck}\left(i\right) = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/PrefixRealizationCertificate6.prefix_realization_rows_6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Kernel reduction checks every literal marker successor against the indexed edge list and every target index against the 4262-state bound. The interval includes its lower endpoint and excludes its upper endpoint.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/PrefixRealizationCertificate6.prefix_realization_rows_6`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixCertificates](MarkedPrefixCertificates.md)
