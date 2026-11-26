# All extended coordinates split into source and tail

## Abstract

All extended coordinates split into source and tail.

**Definition 1.1 (All extended coordinates split into source and tail).**

$$Extended \equiv \operatorname{DependentSourceTail}\left(Source, Tail\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/NativeReader/Fibers.fullCarrierEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

DependentSourceTail denotes the dependent sum over every original source q of the complete legal tail with left boundary b9(q). originalPart keeps b0..b9 and restores the old fixed b10=0. auxiliaryPart keeps the actual b9..b14 and its fixed right boundary b15=1. joinPath reinserts the actual five auxiliary positions. Its seam legality is proved using the shared b9 and the original and auxiliary boundary conditions.

The definition fullCarrierEquiv is an actual equivalence between the complete extended legal-path set and this dependent sum. join_split and original_join prove both reconstruction directions; the dependent tail equality retains all coordinates. This is the full direct-sum decomposition, not a restriction to the ready interface or to a fixed tail matrix. The equivalence is consumed by finite summation in the exact global native projection action. It provides no source process, probability law or causal archive.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/NativeReader/Fibers.fullCarrierEquiv`
- Dependency: [D5/S3/Quantum/Dynamics/NativeReader/Carrier](Carrier.md)
