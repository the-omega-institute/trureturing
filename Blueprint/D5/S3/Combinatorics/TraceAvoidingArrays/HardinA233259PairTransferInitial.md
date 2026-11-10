# Initial weights

## Abstract

Initial class weights.

**Theorem 1.1 (Initial weights).**

$$\forall s \in \operatorname{Fin}\left(14\right),\; \sum_{a \in \operatorname{Col}} (\sum_{b \in \operatorname{Col}} ((if (\operatorname{compatible}\left(a, b\right)) \land (\operatorname{cls}\left(b\right) = s) then 1 else 0))) = \operatorname{weights}\left(s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferInitial.initial_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

Initial class-weight certificate.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferInitial.initial_weights`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer](HardinA233177PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore](HardinA233259PairTransferCore.md)
