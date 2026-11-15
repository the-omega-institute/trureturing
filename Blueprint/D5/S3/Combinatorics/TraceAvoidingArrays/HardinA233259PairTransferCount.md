# Transfer count

## Abstract

The local transfer counting bridge.

**Theorem 1.1 (Transfer count).**

$$\forall n \in \operatorname{Nat},\; (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{L}\left((n) + (2)\right): \operatorname{Int}) = \operatorname{dotProduct}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{weights}, \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{TraceAvoidingArrays}.\operatorname{HardinA233259PairTransferCore}.\operatorname{Q}^{n}, (![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]: \operatorname{Fin}\left(14\right) \to \operatorname{Int})\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCount.count_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A233259: complementary-pair exclusion on a four-row strip*. URL: <https://oeis.org/A233259>.

*Commentary.*

The proper-pattern count equals the weighted transfer scalar.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCount.count_transfer`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer](HardinA233177PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore](HardinA233259PairTransferCore.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferInitial](HardinA233259PairTransferInitial.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferRep](HardinA233259PairTransferRep.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](TransferMatrix.md)
