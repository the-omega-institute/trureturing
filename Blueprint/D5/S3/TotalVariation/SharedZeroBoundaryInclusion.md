# A shared-rule defect requires a boundary event

## Abstract

Deterministic boundary inclusion for the shared longest complete zero-run rule.

**Theorem 1.1 (Exact defect-to-boundary inclusion).**

Lean statement: `D5/S3/TotalVariation/SharedZeroBoundaryInclusion.shared_rule_defect_boundary_inclusion`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/SharedZeroBoundaryInclusion.shared_rule_defect_boundary_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R be any natural number and w any binary word of length R plus one. The old window reads positions zero through R minus one; the new window reads positions one through R, indexed again from zero. In each window a candidate has two observed one endpoints, at least one intervening zero, and no intervening one. Select the longest candidate, breaking ties by the latest closing endpoint. Its direction is the parity of the zeros strictly after that closing one. An empty candidate set has direction zero.

If the XOR of the new direction, the old direction, and the complement of w at position R is true, at least one of the following occurs: the selected old candidate opens at zero; the selected new candidate closes at R minus one; or the new selector returns no candidate. This holds for every binary word, without a source law or any forbidden-word restriction, including R zero.

Outside these three events, the new winner has a closing endpoint before the entering position, so adding one to both endpoints gives an old candidate. Thus the old candidate set is nonempty. The old winner opens after the departing position, so subtracting one from its endpoints gives a new candidate. Maximality in both windows forces the two winners to have equal run lengths and the same physical closing endpoint. The latest-endpoint tie breaker is retained in this comparison. Their strict zero suffixes correspond under translation, except for the single entering bit. Their direction XOR is therefore exactly its complement, contradicting a defect.

If the old selector is empty and the new one is nonempty, the new winner must be entering. If the new selector is empty, the third event applies directly. The statement is deterministic; it does not estimate the probabilities of the boundary events or establish the stationary bound of 512 divided by R.

## References

- Truth anchor: `D5/S3/TotalVariation/SharedZeroBoundaryInclusion.shared_rule_defect_boundary_inclusion`
- Dependency: [D5/S3/TotalVariation/ParrySharedZeroRule](ParrySharedZeroRule.md)
