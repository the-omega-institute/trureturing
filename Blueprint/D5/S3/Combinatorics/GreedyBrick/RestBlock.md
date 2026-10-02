# Literal Capacity Steps and First-Zero Rest Blocks

## Abstract

Literal capacity steps realize the least-zero rest block.

**Theorem 1.1 (The relay reaches exactly the first zero bin).**

$$\forall s : RestState, \exists t : RestState, \operatorname{RestEventStep}\left(s, t, \operatorname{firstZeroBin}\left(\operatorname{capacity}\left(s\right)\right)\right) \land \operatorname{placeBricks}\left(\operatorname{endpoint}\left(s\right), \operatorname{reverse}\left(\operatorname{capacity}\left(s\right)\right), \operatorname{firstZeroBin}\left(\operatorname{capacity}\left(s\right)\right)\right) = \operatorname{reverse}\left(\operatorname{capacity}\left(t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GreedyBrick/RestBlock.literal_rest_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rest state consists of an endpoint N and a finite capacity list whose entries are at most N. Rest capacities are indexed from bottom to top. The single-brick capacity algorithm scans from top to bottom, so the realization reverses the list at both boundaries. Let k be the one-based first zero bin, or height plus one when no old bin is zero. Applying the actual step at widths N+1 through N+k produces a bounded target satisfying every RestEventStep clause.

The endpoint is N+k and the target height is max(height,k). Every bin below k was positive and decreases by exactly one; bin k resets to N+k; every higher bin is unchanged. When all old bins are positive exactly one new top bin is appended. Empty states and k=1 remain in the theorem's domain.

The initial bound forces the first placement onto the floor. At a subsequent relay the current recipient has capacity N+a. If a is positive, the next width N+1 is eligible there and leaves a-1 while transferring upward. All higher capacities are below that width. The first zero stops the ascent. Induction uses the transfer and step definitions, rather than assuming the rest-event recurrence.

This theorem closes the capacity-step to rest-block bridge. It does not identify capacity states with geometric placements, construct a chronological event history, prove reset balance or future same-bin successors, or prove the original OEIS A395531 self-composition identity.

## References

- Truth anchor: `D5/S3/Combinatorics/GreedyBrick/RestBlock.literal_rest_block`
- Dependency: [D5/S3/ArithSums/GreedyBrickCapacityTotality](../../ArithSums/GreedyBrickCapacityTotality.md)
- Dependency: [D5/S3/Combinatorics/GreedyBrick/SuccessorBand](SuccessorBand.md)
