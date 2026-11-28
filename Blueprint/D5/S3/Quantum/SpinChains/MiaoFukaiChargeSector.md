# An odd-deficit sector of the periodic ladder

## Abstract

A recoverable binary tile code gives a jammed family at a common charge.

Assume L ≥ 12 throughout this construction. Let m be the floor of (L−8)/5. The tiles A and B comprise a minus rung followed by one and two empty rungs, respectively. Each of the m five-rung blocks independently reads AB or BA. At zero-based site 5i+2, those two choices read minus and empty, respectively. Reading that coordinate recovers the bit in each block, so the construction is injective on labelled words.

The residual length r=L−5m−6 lies between two and six. Its tail, in increasing order of r, is A, B, AA, AB, or BB. The respective numbers of one-empty gaps are 1, 0, 2, 1, and 0. If m plus that tail count is even, the six-rung pad is AAA, which adds three one-empty gaps. Otherwise the pad is BB, which adds none.

Every tile starts occupied and ends empty, so blockade holds at the periodic seam and each join. The only zero projector values occur at the one-empty gaps. Their neighbours have projector value one. Thus the sum of projector values is the length minus the number of one-empty gaps and every word is jammed.

**Theorem 1.1 (The sector embedding recovers the tile word).**

$$\forall (L: \mathbb{N}), \forall (h: 12 \le L), \forall (b: \operatorname{Fin}\left(\operatorname{blocks}\left(L\right)\right)\to\operatorname{Bool}), \operatorname{val}\left(\operatorname{jamEmbedding}\left(h, b\right)\right) = \operatorname{tiledConfig}\left(h, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/MiaoFukaiChargeSector.jamEmbedding_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two maps use the same labelled configurations, including across the seam.

**Theorem 1.2 (Parity of the common charge deficit).**

$$\forall (L: \mathbb{N}), 12 \le L \Rightarrow \operatorname{Odd}\left(L-\operatorname{targetCharge}\left(L\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/MiaoFukaiChargeSector.target_deficit_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The parity-dependent pad makes the deficit odd for every length at least twelve.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/MiaoFukaiChargeSector.jamEmbedding_val`
- Truth anchor: `D5/S3/Quantum/SpinChains/MiaoFukaiChargeSector.target_deficit_odd`
- Dependency: [D5/S3/Quantum/SpinChains/MiaoFukaiGuardedMoves](MiaoFukaiGuardedMoves.md)
