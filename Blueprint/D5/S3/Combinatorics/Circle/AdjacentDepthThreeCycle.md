# Native adjacent-depth long-seed three-cycle

## Abstract

Native long seeds carry a physical order-three cycle.

**Theorem 1.1 (Native adjacent-depth long-seed three-cycle).**

Lean statement: `D5/S3/Combinatorics/Circle/AdjacentDepthThreeCycle.native_long_seed_three_cycle`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/AdjacentDepthThreeCycle.native_long_seed_three_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a native centered doubling source with k at least three and strictly positive SMALL labels, native_chain_extraction supplies each first-hit chain. When the selected first-hit length is h+1 with h at least one, the physical root, following negative, and next seed are distinct occurrences. Rotating their literal order from [root, negative, seed] to [seed, root, negative] is an actual order-three permutation with an explicit inverse.

The theorem records the native root, negative, and next-label formulas and the two unsigned-potential seam identities. It does not claim the later global mixed root-only loose-run sweep, either cyclic filter order, or the full C3.1 half-strip conjecture; those remain separate obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/AdjacentDepthThreeCycle.native_long_seed_three_cycle`
- Dependency: [D5/S3/Combinatorics/Circle/NativeSeedChains](NativeSeedChains.md)
