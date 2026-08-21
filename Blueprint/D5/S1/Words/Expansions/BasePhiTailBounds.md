# Canonical Negative Base-Phi Tail Bounds

## Abstract

A nonempty canonical negative base-phi tail lies in the unit interval, with its first digit selecting the side of the inverse-golden cut.

**Theorem 1.1 (The first negative digit selects the inverse-golden interval).**

$$0<T_N<1,\ d_{-1}=1 \Rightarrow \varphi^{-1}\leq T_N,\ d_{-1}=0 \Rightarrow T_N<\varphi^{-1}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Expansions/BasePhiTailBounds.negative_tail_real_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reindexing the finite negative support turns it into a binary nonadjacent word. Its inverse-golden evaluation is positive and below one; a leading one gives the closed upper side of the inverse-golden cut, while a leading zero gives the open lower side.

## References

- Truth anchor: `D5/S1/Words/Expansions/BasePhiTailBounds.negative_tail_real_bounds`
- Dependency: [D5/S1/Words/Expansions/BasePhiCanonicalExpansion](BasePhiCanonicalExpansion.md)
