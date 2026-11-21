# Parallel classes of affine lines

## Abstract

Parallel classes of affine lines.

**Theorem 1.1 (A pair of points determines one direction).**

$$x \neq y \Rightarrow \exists! u, \operatorname{line}\left(u, x\right) = \operatorname{line}\left(u, y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineBasis.unique_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two distinct points in the space of k+1 coordinates over a field, normalize their difference at its first nonzero coordinate. This is the unique normalized direction u whose quotient line coordinates agree on the two points. Here line(u, x) records the nonpivot coordinates after subtracting the pivot coordinate of x times u. The corresponding parallel classes partition the unordered edges and supply the basis assembly.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineBasis.unique_line`
- Dependency: [D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineAssembly](AffineNineAssembly.md)
