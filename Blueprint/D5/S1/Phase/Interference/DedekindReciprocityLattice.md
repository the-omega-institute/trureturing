# The Weighted Lattice Exchange

## Abstract

A finite coprime lattice double count evaluates the symmetric weighted floor sum.

Rows below the strict diagonal are finite intervals determined by Euclidean division. Coprimality excludes diagonal points, so the two strict triangles partition the complete residue rectangle.

**Theorem 1.1 (The symmetric weighted floor exchange).**

$$\forall d, c\in \mathbb{N},\ c>0 \land d>0 \land \gcd(c, d)=1 \Rightarrow d\operatorname{weightedFloorSum}(d, c) + c\operatorname{weightedFloorSum}(c, d) = \operatorname{latticeDifference}(d, c) + \frac{c(c-1)d(d-1)}{2}.$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/DedekindReciprocityLattice.weightedFloorSum_exchange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same module proves the unweighted Gauss floor count, evaluates the positive lattice difference row by row, and separates the two coordinate weights before this symmetric assembly.

## References

- Truth anchor: `D5/S1/Phase/Interference/DedekindReciprocityLattice.weightedFloorSum_exchange`
- Dependency: [D5/S1/Phase/Interference/DedekindReciprocityFiniteSums](DedekindReciprocityFiniteSums.md)
