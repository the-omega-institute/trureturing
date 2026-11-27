# Integral top cycles split by circuits through a ground element

## Abstract

Signed restriction and oriented join give inverse maps for all augmented matroid top cycles.

**Theorem 1.1 (Signed restriction to circuit contractions).**

Lean statement: `D5/S3/Combinatorics/Matroids/CircuitCycleDecomposition.circuit_cycle_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/CircuitCycleDecomposition.circuit_cycle_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M be a matroid on a finite totally ordered carrier and let e belong to its ground set. The top-cycle module consists of integral chains supported on bases whose augmented boundary vanishes at every ridge. There is an integral linear equivalence from this module to the finite product of top-cycle modules of M contracted by each circuit through e.

For a circuit C through e, write A for C with e removed. At a contracted basis T the forward map reads the original coefficient at the union of T and A, multiplied by the insertion sign of e at A and the shuffle sign of A followed by T. The coefficient is zero away from contracted bases. The inverse sums the joins of the augmented circuit boundaries with their contracted cycles. At an ambient face, take the circuit vertices first and the outside vertices second, sorting their concatenation with its permutation sign.

At a ridge disjoint from the circuit, the boundary of the signed restriction equals the original boundary at its union with A, times the insertion sign of e at A, the shuffle sign of A followed by the ridge, and minus one to the size of A. Inserting e contributes zero because the extended face contains the circuit. At a ridge meeting the circuit, every extension lies outside the contracted base support. The augmented join boundary rule gives the converse cycle construction.

Each basis omitting e determines its summand by the unique fundamental circuit in the basis with e adjoined. On these bases the two signed maps cancel their signs in pairs. At a basis containing e, its coefficient is recovered from the boundary on the ridge obtained by deleting e. A rank-zero contraction retains the empty-face coefficient. When e is a coloop the product is empty and the original cycle module is zero. A loop gives a single singleton circuit.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/CircuitCycleDecomposition.circuit_cycle_decomposition`
- Dependency: [D5/S3/Combinatorics/Matroids/OrderedCycleFactorization](OrderedCycleFactorization.md)
