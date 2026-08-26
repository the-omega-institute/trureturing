# Element Reduction and Coarse Invariants

## Abstract

Entrywise reduction separates two integral matrices at every prime while trace and characteristic polynomial merge the same reductions.

**Theorem 1.1 (Prime reduction can separate what coarse invariants merge).**

$$\begin{aligned}A = \operatorname{zeroMatrix}(2, Z), N = \operatorname{single}(2, 0, 1, 1, Z),\\A \ne N \land\\\forall p \in Primes,\\\operatorname{reduction}(p, A) \ne \operatorname{reduction}(p, N) \land\\\operatorname{trace}(\operatorname{reduction}(p, A)) = \operatorname{trace}(\operatorname{reduction}(p, N)) \land\\\operatorname{charpoly}(\operatorname{reduction}(p, A)) = \operatorname{charpoly}(\operatorname{reduction}(p, N)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ResidueCoding/ElementReductionCoarseInvariant.element_reduction_coarse_invariant_fork` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the two-by-two integral zero matrix A and the matrix N whose only nonzero entry is one in row zero and column one. These are distinct global integral objects.

For every prime p, entrywise reduction modulo p still distinguishes A from N because the distinguished entry remains one.

On those same reduced matrices, both traces are zero and both characteristic polynomials are X squared. The positive separation and the coarse collision therefore use one shared construction at every prime.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ResidueCoding/ElementReductionCoarseInvariant.element_reduction_coarse_invariant_fork`
- Dependency: [D5/S0/Observation/PowerTraceSimilarityCountermodel](../../../S0/Observation/PowerTraceSimilarityCountermodel.md)
