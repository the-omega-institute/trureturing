# When every calibrating seed action is free

## Abstract

Prime divisibility characterizes freeness in every law calibrating a complete grid.

**Theorem 1.1 (Prime divisibility is necessary and sufficient).**

$$\forall k m, 0 < m \Rightarrow (\operatorname{EveryCalibratingLawFree}\left(k, m\right) \iff \operatorname{PrimeDivisibility}\left(k, m\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/GridSeedFreeness.every_calibrating_law_free_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k and m be natural numbers with m positive. The input profiles are all natural vectors on k labels with total m. EveryCalibratingLawFree means every finite positive calibrating law on these profiles has trivial stabilizer at every seed. PrimeDivisibility means every prime at most k divides m.

If each prime at most k divides m, multiply the seed weights by m and apply the prime-cycle obstruction to the resulting unnormalized masses. A nontrivial seed stabilizer would contain an element of prime order.

If a prime p at most k fails to divide m, choose a single p-cycle on the labels. For a profile fixed by the cycle, the total count on the cycle is a multiple of p, so a positive coordinate exists outside its support. For other profiles the associated subgroup of prime order has trivial input stabilizer, so any positive coordinate is allowed. At every profile a positive output is fixed by the elements of the cyclic subgroup that fix that profile. The resulting calibrating law has a positive seed fixed by the chosen nonidentity cycle.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/GridSeedFreeness.every_calibrating_law_free_iff`
- Dependency: [D5/S3/ConceptDynamics/Attribution/FiniteKernelStabilizers](FiniteKernelStabilizers.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/PermutationGridSupport](PermutationGridSupport.md)
