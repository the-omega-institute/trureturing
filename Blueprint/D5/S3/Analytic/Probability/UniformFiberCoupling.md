# Displacements of uniform couplings on group fibers

## Abstract

Every law on a group homomorphism fiber arises as the displacement of a uniform coupling.

**Theorem 1.1 (Exact displacement laws for a uniform fiber coupling).**

$$P \iff C$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/UniformFiberCoupling.displacement_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be a finite group, let H be a group, and take a homomorphism from G to H and an element t of H. Write K for the fiber over the identity and T for the fiber over t.

For a real weight function on T, P says that its weights are nonnegative and sum to one. C says that a nonnegative matrix on K times T has the uniform marginals on both fibers and recovers the given weight at d by summing its entries over pairs with displacement x inverse times y equal to d.

To construct the coupling, give a pair the weight of its displacement divided by the size of K. With the first entry fixed, left translation permutes T. With the second entry fixed, varying the first entry gives a bijection from K to T. These two bijections give the marginals. The first bijection also gives one occurrence of each prescribed displacement in every row. In reverse, summing all displacement weights gives the total mass of the coupling.

## References

- Truth anchor: `D5/S3/Analytic/Probability/UniformFiberCoupling.displacement_iff`
