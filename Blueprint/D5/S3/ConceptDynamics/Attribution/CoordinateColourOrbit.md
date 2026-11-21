# Fourfold counts for coordinate colour orbits

## Abstract

A pair of distinct Boolean profiles with nontrivial colour shifts has four equally weighted colour pairs.

**Theorem 1.1 (Exactly when every invariant count is divisible by four).**

$$\begin{aligned}\forall m \in M, 4 \mid \sum_{c,d} m\left((p,c), (q,d)\right)\\\iff p \neq q \land (\exists i \in I, p\left(i\right) = 0) \land (\exists j \in I, q\left(j\right) = 0)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/CoordinateColourOrbit.universally_four_dvd_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I be finite and take two Boolean profiles p and q on I. The group of binary vectors acts on an output by keeping its profile and adding to its binary colour the sum of the acting coordinates where that profile is false. The set M consists of natural-number matrices on pairs of coloured outputs invariant under the diagonal action. The sum runs over both binary colours of each profile.

A coordinate where the profiles differ controls one colour. Choose a false coordinate of the other profile to set its shift, and correct any effect on the first colour using the first coordinate. Surjectivity forces equal matrix entries at all four colour pairs.

If one profile is everywhere true, its colour does not move. The two pairs with that colour zero give an invariant count of two. If the profiles coincide, the two pairs with equal colours give the same count. In each case the matrix is zero away from the given profile pair.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/CoordinateColourOrbit.universally_four_dvd_iff`
- Dependency: [D5/S3/ConceptDynamics/Attribution/CoordinateFlagCoupling](CoordinateFlagCoupling.md)
