# Prescribed directions in a hypercube matching

## Abstract

A perfect matching of a binary cube can realize any even direction counts of the correct total.

**Theorem 1.1 (Exactly which direction counts a perfect matching can realize).**

$$\forall n \in Nat,\; \forall d \in \operatorname{Directions}\left(n\right) \to Nat,\; \operatorname{Total}\left(n, d\right) \Rightarrow ((\exists f \in \operatorname{Equiv}\left(\operatorname{EvenProfiles}\left(n\right), \operatorname{OddProfiles}\left(n\right)\right),\; \exists r \in \operatorname{EvenProfiles}\left(n\right) \to \operatorname{Directions}\left(n\right),\; (\forall p \in \operatorname{EvenProfiles}\left(n\right),\; \operatorname{Value}\left(f, p\right) = \operatorname{Flip}\left(p, \operatorname{Value}\left(r, p\right)\right)) \land (\forall i \in \operatorname{Directions}\left(n\right),\; \operatorname{Count}\left(r, i\right) = \operatorname{Value}\left(d, i\right))) \Leftrightarrow (\forall i \in \operatorname{Directions}\left(n\right),\; \operatorname{Even}\left(\operatorname{Value}\left(d, i\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Hypercube/DirectionMatching.exact_matching_directions` (`✓ std3`). ∎

*Citation.* Alexander Felzenbaum; Ron Holzman; Daniel J. Kleitman (1993). *Packing lines in a hypercube*. DOI: [10.1016/0012-365X(93)90327-P](https://doi.org/10.1016/0012-365X(93)90327-P).

*Commentary.*

For a natural number n the cube has n+2 coordinates. Directions(n) is Fin(n+2). EvenProfiles(n) and OddProfiles(n) consist of the binary vectors whose coordinate sum modulo two is zero and one, respectively. Total(n,d) means that the sum of the natural direction counts d(i) is 2^(n+1). Flip(p,i) toggles coordinate i and leaves all other coordinates fixed. Value denotes function evaluation. Count(r,i) counts all even profiles p with r(p)=i. Equiv denotes a bijection. The formula requires every pair to be a coordinate flip and every prescribed count to be attained.

Deleting the first coordinate identifies each parity class with the same additive group of binary tails. A flip of the first coordinate requests zero displacement in the tail. Every other flip requests its unit vector. Even multiplicity of each direction makes the total displacement zero. Hall's theorem numbers the input tails so that adding the requests also numbers the output tails. Restoring the head by parity gives the matching.

For a matching, the input and output tail sums agree because both enumerate the same group. The displacement sum is therefore zero. Each noninitial coordinate of this sum is the corresponding direction count modulo two. The remaining count is even because the total is even.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/DirectionMatching.exact_matching_directions`
- Dependency: [D5/S3/FiniteGroups/Hall/PrescribedDifferences](../../../FiniteGroups/Hall/PrescribedDifferences.md)
