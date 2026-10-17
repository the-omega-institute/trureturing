# The finite rank arithmetic behind the second-star coordinate estimate

## Abstract

The sharp rank-coordinate bound in the second barycentric subdivision

This document isolates the finite arithmetic in CFMP §69.3. The second barycentric vertex is indexed by a nonempty set J of ranks in Fin(4) containing rank 0. The rank weight of r is 1/(r+1), and rankAverage(J) is the arithmetic mean of those weights. The complete rank set gives the sharp value 25/48. A second statement records the corresponding parent-star linear estimate for four coordinates whose zeroth coordinate is maximal.

**Definition 1.1 (Weight attached to a barycentric rank).**

$$\forall r \in Fin\left(4\right),\; rankWeight\left(r\right) = inverse\left(natValue\left(r\right) + 1\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/SecondBarycentricCoordinateBound.rankWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NatVal(r) is the natural-number value of r. The inverse is taken in the real field, so the four weights are 1, 1/2, 1/3 and 1/4.

**Definition 1.2 (Average rank weight).**

$$\forall J \in Finsets\left(Fin\left(4\right)\right),\; rankAverage\left(J\right) = multiply\left(inverse\left(realCard\left(J\right)\right), sum\left(r, J, rankWeight\left(r\right)\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/SecondBarycentricCoordinateBound.rankAverage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum is over r in J and realCard(J) is the cardinality viewed in the real field. The Lean definition is total, while the theorem assumes rank 0 belongs to J and therefore J is nonempty.

**Theorem 1.3 (Every rank type has the 25/48 lower bound, and the full type is sharp).**

$$(\forall J \in Finsets\left(Fin\left(4\right)\right),\; (0 \in J) \implies (div\left(25, 48\right) \le rankAverage\left(J\right))) \land (rankAverage\left(univ\left(Finsets\left(Fin\left(4\right)\right)\right)\right) = div\left(25, 48\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/SecondBarycentricCoordinateBound.second_star_rank_coordinate_bound_and_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are exactly eight subsets J of Fin(4) containing rank 0. The proof splits on membership of ranks 1, 2 and 3, identifies each J, and checks its rational average. The full set {0,1,2,3} has average 1/4 times (1 + 1/2 + 1/3 + 1/4) = 25/48, so the bound is sharp.

This is the finite rank-coordinate core of CFMP §69.3. It does not by itself identify all geometric second-star vertices, perform face gluing, prove the §69.4 separation statement, or construct the §69.5 ambient open neighborhood.

**Theorem 1.4 (The corresponding parent-star linear estimate is sharp).**

$$(\forall beta \in Fin\left(4\right) \to R,\; (sum\left(beta\right) = 1) \implies ((\forall j \in Fin\left(4\right),\; beta\left(j\right) \le beta\left(0\right)) \implies (div\left(25, 48\right) \le beta\left(0\right) + multiply\left(div\left(1, 2\right), beta\left(1\right)\right) + multiply\left(div\left(1, 3\right), beta\left(2\right)\right) + multiply\left(div\left(1, 4\right), beta\left(3\right)\right)))) \land (div\left(25, 48\right) = div\left(1, 4\right) + multiply\left(div\left(1, 2\right), div\left(1, 4\right)\right) + multiply\left(div\left(1, 3\right), div\left(1, 4\right)\right) + multiply\left(div\left(1, 4\right), div\left(1, 4\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/SecondBarycentricCoordinateBound.parent_star_coordinate_bound_and_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For beta:Fin(4) to R with total sum one and beta(j) <= beta(0) for every j, the weighted coordinate expression beta(0) + beta(1)/2 + beta(2)/3 + beta(3)/4 is at least 25/48.

Writing u_j = beta(0)-beta(j) for j=1,2,3 gives the exact identity 25/48 + u_1/48 + 3u_2/48 + 13u_3/48. Equality occurs at beta(0)=beta(1)=beta(2)=beta(3)=1/4. This estimate is the coordinate inequality used after the literal second-star-to-parent-star reduction; the reduction itself is a separate theorem.

## References

- Truth anchor: `D5/S3/Geometry/Gluing/SecondBarycentricCoordinateBound.parent_star_coordinate_bound_and_sharp`
- Truth anchor: `D5/S3/Geometry/Gluing/SecondBarycentricCoordinateBound.rankAverage`
- Truth anchor: `D5/S3/Geometry/Gluing/SecondBarycentricCoordinateBound.rankWeight`
- Truth anchor: `D5/S3/Geometry/Gluing/SecondBarycentricCoordinateBound.second_star_rank_coordinate_bound_and_sharp`
