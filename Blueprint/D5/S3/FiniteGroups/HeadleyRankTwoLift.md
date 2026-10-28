# Headley rank-two R-star construction

## Abstract

The native circular-length paths lift to complete unbounded rank-two R-star records.

**Definition 1.1 (Every exponent at least three gives an actual R-star record).**

Lean statement: `D5/S3/FiniteGroups/HeadleyRankTwoLift.powerTwoRStar`

*Formalization.* `D5/S3/FiniteGroups/HeadleyRankTwoLift.powerTwoRStar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural a and proof ha of 3 <= a, powerTwoRStar(a,ha) constructs HeadleyExtension.RStar(ZMod(2) times ZMod(2^a)). Its only inputs are a and ha. The chosen consecutive triple, in coordinates (epsilon,u), is A=(0,m), B=(1,0), C=(1,m), with m=2^(a-1). It satisfies A+C=B. No R-star assertion for a=2 or for C2 alone is included.

The live input is HeadleyRankTwoPath.powerTwoPath(a,ha), including its two consumed small leaves and unbounded descending R/L branch. Delete its initial zero column and its diameter edge. Each remaining circular length d below m has two occurrences. The first occurrence preserves the two rows; the other swaps them. Prefix sums of these row marks give the two track potentials. The phase chart begins at B, traverses the row-one track forward, crosses the terminal cap and returns on the other track. Its last phase is A and its second phase is C.

Conjugating the phase rotation by the actual vertex equivalence and extending it across zero constructs a successor permutation fixing zero. The phase rotation and full vertex inventory give one cycle on the entire nonzero carrier. For each internal base edge the two opposite traversals have directed labels (e,delta) and (e,-delta). The circular-length calculation identifies delta as d or -d. The two occurrences supply both e=0 and e=1, hence all four labels for that length.

The connector B to C supplies (0,m); A to B supplies (1,m), because m=-m modulo 2m. The terminal cap supplies (1,0). These are computed separately from every internal edge. Surjectivity of the actual full-group difference function, including zero, then gives its bijectivity by finiteness. The record uses that same function as its difference permutation, so difference_spec holds at all vertices and every closing seam. Parity, the nonzero and pairwise-distinct triple fields, both successor equalities and the additive equality are constructed internally.

The result supplies the minimum-exponent-one rank-two bases in the noncyclic abelian 2-group induction. Other ranks and exponent types still require their own suppliers; the general nonsplit extension consumes only an R-cycle on its kernel and an even R-star quotient. This construction does not solve the original arbitrary-subset, original-coordinate, coefficient-one sequencing problem.

Attribution: P. Headley, R-sequenceability and R-star-sequenceability of abelian 2-groups, Discrete Mathematics 131 (1994), 345-350, DOI 10.1016/0012-365X(94)90396-4. The implementation follows the completed native path/two-row reconstruction and its supplied independent mathematical audit. No novelty or new independent-review claim is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/HeadleyRankTwoLift.powerTwoRStar`
- Dependency: [D5/S3/FiniteGroups/HeadleyExtension](HeadleyExtension.md)
- Dependency: [D5/S3/FiniteGroups/HeadleyRankTwoPath](HeadleyRankTwoPath.md)
